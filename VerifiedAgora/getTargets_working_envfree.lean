import Cli.Extensions
import VerifiedAgora.tagger
import VerifiedAgora.Frontend
import VerifiedAgora.TacticInvocation
import VerifiedAgora.Utils
import VerifiedAgora.CollectAxiomsBatched
open Lean Core Elab IO Meta Term Command Tactic Cli Environment CollectAxiomsBatched

structure TimingStats where
  totalMs : Nat := 0
  count : Nat := 0
  maxMs : Nat := 0
  deriving Inhabited

structure TimingState where
  order : Array String := #[]
  stats : Std.HashMap String TimingStats := {}
  deriving Inhabited

def recordTiming (timingsRef : IO.Ref TimingState) (label : String) (elapsedMs : Nat) : IO Unit := do
  timingsRef.modify fun s =>
    let existing := s.stats.get? label
    let prev := existing.getD {}
    let next : TimingStats := {
      totalMs := prev.totalMs + elapsedMs
      count := prev.count + 1
      maxMs := max prev.maxMs elapsedMs
    }
    let order := if existing.isSome then s.order else s.order.push label
    { order := order, stats := s.stats.insert label next }

def withTiming (timingsRef : IO.Ref TimingState) (label : String) (action : IO α) : IO α := do
  let start ← IO.monoMsNow
  try
    let out ← action
    let stop ← IO.monoMsNow
    recordTiming timingsRef label (stop - start)
    return out
  catch e =>
    let stop ← IO.monoMsNow
    recordTiming timingsRef label (stop - start)
    throw e

def printTimingSummary (timingsRef : IO.Ref TimingState) : IO Unit := do
  let timings ← timingsRef.get
  IO.println "<TIMING_SUMMARY>"
  let mut totalMeasured : Nat := 0
  for label in timings.order do
    if let some stats := timings.stats.get? label then
      let avg := if stats.count == 0 then 0 else stats.totalMs / stats.count
      totalMeasured := totalMeasured + stats.totalMs
      IO.println s!"{label}: total={stats.totalMs}ms count={stats.count} avg={avg}ms max={stats.maxMs}ms"
  IO.println s!"TOTAL_MEASURED: {totalMeasured}ms"
  IO.println "</TIMING_SUMMARY>"


def printExpr (ex : Expr) (env : Environment) : IO Format := do
  let ctx:={fileName:="", fileMap:=default}
  Prod.fst <$> (CoreM.toIO (MetaM.run' do ppExpr ex) ctx {env:=env})

def collectAxiomsRaw (env : Environment) (n : Name) : Array Name :=
  let (_, s) := (CollectAxioms.collect n).run env |>.run {}
  s.axioms

def validateCollectedAxioms (n : Name) (axioms : Array Name) (allow_sorry? : Bool := false) : IO Unit := do
  let allowedAxioms := if allow_sorry? then TargetsAllowedAxioms else AllowedAxioms
  for a in axioms do
    if a ∉ allowedAxioms then
      throw <| diagnosticErrorMessage s!"Declaration relies on disallowed axiom." <| Json.mkObj [
        ("summary", Json.str s!"A declaration in the attempted contribution relies on a disallowed axiom. Remember, standard declarations must only rely on the allowed set of standard axioms ({String.intercalate ", " (AllowedAxioms.map Name.toString)}) for Agora contributions. Declarations tagged as targets are allowed to additionally rely on \"sorryAx\", but only if the previous proof of said target also relied on \"sorryAx\" - meaning that contributions cannot regress already resolved targets to once again be unresolved."),
        ("offending axiom", Json.str s!"Declaration {n} relies on axiom {a}, which is not in its allowed set of axioms ({String.intercalate ", " (allowedAxioms.map Name.toString)})")
      ]

def batchHumanDecls (names : Array Name) (env : Environment) : IO (Std.HashMap Name DeclarationRanges) := do
  let ctx := {fileName:="", fileMap:=default}
  let state : Core.State := {env := env}
  let fn : CoreM (Std.HashMap Name DeclarationRanges) := do
    let mut out : Std.HashMap Name DeclarationRanges := {}
    for name in names do
      let hasDeclRange := (← Lean.findDeclarationRanges? name)
      let notProjFn := !(← Lean.isProjectionFn name)
      match (hasDeclRange, notProjFn) with
      | (some rng, true) =>
        out := out.insert name rng
      | _ =>
        pure ()
    return out

  let result? ← CoreM.run' fn ctx state |>.toIO'
  match result?.toOption with
  | some x => pure x
  | none => pure {}


def getConstantsInModule (env : Environment) (mod : Name): IO (Std.HashMap Name ConstantInfo) := do
  let modIdx? : Option ModuleIdx := env.getModuleIdx? mod
  let mut ciMap : Std.HashMap Name ConstantInfo := {}
  for (n,ci) in env.constants  do
    let ownedByModule := match modIdx?, env.getModuleIdxFor? n with
      | some modIdx, some declIdx => modIdx == declIdx
      | _, _ => false
    if ownedByModule then
      ciMap := ciMap.insert n ci
  pure ciMap

def getDescriptorForModule (timingsRef : IO.Ref TimingState) (mod : Name) (targetDescriptor? : Option FileDescriptor := none) (sourceFile? : Option System.FilePath := none) : IO FileDescriptor := do

  let modStr := mod.toString

  let (env'', tagged_decl_names) ← withTiming timingsRef s!"descriptor.loadTaggedDecls[{modStr}]" <| do
    let env'' ← importModules #[{ module := mod }] {} 0
    let modIdx? : Option ModuleIdx := env''.getModuleIdx? mod
    let tagged_decls := env''.constants.fold (fun acc k ci =>
      let ownedByModule := match modIdx?, env''.getModuleIdxFor? k with
        | some modIdx, some declIdx => modIdx == declIdx
        | _, _ => false
      if ownedByModule && TagAttribute.hasTag targetAttribute env'' k then ci::acc else acc
    ) []
    let tagged_decl_names : Std.HashSet Name := tagged_decls.foldl (fun s ci => s.insert ci.name) {}
    pure (env'', tagged_decl_names)

  let constants_in_mod ← getConstantsInModule env'' mod

  let ciMap ← withTiming timingsRef s!"descriptor.buildModuleConstMap[{modStr}]" <| do
    let mut ciMap : Std.HashMap Name ConstantInfo := {}
    for (n,ci) in constants_in_mod  do
      ciMap := ciMap.insert n ci
    pure ciMap

  let (scanCandidates, namesForHumanScan) ← withTiming timingsRef s!"descriptor.scanDeclarations[{modStr}]" <| do
    let mut scanCandidates : Array (Name × ConstantInfo) := #[]
    let mut namesForHumanScan : Array Name := #[]
    for (n,ci) in constants_in_mod  do
      -- IO.println s!"Processing declaration {n} of kind {ci.kind}..."
      if ci.kind ∈ ["theorem", "def"] then
        if let .defnInfo dv := ci then
          if dv.safety != .safe then
            let str_safety := match dv.safety with
              | .safe => "safe"
              | .unsafe => "unsafe"
              | .partial => "partial"
            throw <| diagnosticErrorMessage s!"unsafe/partial declaration detected" <| Json.mkObj [
              ("summary", Json.str "The attempted contribution contains unsafe or partial declarations, which are not allowed. Please change the declaration to be safe/total or remove it from the submission/target."),
              ("offending declaration", Json.str s!"Declaration {n} ({ci.kind}) has safety \"{str_safety}\".")
              ]

        scanCandidates := scanCandidates.push (n, ci)
        namesForHumanScan := namesForHumanScan.push n
    for target in targetDescriptor?.getD [] do
      namesForHumanScan := namesForHumanScan.push target.ci.name

    let mut dedupNames : Array Name := #[]
    let mut seenNames : Std.HashSet Name := {}
    for n in namesForHumanScan do
      if n ∉ seenNames then
        seenNames := seenNames.insert n
        dedupNames := dedupNames.push n
    pure (scanCandidates, dedupNames)

  let humanDeclMap ← withTiming timingsRef s!"descriptor.batchHumanDeclScan[{modStr}]" <| do
    batchHumanDecls namesForHumanScan env''

  let mut ret : Array (DeclarationDescriptor × DeclarationRanges) ← withTiming timingsRef s!"descriptor.buildDescriptorSeed[{modStr}]" <| do
    let mut ret : Array (DeclarationDescriptor × DeclarationRanges) := #[]
    for (n, ci) in scanCandidates do
      if let some rng := humanDeclMap.get? n then
        ret := ret.push ({
          ci := ci,
          contents := default, -- we fill this in later since we need the file map for it
          context := default, -- we fill this in later since we need the file map for it
          target? := tagged_decl_names.contains n,
          sourceFile? := sourceFile?,
          axioms := default, -- we fill this in later when we do regression and axiom checking
          resolved? := default -- same
        }, rng)
    pure ret

  let mut axiomMap : Std.HashMap Name (Array Name) ← withTiming timingsRef s!"descriptor.precomputeAxioms[{modStr}]" <| do
    let names := ret.map (fun (desc, _) => desc.ci.name)
    return collectAxiomsBatched env'' names

  let exprPrinter (e : Expr) := printExpr e env''

  if (targetDescriptor?.getD []).length > 0 then
    axiomMap ← withTiming timingsRef s!"descriptor.compareAgainstTarget[{modStr}]" <| do
      let mut axiomMap := axiomMap
      for target in targetDescriptor?.getD [] do
        if (humanDeclMap.get? target.ci.name).isSome then
          if let some ci' := ciMap.get? target.ci.name then
            if target.ci.kind ≠ ci'.kind then
              throw <| diagnosticErrorMessage s!"Declaration kind mismatch between current and attempted contribution" <|
              Json.mkObj [
                ("summary", Json.str "The declaration kind in the attempted contribution does not match the corresponding declaration in the current version."),
                ("offending declaration", Json.str s!"Declaration {target.ci.name} has kind \"{ci'.kind}\" in the attempted contribution, but is expected to have kind \"{target.ci.kind}\".")
              ]
            if ci'.kind=="theorem" then
              if Not (equivThm target.ci ci') then
                throw <| diagnosticErrorMessage s!"Theorem statement mismatch between current and attempted contribution" <|
                Json.mkObj [
                  ("summary", Json.str "A theorem statement in the attempted contribution does not match the corresponding theorem statement in the current version. Please ensure that the statement (type, name, etc.) of the theorem is exactly the same as in the current version."),
                  ("offending declaration", Json.str s!"Theorem {target.ci.name} has type \"{← exprPrinter ci'.type}\" in the attempted contribution, but is expected to have type \"{← exprPrinter target.ci.type}\".")
                ]
            if ci'.kind=="def" then
              if Not (equivDefn target.ci ci' (`sorryAx ∉ target.axioms)) then
                let valStr ← if `sorryAx ∉ target.axioms then
                  pure s!" \n\nAdditionally, the definitions have the following values:\n\nThe attempted contribution has value: \"{← exprPrinter ci'.value!}\"\n\nThe contribution is expected to have value: \"{← exprPrinter target.ci.value!}\""
                else pure ""
                throw <| diagnosticErrorMessage s!"Definition statement mismatch between current and attempted contribution" <| Json.mkObj [
                  ("summary", Json.str "A definition statement in the attempted contribution does not match the corresponding definition statement in the current version. Please ensure that the statement (type, name, etc.) of the definition is exactly the same as in the current version. Additionally, unless the definition's value relies on the `sorry` axiom, the value of the definition must also be exactly the same."),
                  ("offending declaration", Json.str <| s!"Definition {target.ci.name} has type:\n\n \"{← exprPrinter ci'.type}\" \n\nin the attempted contribution, and is expected to have type \n\n \"{← exprPrinter target.ci.type}\"" ++ valStr)
                ]

            let allow_sorry? := target.ci.name ∈ tagged_decl_names && (`sorryAx ∈ target.axioms)
            -- we allow sorry axiom only on marked targets, where the target itself relies on sorry
            let (axioms, axiomMap') := match axiomMap.get? target.ci.name with
              | some axioms => (axioms, axiomMap)
              | none =>
                let axioms := collectAxiomsRaw env'' target.ci.name
                (axioms, axiomMap.insert target.ci.name axioms)
            axiomMap := axiomMap'
            validateCollectedAxioms target.ci.name axioms allow_sorry?
          else
            throw <| diagnosticErrorMessage s!"Missing declaration in attempted contribution." <| Json.mkObj [
              ("summary", Json.str s!"A declaration in the current file version was not found in the attempted contribution. Please ensure that all declarations in the current file version are still included in the your contribution (i.e. no deletions are allowed)."),
              ("offending declaration", Json.str s!"Declaration {target.ci.name} was found in the current file version, but no declaration with this name was found in the attempted contribution.")
            ]
      pure axiomMap


  -- if we got here, we haven't failed! So now fill in contents and context and axioms!
  let fileMap ← withTiming timingsRef s!"descriptor.loadSourceFile[{modStr}]" <| do
    let source ← IO.FS.readFile (← findLean mod)
    pure (FileMap.ofString source)
  let output ← withTiming timingsRef s!"descriptor.materializeOutput[{modStr}]" <| do
    ret.mapM (fun (desc, rng) => do
      let axioms := match axiomMap.get? desc.ci.name with
        | some a => a
        | none => collectAxiomsRaw env'' desc.ci.name
      validateCollectedAxioms desc.ci.name axioms desc.target?
      pure {desc with
        contents := Substring.mk fileMap.source (fileMap.ofPosition rng.range.pos) (fileMap.ofPosition rng.range.endPos),
        context := Substring.mk fileMap.source ⟨0⟩ (fileMap.ofPosition rng.range.pos),
        axioms := axioms,
        resolved? := axioms.all (fun a => a ∈ AllowedAxioms) -- we consider a declaration resolved if it relies only on allowed axioms, meaning it doesn't rely on sorry or any disallowed axioms
      })

  return output.toList

unsafe def getTargets' (timingsRef : IO.Ref TimingState)
    (submission_module : Name)
    (target_module : Option Name := none)
    (submission_source_file : Option System.FilePath := none)
    (target_source_file : Option System.FilePath := none) : IO FileDescriptor := do
  let effectiveTarget := target_module.getD submission_module
  let submissionSourceFile ← match submission_source_file with
    | some fp => pure fp
    | none => findLean submission_module

  let targetSourceFile ←
    if effectiveTarget == submission_module then
      pure submissionSourceFile
    else
      match target_source_file with
      | some fp => pure fp
      | none => findLean effectiveTarget

  if effectiveTarget == submission_module then
    getDescriptorForModule timingsRef submission_module (sourceFile? := some submissionSourceFile)
  else
    let targetDescriptor ← getDescriptorForModule timingsRef effectiveTarget (sourceFile? := some targetSourceFile)
    let submittedDescriptor ← getDescriptorForModule timingsRef submission_module targetDescriptor (sourceFile? := some targetSourceFile)
    return submittedDescriptor



unsafe def getTargetsCLI (args : Cli.Parsed) : IO UInt32 := do
  let timingsRef ← IO.mkRef ({} : TimingState)
  let runtimeSearchPath ← searchPathRef.get
  let appBuildLib := (← IO.appDir).parent.get! / "lib"
  let runtimeSearchPath :=
    if appBuildLib ∈ runtimeSearchPath then runtimeSearchPath else runtimeSearchPath ++ [appBuildLib]
  searchPathRef.set (runtimeSearchPath ++ compile_time_search_path%)
  enableInitializersExecution

  let submission := args.flag! "submission" |>.as! String
  let target := args.flag! "target" |>.as! String

  let target? := if target == "" then none else some target

  let savePath := args.flag! "save" |>.as! String
  let save? := if savePath == "" then none else some savePath

  try
    let targetContent? ← withTiming timingsRef "cli.resolveTargetInput" <| do
      target?.mapM (fun t => getFileOrModuleContents t)

    let (_, target_mod?, target_fp?) := match targetContent? with
      | some (c, m, fp) => (some c, some m, some fp)
      | none => (none, none, none)


    let (_, sub_mod, sub_fp) ← withTiming timingsRef "cli.resolveSubmissionInput" <| do
      getFileOrModuleContents submission
    let descriptor ← getTargets' timingsRef sub_mod target_mod? (submission_source_file := some sub_fp) (target_source_file := target_fp?)
    let json ← withTiming timingsRef "cli.encodeDescriptorJson" <| do
      pure (ToJson.toJson descriptor)
    if save?.isSome then
        let _ ← withTiming timingsRef "cli.writeDescriptorFile" <| do
          IO.FS.writeFile save?.get! (json.pretty)
        IO.println s!"Wrote file descriptor to {save?.get!}"
    else
      IO.println "<DESCRIPTOR>"
      IO.println json.pretty
      IO.println "</DESCRIPTOR>"

    printTimingSummary timingsRef
    IO.println "Finished with no errors."
    return 0
  catch e =>
    printTimingSummary timingsRef
    IO.eprintln s!"Error: {e}"
    return 1


unsafe def getTargets : Cmd := `[Cli|
  get_targets VIA getTargetsCLI; ["0.0.1"]
"Get targets from a string."

  FLAGS:
    submission : String; "In file mode, the submission module name."
    target : String; "The target module name. Optional; if not provided, then target=submission is assumed."
    save : String; "If provided, save the file descriptor to this file as json to specified path. Default is no save."

  EXTENSIONS:
    defaultValues! #[("target", ""), ("save", "")]
]


unsafe def main (args : List String) : IO UInt32 :=
  getTargets.validate args
