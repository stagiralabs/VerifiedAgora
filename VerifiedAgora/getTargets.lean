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

structure CollectedFailure where
  declName : String
  moduleName : String
  kind : String
  summary : String
  detail : String
  deriving Inhabited, BEq, ToJson

def appendFailures (failuresRef : IO.Ref (Array CollectedFailure)) (newFailures : Array CollectedFailure) : IO Unit := do
  failuresRef.modify (fun failures =>
    newFailures.foldl (fun acc f => if acc.contains f then acc else acc.push f) failures
  )

def mergeFailures (base : Array CollectedFailure) (extra : Array CollectedFailure) : Array CollectedFailure :=
  extra.foldl (fun acc f => if acc.contains f then acc else acc.push f) base

def collectAxiomViolations (n : Name) (axioms : Array Name) (allow_sorry? : Bool := false) (moduleName : String := "<unknown>") :
    Array CollectedFailure := Id.run do
  let allowedAxioms := if allow_sorry? then TargetsAllowedAxioms else AllowedAxioms
  let mut out : Array CollectedFailure := #[]
  for a in axioms do
    if a ∉ allowedAxioms then
      out := out.push {
        declName := n.toString
        moduleName := moduleName
        kind := "disallowed_axiom"
        summary := "A declaration relies on a disallowed axiom."
        detail := s!"Declaration {n} relies on axiom {a}, which is not in its allowed set ({String.intercalate ", " (allowedAxioms.map Name.toString)})."
      }
  out


def printExpr (ex : Expr) (env : Environment) : IO Format := do
  let ctx:={fileName:="", fileMap:=default}
  Prod.fst <$> (CoreM.toIO (MetaM.run' do ppExpr ex) ctx {env:=env})



def parseBoolFlag (flagName : String) (raw : String) : IO Bool := do
  match raw.trim.toLower with
  | "true" => pure true
  | "false" => pure false
  | _ => throw <| IO.userError s!"Invalid boolean value for --{flagName}: \"{raw}\". Expected true or false."

def descriptorCachePathForModule (mod : Name) : IO System.FilePath := do
  pure ((← findOLean mod).withExtension "descriptor")

def systemTimeLe (a b : IO.FS.SystemTime) : Bool :=
  a.sec < b.sec || (a.sec == b.sec && a.nsec <= b.nsec)

def isDescriptorCacheFresh (mod : Name) (descriptorPath : System.FilePath) : IO Bool := do
  if !(← descriptorPath.pathExists) then
    -- IO.println s!"Descriptor cache file {descriptorPath} does not exist."
    return false
  try
    let descriptorMeta ← descriptorPath.metadata
    let sourceMeta ← (← findLean mod).metadata
    let oleanMeta ← (← findOLean mod).metadata
    let t := descriptorMeta.modified
    -- IO.println s!"Descriptor cache modified at {t.sec}, source modified at {sourceMeta.modified.sec}, olean modified at {oleanMeta.modified.sec}."
    return systemTimeLe sourceMeta.modified t && systemTimeLe oleanMeta.modified t
  catch _ =>
    return false

def collectAxiomsRaw (env : Environment) (n : Name) : Array Name :=
  let (_, s) := (CollectAxioms.collect n).run env |>.run {}
  s.axioms

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

def getDescriptorForModule (timingsRef : IO.Ref TimingState) (mod : Name) (targetDescriptor? : Option FileDescriptor := none) :
    IO (List DeclarationDescriptor × Array CollectedFailure) := do

  let failuresRef ← IO.mkRef (#[] : Array CollectedFailure)

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
        scanCandidates := scanCandidates.push (n, ci)
        namesForHumanScan := namesForHumanScan.push n
    for target in (targetDescriptor?.getD default).decls do
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

  withTiming timingsRef s!"descriptor.validateHumanDeclSafety[{modStr}]" <| do
    for (n, ci) in scanCandidates do
      if (humanDeclMap.get? n).isSome then
        if let .defnInfo dv := ci then
          if dv.safety != .safe then
            let str_safety := match dv.safety with
              | .safe => "safe"
              | .unsafe => "unsafe"
              | .partial => "partial"
            appendFailures failuresRef #[{
              declName := n.toString
              moduleName := modStr
              kind := "unsafe_partial"
              summary := "The declaration is unsafe or partial."
              detail := s!"Declaration {n} ({ci.kind}) has safety \"{str_safety}\"."
            }]

  let mut ret : Array (DeclarationDescriptor × DeclarationRanges) ← withTiming timingsRef s!"descriptor.buildDescriptorSeed[{modStr}]" <| do
    let mut ret : Array (DeclarationDescriptor × DeclarationRanges) := #[]
    for (n, ci) in scanCandidates do
      if let some rng := humanDeclMap.get? n then
        ret := ret.push ({
          ci := .fromConstantInfo mod ci,
          contents := default, -- we fill this in later since we need the file map for it
          context := default, -- we fill this in later since we need the file map for it
          target? := tagged_decl_names.contains n,
          -- sourceFile? := sourceFile?,
          axioms := default, -- we fill this in later when we do regression and axiom checking
          resolved? := default -- same
        }, rng)
    pure ret

  let mut axiomMap : Std.HashMap Name (Array Name) ← withTiming timingsRef s!"descriptor.precomputeAxioms[{modStr}]" <| do
    let names := ret.map (fun (desc, _) => desc.ci.name)
    return collectAxiomsBatched env'' names

  if (targetDescriptor?.getD default).decls.length > 0 then
    axiomMap ← withTiming timingsRef s!"descriptor.compareAgainstTarget[{modStr}]" <| do
      let mut axiomMap := axiomMap
      for target in (targetDescriptor?.getD default).decls do
        if (humanDeclMap.get? target.ci.name).isSome then
          if let some ci'_info := ciMap.get? target.ci.name then
            let ci' := .fromConstantInfo mod ci'_info
            if target.ci.kind ≠ ci'.kind then
              appendFailures failuresRef #[{
                declName := target.ci.name.toString
                moduleName := modStr
                kind := "kind_mismatch"
                summary := "The declaration kind in the attempted contribution does not match the current version."
                detail := s!"Declaration {target.ci.name} has kind \"{ci'.kind}\" in the attempted contribution, but is expected to have kind \"{target.ci.kind}\"."
              }]
            if ci'.kind=="theorem" then
              if Not (equivThmDataNormalized target.ci ci' mod (targetDescriptor?.map FileDescriptor.moduleName)) then
                appendFailures failuresRef #[{
                  declName := target.ci.name.toString
                  moduleName := modStr
                  kind := "theorem_mismatch"
                  summary := "A theorem statement in the attempted contribution does not match the current version."
                  detail := s!"Theorem {target.ci.name} has type \"{ci'.type}\" in the attempted contribution, but is expected to match the type of: {target.ci.type}."
                }]
            if ci'.kind=="def" then
              if Not (equivDefnDataNormalized target.ci ci' mod (targetDescriptor?.map FileDescriptor.moduleName) (`sorryAx ∉ target.axioms)) then
                let valStr ← if `sorryAx ∉ target.axioms then
                  pure s!" Additionally, attempted value: \"{ci'.value?.get!}\"; expected value: \"{target.ci.value?.get!}\"."
                else pure ""
                appendFailures failuresRef #[{
                  declName := target.ci.name.toString
                  moduleName := modStr
                  kind := "definition_mismatch"
                  summary := "A definition statement in the attempted contribution does not match the current version."
                  detail := s!"Definition {target.ci.name} has type \"{ci'.type}\" in the attempted contribution, and is expected to have type \"{target.ci.type}\".{valStr}"
                }]

            let allow_sorry? := target.ci.name ∈ tagged_decl_names && (`sorryAx ∈ target.axioms)
            -- we allow sorry axiom only on marked targets, where the target itself relies on sorry
            let (axioms, axiomMap') := match axiomMap.get? target.ci.name with
              | some axioms => (axioms, axiomMap)
              | none =>
                let axioms := collectAxiomsRaw env'' target.ci.name
                (axioms, axiomMap.insert target.ci.name axioms)
            axiomMap := axiomMap'
            appendFailures failuresRef (collectAxiomViolations target.ci.name axioms allow_sorry? modStr)
          else
            appendFailures failuresRef #[{
              declName := target.ci.name.toString
              moduleName := modStr
              kind := "missing_declaration"
              summary := "A declaration in the current file version was not found in the attempted contribution."
              detail := s!"Declaration {target.ci.name} was found in the current file version, but no declaration with this name was found in the attempted contribution."
            }]
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
      appendFailures failuresRef (collectAxiomViolations desc.ci.name axioms desc.target? modStr)
      pure {desc with
        contents := Substring.mk fileMap.source (fileMap.ofPosition rng.range.pos) (fileMap.ofPosition rng.range.endPos) |>.toString,
        context := Substring.mk fileMap.source ⟨0⟩ (fileMap.ofPosition rng.range.pos) |>.toString,
        axioms := axioms,
        resolved? := axioms.all (fun a => a ∈ AllowedAxioms) -- we consider a declaration resolved if it relies only on allowed axioms, meaning it doesn't rely on sorry or any disallowed axioms
      })

  let failures ← failuresRef.get
  return (output.toList, failures)

unsafe def getTargets' (timingsRef : IO.Ref TimingState)
    (submission_data : (String × Name × System.FilePath))
    (target_data : Option (String × Name × System.FilePath) := none)
    (useCache : Bool := true)
    : IO (FileDescriptor × Array CollectedFailure) := do
  let submission_module := submission_data.2.1
  let target_module := target_data.map (fun d => d.2.1) |>.getD submission_module
  let submissionSourceFile ← findLean submission_module
  if target_module == submission_module then
    let (decls, failures) ← getDescriptorForModule timingsRef submission_module
    return ({
      decls := decls,
      path := submissionSourceFile,
      moduleName := submission_module,
      contents := submission_data.1
    }, failures)
  else
    let targetSourceFile ← findLean target_module
    -- if useCache is true, get and parse descriptor from cache if possible:
    let extractedTargetDescriptor? : Option FileDescriptor ← if useCache then do
      let cachePath ← descriptorCachePathForModule target_module
      if (← isDescriptorCacheFresh target_module cachePath) then
        let cachedDescriptorStr ← IO.FS.readFile cachePath
        let cachedDescriptorJson ← match Json.parse cachedDescriptorStr with
          | Except.ok json => pure json
          | Except.error err => do
            IO.eprintln s!"Warning: Failed to parse cached descriptor at {cachePath}: {err}. Will regenerate descriptor from source. Error details: {err}"
            pure Json.null

        match @FromJson.fromJson? FileDescriptor _ cachedDescriptorJson with
        | Except.ok desc => pure (some desc)
        | Except.error err => do
          IO.eprintln s!"Warning: Failed to parse cached descriptor at {cachePath}: {err}. Will regenerate descriptor from source. Error details: {err}"
          pure none
      else do
        IO.eprintln s!"Cached descriptor at {cachePath} is not fresh. Will regenerate descriptor from source."
        pure none
    else pure none

    let (targetDescriptor, targetFailures) ← (match extractedTargetDescriptor? with
      | some desc => pure (desc, #[])
      | none => do
        let (regeneratedDecls, regeneratedFailures) ← getDescriptorForModule timingsRef target_module
        pure ({
          decls := regeneratedDecls,
          path := targetSourceFile,
          moduleName := target_module,
          contents := (target_data.getD default).1
        }, regeneratedFailures) : IO (FileDescriptor × Array CollectedFailure))

    let (submittedDescriptor, submissionFailures) ← getDescriptorForModule timingsRef submission_module targetDescriptor
    return ({
      decls := submittedDescriptor,
      path := submissionSourceFile,
      moduleName := submission_module,
      contents := submission_data.1
    }, mergeFailures targetFailures submissionFailures)



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

  let useCache ← parseBoolFlag "use_cache" (args.flag! "use_cache" |>.as! String)

  try
    let targetContent? ← withTiming timingsRef "cli.resolveTargetInput" <| do
      target?.mapM (fun t => getFileOrModuleContents t)


    let submissionContent ← withTiming timingsRef "cli.resolveSubmissionInput" <| do
      getFileOrModuleContents submission
    let (descriptor, failures) ← getTargets' timingsRef submissionContent targetContent? useCache
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
    if useCache && failures.size == 0 then
      let cachePath ← descriptorCachePathForModule submissionContent.2.1
      let _ ← withTiming timingsRef "cli.writeCacheDescriptor" <| do
        IO.FS.writeFile cachePath (json.pretty)
      IO.println s!"Wrote cached file descriptor to {cachePath}"

    if failures.size > 0 then
      let diagnosticsJson ← withTiming timingsRef "cli.encodeDiagnosticsJson" <| do
        pure (toJson failures).pretty
      IO.println "<AGORA_DIAGNOSTICS_ALL>"
      IO.println diagnosticsJson
      IO.println "</AGORA_DIAGNOSTICS_ALL>"

    printTimingSummary timingsRef
    if failures.size > 0 then
      return (1 : UInt32)
    else
      IO.println "Finished with no errors."
      return (0 : UInt32)
  catch e =>
    printTimingSummary timingsRef
    IO.eprintln s!"Error: {e}"
    return (1 : UInt32)


unsafe def getTargets : Cmd := `[Cli|
  get_targets VIA getTargetsCLI; ["0.0.1"]
"Get targets from a string."

  FLAGS:
    submission : String; "In file mode, the submission module name."
    target : String; "The target module name. Optional; if not provided, then target=submission is assumed."
    use_cache : String; "If true, then look for cached .descriptor file next to the target .olean. If success, write new .descriptor to submission olean. Default: true."
    save : String; "If provided, save the file descriptor to this file as json to specified path. Default is no save."

  EXTENSIONS:
    defaultValues! #[("target", ""), ("save", ""), ("use_cache", "true")]
]


unsafe def main (args : List String) : IO UInt32 :=
  getTargets.validate args
