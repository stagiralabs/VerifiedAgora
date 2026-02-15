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
  let ctx := {fileName := "", fileMap := default}
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
  | some out => pure out
  | none => pure {}


/-- Imports the project modules in a single environment and gets all tagged declarations. Requires project to be `lake build`-ed first. -/
unsafe def getAllTargetsInProject (timingsRef : IO.Ref TimingState) (importMods : Array Name) : IO FileDescriptor := do
  let env ← withTiming timingsRef "descriptor.importDependencies" <| do
    let imports := importMods.map (fun mod => ({ module := mod } : Import))
    importModules imports {} 0

  let tagged_decls ← withTiming timingsRef "descriptor.loadTaggedDecls" <| do
    pure <| env.constants.fold (fun acc k ci =>
      if TagAttribute.hasTag targetAttribute env k then ci :: acc else acc
    ) []

  let (scanCandidates, namesForHumanScan) ← withTiming timingsRef "descriptor.scanDeclarations" <| do
    let mut scanCandidates : Array (Name × ConstantInfo) := #[]
    let mut namesForHumanScan : Array Name := #[]
    for ci in tagged_decls do
      if ci.kind ∈ ["theorem", "def"] then
        scanCandidates := scanCandidates.push (ci.name, ci)
        namesForHumanScan := namesForHumanScan.push ci.name
    let mut dedupNames : Array Name := #[]
    let mut seenNames : Std.HashSet Name := {}
    for n in namesForHumanScan do
      if n ∉ seenNames then
        seenNames := seenNames.insert n
        dedupNames := dedupNames.push n
    pure (scanCandidates, dedupNames)

  let humanDeclMap ← withTiming timingsRef "descriptor.batchHumanDeclScan" <| do
    batchHumanDecls namesForHumanScan env

  withTiming timingsRef "descriptor.validateHumanDeclSafety" <| do
    for (n, ci) in scanCandidates do
      if (humanDeclMap.get? n).isSome then
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

  let sourceFileCacheRef ← IO.mkRef ({} : Std.HashMap Name System.FilePath)
  let ret : Array (DeclarationDescriptor × DeclarationRanges) ← withTiming timingsRef "descriptor.buildDescriptorSeed" <| do
    let mut ret : Array (DeclarationDescriptor × DeclarationRanges) := #[]
    for (n, ci) in scanCandidates do
      if let some rng := humanDeclMap.get? n then
        let sourceFile? ←
          match env.getModuleIdxFor? n with
          | some modidx =>
            let declMod := env.header.moduleNames.get! modidx
            let sourceFileCache ← sourceFileCacheRef.get
            match sourceFileCache.get? declMod with
            | some fp => pure (some fp)
            | none =>
              let fp ← findLean declMod
              sourceFileCacheRef.modify (fun m => m.insert declMod fp)
              pure (some fp)
          | none => pure none
        ret := ret.push ({
          ci := ci,
          contents := default,
          context := default,
          axioms := default,
          target? := true,
          resolved? := default,
          sourceFile? := sourceFile?
        }, rng)
    pure ret

  let axiomMap : Std.HashMap Name (Array Name) ← withTiming timingsRef "descriptor.precomputeAxioms" <| do
    let names := ret.map (fun (desc, _) => desc.ci.name)
    pure (collectAxiomsBatched env names)

  let mut loadedFileMaps : Std.HashMap System.FilePath FileMap := {}
  let mut out : Array DeclarationDescriptor := #[]
  for (desc, rng) in ret do
    let source ← match desc.sourceFile? with
    | some fp =>
      match loadedFileMaps.get? fp with
      | some fm => pure fm
      | none => do
        let fm ← withTiming timingsRef "descriptor.loadSourceFile" <| do
          pure <| FileMap.ofString (← IO.FS.readFile fp)
        loadedFileMaps := loadedFileMaps.insert fp fm
        pure fm
    | none => pure default

    let axioms := match axiomMap.get? desc.ci.name with
      | some a => a
      | none => collectAxiomsRaw env desc.ci.name
    validateCollectedAxioms desc.ci.name axioms true

    out := out.push {
      desc with
      contents := Substring.mk source.source (source.ofPosition rng.range.pos) (source.ofPosition rng.range.endPos),
      context := Substring.mk source.source ⟨0⟩ (source.ofPosition rng.range.pos),
      axioms := axioms,
      resolved? := axioms.all (fun a => a ∈ AllowedAxioms)
    }

  return out.toList




def getDefaultImportsViaLakeExe : IO (List Name) := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["exe", "get_default_targets"]
    stdin := .null
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"lake exe get_default_targets failed:\n{out.stderr}\n{out.stdout}"

  let js := Json.parse out.stdout
  match js with
  | Except.error e => throw <| IO.userError s!"Could not parse JSON from get_default_targets: {e}"
  | Except.ok (Json.arr xs) =>
      let names := xs.toList.map (fun
        | Json.str s => s.toName
        | _ => Name.anonymous)
      if names.any (· == Name.anonymous) then
        throw <| IO.userError "get_default_targets returned non-string JSON entries"
      return names
  | Except.ok _ =>
      throw <| IO.userError "get_default_targets did not return a JSON array"



unsafe def getAllTargetsCLI (args : Cli.Parsed) : IO UInt32 := do
  let timingsRef ← IO.mkRef ({} : TimingState)
  let runtimeSearchPath ← searchPathRef.get
  let appBuildLib := (← IO.appDir).parent.get! / "lib"
  let runtimeSearchPath :=
    if appBuildLib ∈ runtimeSearchPath then runtimeSearchPath else runtimeSearchPath ++ [appBuildLib]
  searchPathRef.set (runtimeSearchPath ++ compile_time_search_path%)
  enableInitializersExecution

  try
    let importModsList : List Name ← withTiming timingsRef "cli.resolveImportInput" <| do
      let importFiles := (args.flag! "importFiles" |>.as! String).trim
      if importFiles == "<default>" then
        return (← getDefaultImportsViaLakeExe)
      else
        importFiles.splitOn "," |>.mapM (fun s => do
          let (_, mod, _) ← getFileOrModuleContents (s.trim)
          pure mod
        )

    let mut seenMods : Std.HashSet Name := {}
    let mut importMods : Array Name := #[]
    for mod in importModsList do
      if mod ∉ seenMods then
        seenMods := seenMods.insert mod
        importMods := importMods.push mod

    let descriptors ← getAllTargetsInProject timingsRef importMods

    let json ← withTiming timingsRef "cli.encodeDescriptorJson" <| do
      pure (toJson descriptors).pretty

    IO.println "<DESCRIPTOR>"
    IO.println json
    IO.println "</DESCRIPTOR>"
    printTimingSummary timingsRef
    return (0 : UInt32)
  catch e =>
    printTimingSummary timingsRef
    IO.eprintln s!"Error: {e}"
    return (1 : UInt32)




unsafe def getAllTargets : Cmd := `[Cli|
    get_all_targets VIA getAllTargetsCLI; ["0.0.1"]
  "Get targets from a string."

    FLAGS:
      importFiles : String; "(Comma-seperated list of) file paths/modules for target import files."

    EXTENSIONS:
      defaultValues! #[("importFiles", "<default>")]
  ]


unsafe def main (args : List String) : IO UInt32 := do
  getAllTargets.validate args
