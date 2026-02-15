import Cli.Extensions
import VerifiedAgora.tagger
import VerifiedAgora.Frontend
import VerifiedAgora.TacticInvocation
import VerifiedAgora.Utils
open Lean Core Elab IO Meta Term Command Tactic Cli

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


/-- Imports the entire project (in the way `lake build` would) and gets all tagged declarations. Requires project to be `lake build`-ed first. -/
unsafe def getAllTargetsInProject (timingsRef : IO.Ref TimingState) (mod : Name) : IO FileDescriptor := do
  -- let moduleName ← moduleNameOfFileName importFile none
  let modStr := mod.toString

  let env ← withTiming timingsRef s!"descriptor.importDependencies[{modStr}]" <| do
    let m : Import := { module := mod }
    importModules #[m] {} 0

  let tagged_decls ← withTiming timingsRef s!"descriptor.loadTaggedDecls[{modStr}]" <| do
    pure <| env.constants.fold (fun acc k ci =>
      if TagAttribute.hasTag targetAttribute env k then ci::acc else acc
    ) []
  let mut out : List DeclarationDescriptor := []
  for decl in tagged_decls do
    let modidx := env.getModuleIdxFor? decl.name
    let declMod := env.header.moduleNames.get! modidx.get!
    let fp ← findLean declMod
    let source ← withTiming timingsRef s!"descriptor.loadSourceFile[{modStr}]" <| do
      pure <| FileMap.ofString (← IO.FS.readFile fp)
    let location := declRangeExt.find? (env) decl.name |>.getD ⟨default, default⟩
    let range := location.range
    let contents := Substring.mk source.source (source.ofPosition range.pos) (source.ofPosition range.endPos)
    let context := Substring.mk source.source ⟨0⟩ (source.ofPosition range.pos)

    let axioms ← withTiming timingsRef s!"descriptor.collectAxioms[{modStr}]" <| do
      checkAxioms env decl.name true
    let resolved? := axioms.all (fun a => a ∈ AllowedAxioms)

    out := {
      ci := decl,
      contents := contents,
      context := context,
      axioms := axioms,
      target? := true,
      resolved? := resolved?,
      sourceFile? := some fp
    } :: out

  return out




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
    let importMods : List Name ← withTiming timingsRef "cli.resolveImportInput" <| do
      let importFiles := (args.flag! "importFiles" |>.as! String).trim
      if importFiles == "<default>" then
        getDefaultImportsViaLakeExe
      else
        importFiles.splitOn "," |>.mapM (fun s => do
          let (_,mod,_) ← getFileOrModuleContents (s.trim)
          pure mod
        )

    let mut descriptors : List DeclarationDescriptor := []
    for mod in importMods do
      let targets ← getAllTargetsInProject timingsRef mod
      for decl in targets do
        descriptors := decl :: descriptors
    descriptors := descriptors.reverse

    let json ← withTiming timingsRef "cli.encodeDescriptorJson" <| do
      pure (toJson descriptors).pretty

    IO.println "<DESCRIPTOR>"
    IO.println json
    IO.println "</DESCRIPTOR>"
    printTimingSummary timingsRef
    return 0
  catch e =>
    printTimingSummary timingsRef
    IO.eprintln s!"Error: {e}"
    return 1




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
