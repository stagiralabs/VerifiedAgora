import Cli.Extensions
import VerifiedAgora.tagger
import VerifiedAgora.Utils.Utils
open Lean Core Elab IO Meta Term Command Tactic Cli Environment CollectAxiomsBatched

/-- Imports the project modules in a single environment and gets all tagged declarations. Requires project to be `lake build`-ed first. -/
unsafe def getAllTargetsInProject (timingsRef : IO.Ref TimingState) (importMods : Array Name) (checkAll? : Bool) :
    IO (List FileDescriptor × Array CollectedFailure) := do
  let env ← withTiming timingsRef "descriptor.importDependencies" <| do
    let imports := importMods.map (fun mod => ({ module := mod } : Import))
    importModules imports {} 0

  let tagged_decls ← withTiming timingsRef "descriptor.loadTaggedDecls" <| do
    pure <| env.constants.fold (fun acc k ci =>
      if TagAttribute.hasTag targetAttribute env k then ci :: acc else acc
    ) []
  let tagged_decl_names := tagged_decls.map (fun ci => ci.name) |>.foldl (·.insert ·) Std.HashSet.empty
  let failuresRef ← IO.mkRef (#[] : Array CollectedFailure)

  let (scanCandidates, namesForHumanScan) ← withTiming timingsRef "descriptor.scanDeclarations" <| do
    let mut scanCandidates : Array (Name × ConstantInfo) := #[]
    let mut namesForHumanScan : Array Name := #[]
    let decls_to_scan ← if checkAll?
      then
        let temp ← getConstantsInModules env importMods
        pure <| temp.toList.map (fun (_, ci) => ci)
      else
        pure tagged_decls
    IO.println s!"Scanning {decls_to_scan.length} declarations for targets..."
    for ci in decls_to_scan do
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
    batchHumanDecls namesForHumanScan env true

  withTiming timingsRef "descriptor.validateHumanDeclSafety" <| do
    for (n, ci) in scanCandidates do
      if (humanDeclMap.get? n).isSome then
        if let .defnInfo dv := ci then
          if dv.safety != .safe then
            let str_safety := match dv.safety with
              | .safe => "safe"
              | .unsafe => "unsafe"
              | .partial => "partial"
            let moduleName := match env.getModuleIdxFor? n with
              | some idx => (env.header.moduleNames.get! idx).toString
              | none => "<unknown>"
            failuresRef.modify (fun failures => failures.push {
              declName := n.toString
              moduleName := moduleName
              kind := "unsafe_partial"
              summary := "The declaration is unsafe or partial."
              detail := s!"Declaration {n} ({ci.kind}) has safety \"{str_safety}\"."
            })

  let sourceFileCacheRef ← IO.mkRef ({} : Std.HashMap Name System.FilePath)
  let ret : Array (DeclarationDescriptor × (Option Name) × DeclarationRanges) ← withTiming timingsRef "descriptor.buildDescriptorSeed" <| do
    let mut ret : Array (DeclarationDescriptor × (Option Name) × DeclarationRanges) := #[]
    for (n, ci) in scanCandidates do
      if let some rng := humanDeclMap.get? n then
        let mod? ←
          match env.getModuleIdxFor? n with
          | some modidx =>
            let declMod := env.header.moduleNames.get! modidx
            let sourceFileCache ← sourceFileCacheRef.get
            match sourceFileCache.get? declMod with
            | some _ => pure (some declMod)
            | none =>
              let fp ← findLean declMod
              sourceFileCacheRef.modify (fun m => m.insert declMod fp)
              pure (some declMod)
          | none => pure none

        ret := ret.push ({
          name := n,
          range := rng.range,
          modified := false, --meaningless
          new := false, --meaningless
          attributes := default, --will fill this in later
          isInstance := default, --will fill this in later
          ci := ← (ConstantData.fromConstantInfo ci env),
          contents := default,
          axioms := default,
          target := tagged_decl_names.contains n,
          resolved := default
        }, mod?, rng)
    pure ret

  let axiomMap : Std.HashMap Name (Array Name) ← withTiming timingsRef "descriptor.precomputeAxioms" <| do
    let names := ret.map (fun (desc, _, _) => desc.ci.name)
    pure (collectAxiomsBatched env names)

  let mut loadedFileMaps : Std.HashMap System.FilePath FileMap := {}
  let mut out : Array (DeclarationDescriptor × Name) := #[]
  for (desc, mod?, rng) in ret do
    let source ← match mod? with
    | some mod => do
      let fp? := (← sourceFileCacheRef.get).get? mod
      match fp? with
      | some fp => match loadedFileMaps.get? fp with
        | some fm => pure fm
        | none => do
          let fm ← withTiming timingsRef "descriptor.loadSourceFile" <| do
            pure <| FileMap.ofString (← IO.FS.readFile fp)
          loadedFileMaps := loadedFileMaps.insert fp fm
          pure fm
      | none => pure default
    | none => pure default

    let axioms := match axiomMap.get? desc.ci.name with
      | some a => a
      | none => collectAxiomsRaw env desc.ci.name
    let moduleName := mod?.map Name.toString |>.getD "<unknown>"
    let axiomFailures := collectAxiomViolations desc.ci.name axioms (tagged_decl_names.contains desc.ci.name) moduleName
    failuresRef.modify (fun failures => failures ++ axiomFailures)

    out := out.push ({
      desc with
      contents := Substring.mk source.source (source.ofPosition rng.range.pos) (source.ofPosition rng.range.endPos) |>.toString,
      axioms := axioms,
      resolved := axioms.all (fun a => a ∈ AllowedAxioms)
    }, mod?.getD default)

  let out' : Array (DeclarationDescriptor × Name × System.FilePath × String) ← out.mapM (fun (desc, mod) => do
    let fp := (← sourceFileCacheRef.get).get? mod |>.getD default
    let contents := match loadedFileMaps[fp]? with
      | some fm => fm.source
      | none => default
    pure (desc, mod, fp, contents)
    )

  let out'' := out'.groupByKey (fun (_, mod, _, _) => mod) |>.toArray.map (fun (mod, vals) =>
    let decls := vals.map (fun (desc, _, _, _) => desc)
    let path := match vals[0]? with
      | some (_, _, fp, _) => fp
      | none => default
    let contents := match vals[0]? with
      | some (_, _, _, contents) => contents
      | none => default
    { decls := decls, path := path, moduleName := mod, contents := contents }
  )

  let failures ← failuresRef.get
  return (out''.toList, failures)




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
  let merged ← Lean.addSearchPathFromEnv (runtimeSearchPath ++ compile_time_search_path%)
  searchPathRef.set merged
  enableInitializersExecution

  try
    let importModsList : List Name ← withTiming timingsRef "cli.resolveImportInput" <| do
      let importFiles := (args.flag! "import_files" |>.as! String).trim
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

    let checkFiles? := (args.flag! "check_all" |>.as! String).trim.toLower == "true"


    let (descriptors, failures) ← getAllTargetsInProject timingsRef importMods checkFiles?

    let json ← withTiming timingsRef "cli.encodeDescriptorJson" <| do
      pure (toJson descriptors).pretty

    IO.println "<DESCRIPTOR>"
    IO.println json
    IO.println "</DESCRIPTOR>"

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
      return (0 : UInt32)
  catch e =>
    printTimingSummary timingsRef
    IO.eprintln s!"Error: {e}"
    return (1 : UInt32)




unsafe def getAllTargets : Cmd := `[Cli|
    get_all_targets VIA getAllTargetsCLI; ["0.0.1"]
  "Get targets from a string."

    FLAGS:
      import_files : String; "(Comma-seperated list of) file paths/modules for target import files. Default: defaultTargets in your lakefile"
      check_all : Bool; "If true, check all declarations in the imported modules. Default: false."

    EXTENSIONS:
      defaultValues! #[("import_files", "<default>"), ("check_all", "false")]
  ]


unsafe def main (args : List String) : IO UInt32 := do
  getAllTargets.validate args
