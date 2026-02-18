import Cli.Extensions
import VerifiedAgora.tagger
import VerifiedAgora.Utils.Utils
import Batteries.Lean.TagAttribute
open Lean Core Elab IO Meta Term Command Tactic Cli Environment CollectAxiomsBatched



def getDeclDescriptors (env : Environment) (timingsRef : IO.Ref TimingState) (source : String) (mod? : Option Name) : IO (Array DeclarationDescriptor) := do

  let targetSet := targetAttribute.getDecls env
  let ciMap ← getConstantsInModule env mod?
  let humanDeclMap ← batchHumanDecls ciMap.keys.toArray env
  let axiomMap := collectAxiomsBatched env humanDeclMap.keys.toArray
  let fileMap := source.toFileMap
  let allAttributes := getAttributeNames env


  let output ← humanDeclMap.toArray.filterMapM (fun (n, rng) => do
    if let some ci := ciMap.get? n then do
      if let some axioms := axiomMap.get? n then do
        let target? := n ∈ targetSet
        let attributes := #[]
        --allAttributes.filter (fun attr => (← hasTag attr n) |>.toArray TODO
        let isInstance := isInstanceCore env n
        let entry? := Meta.instanceExtension.getState env |>.instanceNames.find? n




        pure <| some {
          name := n,
          ci := ← ConstantData.fromConstantInfo ci env,
          contents := Substring.mk fileMap.source (fileMap.ofPosition rng.range.pos) (fileMap.ofPosition rng.range.endPos) |>.toString,
          range := rng.range, -- keep the ranges around for creating the merged file contents
          axioms := axioms,
          target := target?,
          resolved := axioms.all (fun a => a ∈ AllowedAxioms),
          modified := false, -- will fill this in later during validation
          new := false -- will fill this in later during validation
          attributes := attributes,
          isInstance := (isInstance, entry?.map (·.priority), entry?.map (·.attrKind))

        }
      else pure none
    else pure none
  )

  return output


def mergeDescriptors (submissionDescriptor : FileDescriptor) (rbuf : Array (DeclarationDescriptor × Option DeclarationDescriptor × Bool)) : FileDescriptor := Id.run do
  let mergedDecls := rbuf.map (fun (submDesc, targetDesc?, useSubm?) =>
    if let some targetDesc := targetDesc? then
      if useSubm? then submDesc else targetDesc
    else submDesc
  )
  -- now want to build merged file contents. To do this, we will take the submission file contents as base, and for each decl this does not have useSubm? = true, we will replace the corresponding range in the file with the target decl contents' range. We will do this in descending line number order of the submDesc's start line number. We can be assured that the ranges will not overlap because of how we constructed the descriptors.
  let sortedRbuf := rbuf.qsort (fun (d1, _, _) (d2, _, _) => d1.range.pos.line > d2.range.pos.line)
  let mut finalContents := submissionDescriptor.contents
  for (submDesc, targetDesc?, useSubm?) in sortedRbuf do
    -- if useSubm? is true, continue.
    -- if useSubm? is false and targetDesc? is some, then replace the corresponding range in submissionDescriptor.contents with targetDesc.contents
    let fileMap := submissionDescriptor.contents.toFileMap
    if !useSubm? && targetDesc?.isSome then
      let targetDesc := targetDesc?.get!
      let range := submDesc.range
      let before := Substring.mk finalContents 0 (fileMap.ofPosition range.pos) |>.toString
      let after := Substring.mk finalContents (fileMap.ofPosition range.endPos) finalContents.endPos |>.toString
      let newContents := before ++ targetDesc.contents ++ after
      finalContents := newContents
  { submissionDescriptor with decls := mergedDecls, contents := finalContents }


def validateDescriptor (submissionDescriptor : FileDescriptor) (targetDescriptor? : Option FileDescriptor) (timingsRef : IO.Ref TimingState) : IO (FileDescriptor × Array CollectedFailure) := do
  let failuresRef ← IO.mkRef (#[] : Array CollectedFailure)
  -- check target is a subset of submission
  let submissionSet := Std.HashMap.ofList <| submissionDescriptor.decls.toList.map (fun d => (d.name, d))
  let targetSet := Std.HashMap.ofList <| targetDescriptor?.getD default |>.decls.toList.map (fun d => (d.name, d))

  if let some targetDescriptor := targetDescriptor? then
    for desc in targetDescriptor.decls do
      if !submissionSet.contains desc.name then
        let failure : CollectedFailure := {
          declName := desc.name.toString,
          moduleName := submissionDescriptor.moduleName.toString,
          kind := "missing_declaration",
          summary := "A declaration from the target is missing in the submission.",
          detail := s!"The declaration {desc.name} is present in the target but not found in the submission."
        }
        appendFailures failuresRef #[failure]

  --reconstruction buffer, of elements (submissionDecl, targetDecl?, useSubmission?)
  let mut rbuf : Array (DeclarationDescriptor × Option DeclarationDescriptor × Bool) := #[]

  -- for each decl in submission:
  for desc in submissionDescriptor.decls do
    -- first check safety
    let mut valid? := true

    if let .defnData dv := desc.ci then
      if dv.safety != .safe then
        valid? := false
        let str_safety := match dv.safety with
          | .safe => "safe"
          | .unsafe => "unsafe"
          | .partial => "partial"
        appendFailures failuresRef #[{
          declName := desc.name.toString
          moduleName := submissionDescriptor.moduleName.toString
          kind := "unsafe_partial"
          summary := "The declaration is unsafe or partial."
          detail := s!"Declaration {desc.name} has safety \"{str_safety}\"."
        }]

    -- then check if there is a matching decl name in target.
    let targetDesc? := targetSet.get? desc.name
    if let some targetDesc := targetDesc? then
    -- then check if kind matches
      if desc.ci.kind != targetDesc.ci.kind then
        valid? := false
        appendFailures failuresRef #[{
          declName := desc.name.toString
          moduleName := submissionDescriptor.moduleName.toString
          kind := "kind_mismatch"
          summary := "The declaration kind does not match the target."
          detail := s!"Declaration {desc.name} has kind {desc.ci.kind} in submission but {targetDesc.ci.kind} in target."
        }]
    -- then check if isInstance, instance priority, and instance kind matches
      if desc.isInstance != targetDesc.isInstance then
        valid? := false
        appendFailures failuresRef #[{
          declName := desc.name.toString
          moduleName := submissionDescriptor.moduleName.toString
          kind := "instance_mismatch"
          summary := "The declaration instance status does not match the target."
          detail := s!"Declaration {desc.name} has instance data {desc.isInstance} in submission but {targetDesc.isInstance} in target."
        }]
    -- then check if target matches
      if desc.target != targetDesc.target then
        valid? := false
        appendFailures failuresRef #[{
          declName := desc.name.toString
          moduleName := submissionDescriptor.moduleName.toString
          kind := "target_mismatch"
          summary := "The declaration target does not match the target."
          detail := s!"Declaration {desc.name} has target {desc.target} in submission but {targetDesc.target} in target."
        }]
    -- then check if attributes match
      if (Std.HashSet.ofArray desc.attributes) != (Std.HashSet.ofArray targetDesc.attributes) then
        valid? := false
        appendFailures failuresRef #[{
          declName := desc.name.toString
          moduleName := submissionDescriptor.moduleName.toString
          kind := "attribute_mismatch"
          summary := "The declaration attributes do not match the target."
          detail := s!"Declaration {desc.name} has attributes {desc.attributes.toList} in submission but {targetDesc.attributes.toList} in target."
        }]
    -- check if types match
      if desc.ci.type != targetDesc.ci.type then
        valid? := false
        appendFailures failuresRef #[{
          declName := desc.name.toString
          moduleName := submissionDescriptor.moduleName.toString
          kind := "type_mismatch"
          summary := "The declaration type does not match the target."
          detail := s!"Declaration {desc.name} has type {desc.ci.type} in submission but {targetDesc.ci.type} in target."
        }]
    -- check if values match (if sorry not in value of target)
      if targetDesc.resolved then
        if desc.ci.value? != targetDesc.ci.value? then
          valid? := false
          appendFailures failuresRef #[{
            declName := desc.name.toString
            moduleName := submissionDescriptor.moduleName.toString
            kind := "value_mismatch"
            summary := "The declaration value does not match the target."
            detail := s!"Declaration {desc.name} has value {desc.ci.value?} in submission but {targetDesc.ci.value?} in target."
          }]
    -- then check if axioms are valid (even for non in target)
    let allow_sorry? := if let some targetDesc := targetDesc? then
      targetDesc.target && !targetDesc.resolved else desc.target

    let axiomFailures := collectAxiomViolations desc.name desc.axioms allow_sorry? submissionDescriptor.moduleName.toString
    if axiomFailures.size > 0 then
      valid? := false
      appendFailures failuresRef axiomFailures

    -- if no decl in target, can stop and mark as new. Otherwise, continue
    if let some targetDesc := targetDesc? then
      --mark as modified, and set useSubmission? to true iff targetDecl is not resolved, valid=true, and submission decl is resolved
      let newDesc := { desc with modified := true }
      let useSubmission? := (!targetDesc.resolved && valid? && desc.resolved)
      rbuf := rbuf.push (newDesc, targetDesc, useSubmission?)
    else
      -- mark as new
      let newDesc := { desc with new := true }
      rbuf := rbuf.push (newDesc, none, true)
    -- select whether or not to take submission or target decl and mark as modified
  let finalDesc := mergeDescriptors submissionDescriptor rbuf
  return (finalDesc, (← failuresRef.get))






def getTargets (submissionContent : String) (targetData? : Name × System.FilePath × Bool) (useCache : Bool) (overwriteTarget : Bool) (timingsRef : Ref TimingState): IO (Option FileDescriptor × Array CollectedFailure) := do

  let (targetModule, targetPath, targetExists?) := targetData?
  let targetContents? ← if targetExists? then pure <| some (← IO.FS.readFile targetPath) else pure none

  let targetDecls? : Option (Array DeclDescriptor) ← match targetContents? with
  | some targetContents => do
    let extractedTargetDescriptor? ← if useCache then do
      let cachePath ← descriptorCachePathForModule targetModule
      if (← isDescriptorCacheFresh targetModule cachePath) then
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

    match extractedTargetDescriptor? with
    | some fd => pure (some fd.decls)
    | none =>
      let targetEnv ← importModules #[{ module := targetModule }] {} 0
      let targetDecls ← getDeclDescriptors targetEnv timingsRef targetContents targetModule
      pure (some targetDecls)
  | _ => pure none

  let targetDescriptor? : Option FileDescriptor := match (targetDecls?, targetContents?) with
    | (some targetDecls, some targetContents) => do
        some {
          decls := targetDecls,
          path := targetPath,
          moduleName := targetModule,
          contents := targetContents
        }
    | _ => none

  let (submissionDescriptor, compilationSteps?) ← if (targetContents?.getD default) == submissionContent then
      -- short circuit
      IO.println "Submission content is identical to target content, skipping compilation and using target descriptor directly."
      pure (targetDescriptor?.getD default, none)
    else do
      -- normal case: first compile to get compilationSteps
      let compilationSteps ← withTiming timingsRef "getTargets.compileSubmission" <| do
        let steps ← Lean.Elab.IO.processInput' submissionContent |>.force
        return steps
      -- now get environment after compilation and extract decl descriptors from it
      let submissionEnv? := compilationSteps.getLast?.map (·.after)
      let submissionDescriptor ← match submissionEnv? with
        | some submissionEnv => do
          let submissionDecls ← getDeclDescriptors submissionEnv timingsRef submissionContent none
          pure {
            decls := submissionDecls,
            path := targetPath,
            moduleName := targetModule,
            contents := submissionContent
          }
        | none => throw <| IO.userError "Failed to compile submission content, so could not extract declaration descriptors."
      pure (submissionDescriptor, some compilationSteps)


  let errorMsgs ← if let some compilationSteps := compilationSteps? then do
    let errorMsgs := (← compilationSteps.flatMapM (fun step => do
      let errorMsgsRaw ← step.msgs.filterMapM (fun msg => do
        if msg.severity == .error then do
          let msgStr ← msg.serialize
          pure (some msgStr)
        else
          pure none
      )
      pure errorMsgsRaw
    )) |>.map (fun s => s.toString)
    pure errorMsgs
  else
    pure default

  if errorMsgs.length > 0 then do
    let errorDetails := errorMsgs.toArray.map (fun msg => {
      declName := ""
      moduleName := targetModule.toString
      kind := "compilation_error"
      summary := "The submission failed to compile."
      detail := msg
    })
    return (targetDescriptor?, errorDetails)

  let (finalDescriptor, failures) ← validateDescriptor submissionDescriptor targetDescriptor? timingsRef

  if overwriteTarget then do
    -- then write finalDescriptor.contents to target path (create file if it doesn't already exist) and lake build targetModule (idk what to do about the none case)
    IO.FS.writeFile targetPath finalDescriptor.contents
    let out ← IO.Process.output {
      cmd := "lake"
      args := #["build", targetModule.toString]
      stdin := .null
    }
    if out.exitCode != 0 then
      -- if failure, restore original target file contents (if they existed) or delete target file (if it did not exist). log errors and add to failures as automerge_failure with details of the error. Then return (targetDescriptor?, failures).
      let errorDetails := {
        declName := ""
        moduleName := targetModule.toString
        kind := "automerge_failure"
        summary := "The submission failed to automerge into the target - but the resulting file failed to compile."
        detail := "Stdout:\n" ++ out.stdout ++ "\n\nStderr:\n" ++ out.stderr
      }
      let failures := failures.push errorDetails
      if let some targetContents := targetContents? then
        IO.FS.writeFile targetPath targetContents
      else
        IO.FS.removeFile targetPath
      return (targetDescriptor?, failures)

    -- if success, write finalDescriptor to .descriptor next to olean of target module.
    if useCache then do
      let cachePath ← descriptorCachePathForModule targetModule
      IO.FS.writeFile cachePath (ToJson.toJson finalDescriptor).pretty

  return (some finalDescriptor, failures)



unsafe def getTargetsParser (args : Cli.Parsed) : IO UInt32 := do
  let timingsRef ← IO.mkRef ({} : TimingState)

  let runtimeSearchPath ← searchPathRef.get
  let appBuildLib := (← IO.appDir).parent.get! / "lib"
  let runtimeSearchPath :=
    if appBuildLib ∈ runtimeSearchPath then runtimeSearchPath else runtimeSearchPath ++ [appBuildLib]
  searchPathRef.set (runtimeSearchPath ++ compile_time_search_path%)
  enableInitializersExecution

  try

    let submission := args.flag! "submission" |>.as! String
    let target := args.flag! "target" |>.as! String
    let savePath := args.flag! "save" |>.as! String
    let save? := if savePath == "" then none else some savePath
    let useCache ← parseBoolFlag "use_cache" (args.flag! "use_cache" |>.as! String)
    let overwriteTarget ← parseBoolFlag "overwrite_target" (args.flag! "overwrite_target" |>.as! String)

    let targetData? ← getFileOrModuleName target

    let submissionContent ← withTiming timingsRef "getTargetsParser.resolveSubmissionInput" <| do
      match submission.toNat? with
      | some submissionBytes =>
        let payload_raw : ByteArray ← (← getStdin).read submissionBytes.toUSize
        let payload_str? := String.fromUTF8? payload_raw
        match payload_str? with
        | none =>
          throw <| IO.userError "Error: could not decode stdin as UTF-8"
        | some payload => do
          return payload
      | none => do
        let contents ← getFileOrModuleContents submission
        return contents.1

    let (finalDescriptor?, failures) ← getTargets submissionContent targetData? useCache overwriteTarget timingsRef




    let json ← withTiming timingsRef "cli.encodeDescriptorJson" <| do
      pure (ToJson.toJson finalDescriptor?)
    if save?.isSome then
        let _ ← withTiming timingsRef "cli.writeDescriptorFile" <| do
          IO.FS.writeFile save?.get! (json.pretty)
        IO.println s!"Wrote file descriptor to {save?.get!}"
    else
      IO.println "<DESCRIPTOR>"
      IO.println json.pretty
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
      IO.println "Finished with no errors."
      return (0 : UInt32)
  catch e =>
    IO.eprintln s!"Error: {e}"
    return (1 : UInt32)





unsafe def getTargetsCLI : Cmd := `[Cli|
  get_targets VIA getTargetsParser; ["0.0.1"]
"Get targets from a string."

  FLAGS:
    submission : String; "In buffer mode, number of expected bytes in submission content to read from stdin. In file mode, the path to the submission file. "
    target : String; "The target module/file path. If it exists, we will treat its contents as the target descriptor contents to compare against. Otherwise -- or if no olean found -- we simply treat it as the destination path in the fileDescriptor."
    use_cache : String; "If true, then look for cached .descriptor file next to the target .olean. If success, write new .descriptor to submission olean. Default: true."
    save : String; "If provided, additionally save the file descriptor to this file as json to specified path. Default is no save."
    overwrite_target : String; "If true, then in case of a mismatch between submission and target, will overwrite target with (automerged) submission. Default: true."

  EXTENSIONS:
    defaultValues! #[("save", ""), ("use_cache", "true"), ("overwrite_target", "true")]
]


unsafe def main (args : List String) : IO UInt32 :=
  getTargetsCLI.validate args
