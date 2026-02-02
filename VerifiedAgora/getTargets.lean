import Cli.Extensions
import VerifiedAgora.tagger
import VerifiedAgora.Frontend
import VerifiedAgora.TacticInvocation
import VerifiedAgora.Utils
open Lean Core Elab IO Meta Term Command Tactic Cli



unsafe def replayFileDirect (final_env : Environment) (targets : Array _root_.Info := #[]) (marked : List Name := []): IO (Array _root_.Info) := do
  let mod ← mkModuleData final_env
  let env ← importModules mod.imports {} 0
  IO.println "Finished imports"
  let mut newConstants := {}
  for name in mod.constNames, ci in mod.constants do
    newConstants := newConstants.insert name ci
  let mut env' ← env.replay newConstants
  IO.println "Finished replay"
  --env' ← setImportedEntries env' #[mod]
  --env' ← finalizePersistentExtensions env' #[mod] {}
  let ctx:={fileName:="", fileMap:=default}
  let mut ret:Array _root_.Info:= #[]
  for (n,ci) in env'.constants.map₂  do
    if ci.kind ∈ ["theorem", "def"] then
      IO.println "---"
      IO.println ci.kind
      IO.println n
      IO.println <| ←  Prod.fst <$> (CoreM.toIO (MetaM.run' do ppExpr ci.type) ctx {env:=env'})
      if ci.kind=="def" then
        IO.println s!":= {ci.value!}"
      let (_,s):=(CollectAxioms.collect n).run env' |>.run {}
      IO.println s.axioms
      --let nc:=isNoncomputable env' n
      --IO.println s!"noncomputable: {nc}"
      ret:=ret.push ⟨ n,ci,s.axioms⟩
      if let .defnInfo dv := ci then
        if dv.safety != .safe then
          throw <| IO.userError s!"unsafe/partial function {n} detected"

  if targets.size>0 then
    for ⟨ n,ci,axs⟩ in targets do
      if let some ci':=env'.constants.map₂.find? n then
        if ci.kind ≠ ci'.kind then
          throw <| IO.userError s!"{ci'.kind} {n} is not the same kind as the requirement {ci.kind} {n}"
        if ci'.kind=="theorem" then
          if Not (equivThm ci ci') then
            throw <| IO.userError s!"theorem {n} does not have the same type as the requirement"
        if ci'.kind=="def" then
          if Not (equivDefn ci ci' (`sorryAx ∉ axs)) then
            throw <| IO.userError s!"definition {n} does not match the requirement"
          --if (¬ nc) && isNoncomputable env' n then
          --  throw <| IO.userError s!"definition {n} is noncomputable"
        -- let allow_sorry? := marked.length > 0 || n ∈ marked
        let allow_sorry? := n ∈ marked
        checkAxioms env' n allow_sorry?
      else
        throw <| IO.userError s!"{n} not found in submission"
  --env'.freeRegions
  --region.free
  return ret



-- def process (submitted : Environment) (target : Option Environment := none) : IO FileDescriptor := do
--   let success ←match target with
--   | none =>
--     return replayFileDirect submitted
--   | some target =>
--     let targetInfos ← replayFileDirect target
--     let task ← IO.asTask (replayFileDirect submitted targetInfos)
--     if let .error e:=task.get then
--       IO.eprintln s!"found a problem in submission."
--       throw e
--     IO.println s!"Finished with no errors."



def Lean.Name.isHumanTheorem (name : Name) : CoreM Bool := do
  let hasDeclRange := (← Lean.findDeclarationRanges? name).isSome
  -- let isTheorem ← Name.isTheorem name
  let notProjFn := !(← Lean.isProjectionFn name)
  return hasDeclRange --&& isTheorem
    && notProjFn


def onlyHuman (targets : List (CompilationStep × ConstantInfo)) : IO (List (CompilationStep × ConstantInfo)) := do
  let mut targets_new : Array (CompilationStep × ConstantInfo) := #[]

  for (cmd, ci) in targets do
    let pf_env := cmd.after
    let ctx : Core.Context := {fileName := "", fileMap := default}
    let state : Core.State := {env := pf_env}
    let isHuman := match (← CoreM.run (Lean.Name.isHumanTheorem ci.name) ctx state |>.toIO').toOption with
      | some x => x.1
      | none => false
    if not isHuman then
      continue

    targets_new := targets_new.push (cmd, ci)
  return targets_new.toList


unsafe def getTargets' (submitted : String) (target? : Option String := none) (diff? : Bool := False) (source_file : Option System.FilePath := none): IO FileDescriptor := do
  let target := target?.getD submitted
  let target_steps := Lean.Elab.IO.processInput' target
  let targets_cs := target_steps.bind fun c => (MLList.ofList c.diff).map fun i => (c, i)
  let targets_flat ← (onlyHuman (← targets_cs.force))
  let submitted_flat : List (CompilationStep × ConstantInfo) ← if target?.isNone then pure targets_flat else do
    let submitted_steps := Lean.Elab.IO.processInput' submitted
    let temp ← submitted_steps.force
    IO.println s!"Processed {temp.length} compilation steps in submission"

    let submitted_cs := submitted_steps.bind fun c => (MLList.ofList c.diff).map fun i => (c, i)
    onlyHuman (← submitted_cs.force)

  /- now that we have the decls for both target and submission, we need to:
    1. mark the decls that are tagged
    2. check rules:
      a. decls in target must be present in submission with same type
      b. the tagged items in the target must also be the only tagged items in the submission
      c. both target and submission must both have no errors, and only allow for warnings within the tagged items
    3. if the rules pass, check against safeVerify. Namely, get the environment after the final item in both the submitted/target lists, called env_sub, env_targ. if target?.isNone, then run replayFileDirect env_targ []. store the outputs and run replayFileDirect env_sub with the outputs from the target run as the targets. This outputs a list of infos.
    4. if the latter safeVerify passes, continue. else return error
    5. construct a fileDescriptor from submitted_flat.
  -/
  let final_env_targets? := targets_flat.getLast?.map (fun (c, _) => c.after)
  let final_env_submitted? := submitted_flat.getLast?.map (fun (c, _) => c.after)

  match (final_env_submitted?, final_env_targets?) with
  | (some env_sub, some env_targ) =>
    IO.println "[Finished imports]"
    let targetTargetDecls := targetAttribute.getDecls env_targ
    let targetSubmittedDecls := targetAttribute.getDecls env_sub
    let targetData := targets_flat.map (fun (c, ci) => (c, ci, targetTargetDecls.contains ci.name))
    let submittedData := submitted_flat.map (fun (c, ci) => (c, ci, targetSubmittedDecls.contains ci.name))

    -- check rules
    let target_decls := targetData.map (fun (_, ci, _) => (ci.name, ci.type))
    let submitted_decls := submittedData.map (fun (_, ci, _) => (ci.name, ci.type))
    let same_decls := target_decls == submitted_decls
    if not same_decls then
      throw <| IO.userError s!"The submission does not contain the same declarations as the target:\n {target_decls}\n [vs]\n {submitted_decls}"
    IO.println "Checked same declarations"

    let targets_tagged := targetData.filterMap (fun (_, ci, is_tagged) => if is_tagged then some (ci.name, ci.type) else none)
    let submitted_tagged := submittedData.filterMap (fun (_, ci, is_tagged) => if is_tagged then some (ci.name, ci.type) else none)
    let same_tagged := targets_tagged == submitted_tagged
    if not same_tagged then
      throw <| IO.userError s!"The submission does not contain the same tagged declarations as the target:\n {targets_tagged}\n [vs]\n {submitted_tagged}"
    IO.println "Checked same tagged declarations"

    let correct? (cs : CompilationStep) (is_tagged: Bool) : Bool :=
      if is_tagged then
        cs.msgs.all (fun m => m.severity != MessageSeverity.error)
      else
        cs.msgs.all (fun m => m.severity != MessageSeverity.error && m.severity != MessageSeverity.warning)
      -- i.e. tagged items can have warnings, untagged items cannot
    let all_targets_correct := targetData.all (fun (cs, _, is_tagged) => correct? cs is_tagged)
    let all_submitted_correct := submittedData.all (fun (cs, _, is_tagged) => correct? cs is_tagged)
    if not (all_targets_correct && all_submitted_correct) then
      throw <| IO.userError s!"The submission or target contains errors or warnings outside of the tagged items."
    IO.println "Checked no errors/warnings outside tagged items"

    -- all rules passed, now run safeVerify
    let targetInfos ← replayFileDirect env_targ
    -- let task ← IO.asTask (replayFileDirect env_sub targetInfos)
    -- if let .error e:=task.get then
    --   IO.eprintln s!"found a problem in submission."
    --   throw e
    let _ ← replayFileDirect env_sub targetInfos (targetData.filterMap (fun (_,ci,is_tagged) => if is_tagged then some ci.name else none))

    IO.println s!"Finished with no errors; building file descriptor."

    let toDeclDescriptor (item : (CompilationStep × ConstantInfo × Bool)) : IO DeclarationDescriptor := do
      let (cs, ci, is_tagged) := item
      let mut msgs := #[]
      for m in cs.msgs do
        let st ← m.data.toString
        msgs := msgs.push (m.severity, st)
      return  {
        ci := ci,
        contents := cs.src,
        context := (Substring.mk cs.src.str 0 cs.src.startPos),
        msgs? := some msgs.toList,
        target? := is_tagged,
        sourceFile? := source_file
      }

    let target_final : List DeclarationDescriptor ← targetData.mapM toDeclDescriptor
    let submitted_final : List DeclarationDescriptor ← submittedData.mapM toDeclDescriptor

    let outputs := if diff? then
      let diffs := submitted_final.filter (fun d => not (target_final.contains d))
      diffs
    else
      submitted_final

    return outputs
    -- throw <| IO.userError s!"safeVerify not yet implemented"

  | _ =>
    throw <| IO.userError s!"Could not get final environment from submission/target."


unsafe def getTargetsCLI (args : Cli.Parsed) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%

  let submission := args.flag! "submission" |>.as! String
  let target := args.flag! "target" |>.as! String

  let target? := if target == "" then none else some target

  let savePath := args.flag! "save" |>.as! String
  let save? := if savePath == "" then none else some savePath

  let diff := args.flag! "diff" |>.as! String
  let diff? := if diff != "true" then false else true

  try
    let targetContent? ← target?.mapM (fun t => getFileOrModuleContents t)

    let (targetContent?, _, target_fp?) := match targetContent? with
      | some (c, m, fp) => (some c, some m, some fp)
      | none => (none, none, none)

    match submission.toNat? with
    | some n =>
      -- buffer mode
      let payload_raw : ByteArray ← (← getStdin).read n.toUSize
      let payload_str? := String.fromUTF8? payload_raw
      match payload_str? with
      | none =>
        IO.eprintln "Error: could not decode stdin as UTF-8"
      | some payload => do
        let descriptor ← getTargets' payload targetContent? diff? target_fp?
        let json := ToJson.toJson descriptor.toArray
        if save?.isSome then
          let _ ← IO.FS.writeFile save?.get! (json.pretty)
          IO.println s!"Wrote file descriptor to {save?.get!}"
        else
          IO.println "<DESCRIPTOR>"
          IO.println json.pretty
          IO.println "</DESCRIPTOR>"

    | none =>
      -- file mode
      let (contents,_, fp) ← getFileOrModuleContents submission
      let descriptor ← getTargets' contents targetContent? diff? (some fp)
      let json := ToJson.toJson descriptor
      if save?.isSome then
          let _ ← IO.FS.writeFile save?.get! (json.pretty)
          IO.println s!"Wrote file descriptor to {save?.get!}"
      else
        IO.println "<DESCRIPTOR>"
        IO.println json.pretty
        IO.println "</DESCRIPTOR>"

      IO.println "Finished with no errors."
    return 0
  catch e =>
    IO.eprintln s!"Error: {e}"
    return 1



/-

File mode:
--submission <file>
--target <file> (optional)

buffer mode:
--submission <bytes in buffer>
--target <file> (optional)



additional flags:

--save <file> (optional) : if provided, save the file descriptor to this file as json to specified path.
--diff : if provided (and target file is specified), output the diff of the file descriptor instead of the full thing.


-/

unsafe def getTargets : Cmd := `[Cli|
  get_targets VIA getTargetsCLI; ["0.0.1"]
"Get targets from a string."

  FLAGS:
    submission : String; "In file mode, the submission module name. In buffer mode, the number of bytes to read from stdin."
    target : String; "The target module name. Optional; if not provided, then target=submission is assumed."

    save : String; "If provided, save the file descriptor to this file as json to specified path. Default is no save."
    diff : String; "If provided (and target file is specified), output the diff of the file descriptor instead of the full thing. Default is false."



  EXTENSIONS:
    defaultValues! #[("target", ""), ("save", ""), ("diff", "false")]
]


unsafe def main (args : List String) : IO UInt32 :=
  getTargets.validate args
