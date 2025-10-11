import Cli.Extensions
import VerifiedAgora.tagger
import VerifiedAgora.Frontend
import VerifiedAgora.TacticInvocation
open Lean Meta Core

/-
  From Batteries.Lean.TagAttribute
-/

/-- Get the list of declarations tagged with the tag attribute `attr`. -/
def Lean.TagAttribute.getDecls (attr : TagAttribute) (env : Environment) : Array Name :=
  core <| attr.ext.toEnvExtension.getState env
where
  /-- Implementation of `TagAttribute.getDecls`. -/
  core (st : PersistentEnvExtensionState Name NameSet) : Array Name := Id.run do
    let mut decls := st.state.toArray
    for ds in st.importedEntries do
      decls := decls ++ ds
    decls




def Lean.ConstantInfo.kind : ConstantInfo → String
  | .axiomInfo  _ => "axiom"
  | .defnInfo   _ => "def"
  | .thmInfo    _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo   _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo   _ => "constructor"
  | .recInfo    _ => "recursor"

def AllowedAxioms := [`propext, `Quot.sound, `Classical.choice]
def TargetsAllowedAxioms := AllowedAxioms ++ [`sorryAx]

def checkAxioms (env: Environment) (n: Name) (allow_sorry? : Bool := false): IO Unit:= do
  let (_,s):=(CollectAxioms.collect n).run env |>.run {}
  for a in s.axioms do
    let ax := if allow_sorry? then TargetsAllowedAxioms else AllowedAxioms
    if a ∉ ax then
      throw <| IO.userError s!"{a} is not in the allowed set of standard axioms"

structure Info where
  name: Name
  constInfo: ConstantInfo
  axioms: Array Name
  --nonComputable: Bool
  deriving Inhabited

/-
From Lean.Environment
Check if two theorems have the same type and name
-/
def equivThm (cinfo₁ cinfo₂ : ConstantInfo) : Bool := Id.run do
  let .thmInfo tval₁ := cinfo₁ | false
  let .thmInfo tval₂ := cinfo₂ | false
  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all

/-
Check if two definitions have the same type and name.
If checkVal is true, then also check their values are the same
-/
def equivDefn (ctarget cnew : ConstantInfo)(checkVal:Bool:=false) : Bool := Id.run do
  let .defnInfo tval₁ := ctarget | false
  let .defnInfo tval₂ := cnew | false

  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.safety == tval₂.safety
    && (if checkVal then tval₁.value==tval₂.value else true)

open Lean Core Elab IO Meta Term Command Tactic Cli



-- structure ExampleData extends TheoremData where
--   improved : String := ""
--   deriving ToJson, FromJson


-- def groupByTagName (targetData : List (CompilationStep × ConstantInfo × Name × Version))
--   : IO (Array (Name × Array (CompilationStep × ConstantInfo × Version))) := do

--   let mut grouped : Array (Name × Array (CompilationStep × ConstantInfo × Version)) := #[]

--   for (cmd, ci, tagName, version) in targetData do
--     let existingGroup? := grouped.findIdx? (fun (name, _) => name == tagName)
--     match existingGroup? with
--     | some idx =>
--       let (name, existing) := grouped[idx]!

--       -- push only if a singleton containing unoptimized or optimized.
--       let version_subarray := existing.filterMap (fun (_, _, v) => if v == Version.unoptimized || v == Version.optimized then some v else none)
--       if version_subarray.size == 1 && (
--           (version == .unoptimized && version_subarray[0]! == .optimized)
--         || (version == .optimized && version_subarray[0]! == .unoptimized)
--         ) then
--         grouped := grouped.set! idx (name, existing.push (cmd, ci, version))
--       else
--         IO.println s!"Unexpected versioning in {tagName}: {version} with existing versions: {version_subarray}, taking only first"

--     | none =>
--       grouped := grouped.push (tagName, #[(cmd, ci, version)])
--   return grouped



structure DeclarationDescriptor where
  cs : CompilationStep
  ci : ConstantInfo
  msgs : List (MessageSeverity × String)
  target? : Bool


instance: BEq DeclarationDescriptor where
  beq d1 d2 :=
    d1.ci.name == d2.ci.name &&
    d1.ci.type == d2.ci.type &&
    d1.ci.kind == d2.ci.kind &&
    d1.target? == d2.target? &&
    d1.msgs == d2.msgs &&
    d1.cs.src == d2.cs.src

instance : ToJson DeclarationDescriptor where
  toJson fd :=

  Json.mkObj [
    ("name", Json.str fd.ci.name.toString),
    ("contents", Json.str fd.cs.src.toString),
    ("isTarget", Json.bool fd.target?),
    ("context", Json.str ((⟨fd.cs.src.str, 0, fd.cs.src.startPos⟩ : Substring).toString)),
    ("kind", Json.str (fd.ci.kind)),
    ("msgs", Json.arr <| fd.msgs.toArray.map (fun (sev, data) => Json.mkObj [("severity", (ToJson.toJson sev)), ("data", Json.str data)]) )
  ]

instance : ToString DeclarationDescriptor where
  toString fd := ToJson.toJson fd |>.pretty

abbrev FileDescriptor := List DeclarationDescriptor




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


unsafe def getTargets (submitted : String) (target? : Option String := none) (diff? : Bool := False): IO FileDescriptor := do
  let target := target?.getD submitted

  let target_steps := Lean.Elab.IO.processInput' target
  let targets_cs := target_steps.bind fun c => (MLList.ofList c.diff).map fun i => (c, i)
  let targets_flat ← (onlyHuman (← targets_cs.force))

  let submitted_flat : List (CompilationStep × ConstantInfo) ← if target?.isNone then pure targets_flat else do
    let submitted_steps := Lean.Elab.IO.processInput' submitted
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
        cs := cs,
        ci := ci,
        msgs := msgs.toList,
        target? := is_tagged
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
    throw <| IO.userError s!"Could not get final environment from submission/target"






unsafe def getTargetsCLI (args : Cli.Parsed) : IO UInt32 := do
  let submission := args.flag! "submission" |>.as! String
  let target := args.flag! "target" |>.as! String

  let target? := if target == "" then none else some target

  let savePath := args.flag! "save" |>.as! String
  let save? := if savePath == "" then none else some savePath

  let diff := args.flag! "diff" |>.as! String
  let diff? := if diff != "true" then false else true


  let getFileOrModuleContents (name : String) : IO String := do
    --first attempt as module name
    let modName := name.toName
    try
      let contents? ← moduleSource modName
      return contents?
    catch _ =>
      try
        -- attempt as file name
        let contents? ← IO.FS.readFile name
        return contents?
      catch _ =>
        throw <| IO.userError s!"Could not find module or file: {name}"

  try
    let targetContent? ← target?.mapM (fun t => getFileOrModuleContents t)

    match submission.toNat? with
    | some n =>
      -- buffer mode
      let payload_raw : ByteArray ← (← getStdin).read n
      let payload_str? := String.fromUTF8? payload_raw
      match payload_str? with
      | none =>
        IO.eprintln "Error: could not decode stdin as UTF-8"
      | some payload => do
        let descriptor ← getTargets payload targetContent? diff?

        if save?.isSome then
          let json := Json.arr <| descriptor.toArray.map ToJson.toJson
          let _ ← IO.FS.writeFile save?.get! (json.pretty)
          IO.println s!"Wrote file descriptor to {save?.get!}"

    | none =>
      -- file mode
      let contents ← getFileOrModuleContents submission
      let descriptor ← getTargets contents targetContent? diff?

      if save?.isSome then
          let json := Json.arr <| descriptor.toArray.map ToJson.toJson
          let _ ← IO.FS.writeFile save?.get! (json.pretty)
          IO.println s!"Wrote file descriptor to {save?.get!}"

      -- IO.println "Finished with no errors."
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

unsafe def get_targets : Cmd := `[Cli|
  get_targets VIA getTargetsCLI; ["0.0.1"]
"Get targets from a string."

  FLAGS:
    submission : String; "In file mode, the submission module name. In buffer mode, the number of bytes to read from stdin."
    target : String; "The target module name. Optional; if not provided, then target=submission is assumed."

    save : String; "If provided, save the file descriptor to this file as json to specified path. Default is no save."
    diff : String; "If provided (and target file is specified), output the diff of the file descriptor instead of the full thing. Default is false."

  -- ARGS:
    -- n : Nat; "Bytes to read from stdin"
    -- replace_proof : String; "What to replace the proof with. Default is none"
  --   pythonCommand : String; "Path to python executable."
  --   rag_id : String; "ID for the rag directory, used to identify the source of the prompts in the database."
  --   k : Nat; "Number of RAG results to use for each prompt."

  EXTENSIONS:
    defaultValues! #[("target", ""), ("save", ""), ("diff", "false")]
]


unsafe def main (args : List String) : IO UInt32 :=
  get_targets.validate args
