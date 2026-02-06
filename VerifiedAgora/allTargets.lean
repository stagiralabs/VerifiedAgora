import Cli.Extensions
import VerifiedAgora.tagger
import VerifiedAgora.Frontend
import VerifiedAgora.TacticInvocation
import VerifiedAgora.Utils
open Lean Core Elab IO Meta Term Command Tactic Cli


def toDeclDescriptor (ci : ConstantInfo) (source : FileMap) (range : DeclarationRange)  (msgs? : Option (List (MessageSeverity × String))) (target? : Bool) (sourceFile? : Option System.FilePath) : DeclarationDescriptor :=
    {
      ci := ci,
      contents := Substring.mk source.source (source.ofPosition range.pos) (source.ofPosition range.endPos),
      target? := target?,
      sourceFile? := sourceFile?
      context := Substring.mk source.source ⟨0⟩ (source.ofPosition range.pos),
      msgs? := msgs?
    }



/-- Imports the entire project (in the way `lake build` would) and gets all tagged declarations. Requires project to be `lake build`-ed first. -/
unsafe def getAllTargetsInProject (mod : Name) : IO FileDescriptor := do
  -- let moduleName ← moduleNameOfFileName importFile none

  let m : Import := { module := mod }
  let env ← importModules #[m] {} 0

  let tagged_decls := env.constants.fold (fun acc k ci => if TagAttribute.hasTag targetAttribute env k then ci::acc else acc) []
  let mut out : List DeclarationDescriptor := []
  for decl in tagged_decls do
    let modidx := env.getModuleIdxFor? decl.name
    let mod := env.header.moduleNames.get! modidx.get!
    let fp ← findLean mod
    let source ← IO.FS.readFile fp
    let location := declRangeExt.find? (env) decl.name |>.getD ⟨default, default⟩

    let (_, _, syntheticMsgs) := axiomAudit env decl.name


    out := (toDeclDescriptor decl (FileMap.ofString source) location.range (some syntheticMsgs) true (some fp)) :: out

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
  searchPathRef.set compile_time_search_path%

  let importFiles := (args.flag! "importFiles" |>.as! String).trim

  let importMods : List Name ←
    if importFiles == "<default>" then
      getDefaultImportsViaLakeExe
    else
      (importFiles.splitOn "," |>.mapM (fun s => do
        let (_,mod,_) ← getFileOrModuleContents (s.trim)
        pure mod
        )
      )

  let mut descriptors : List DeclarationDescriptor := []
  for mod in importMods do
    let targets ← getAllTargetsInProject mod
    for decl in targets do
      descriptors := decl :: descriptors

  IO.println "<DESCRIPTOR>"
  IO.println (toJson descriptors.reverse).pretty
  IO.println "</DESCRIPTOR>"

  return 0




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
