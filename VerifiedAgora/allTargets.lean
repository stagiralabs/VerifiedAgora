import Cli.Extensions
import VerifiedAgora.tagger
import VerifiedAgora.Frontend
import VerifiedAgora.TacticInvocation
import VerifiedAgora.Utils
open Lean Core Elab IO Meta Term Command Tactic Cli


def toDeclDescriptor (ci : ConstantInfo) (source : FileMap) (range : DeclarationRange)  (target? : Bool) (sourceFile? : Option System.FilePath) : DeclarationDescriptor :=
    {
      ci := ci,
      contents := Substring.mk source.source (source.ofPosition range.pos) (source.ofPosition range.endPos),
      target? := target?,
      sourceFile? := sourceFile?
      context := Substring.mk source.source ⟨0⟩ (source.ofPosition range.pos),
      msgs? := none
    }
/-- Imports the entire project (in the way `lake build` would) and gets all tagged declarations. Requires project to be `lake build`-ed first. -/
unsafe def getAllTargetsInProject (mod : Name) : IO FileDescriptor := do
  -- let moduleName ← moduleNameOfFileName importFile none

  let ⟨env, msgs, _⟩  ← IO.processInput s!"import {mod}"
  for msg in msgs do
    if msg.severity == MessageSeverity.error then
      throw <| IO.userError s!"Build failed: {← msg.data.toString}"

  let tagged_decls := env.constants.fold (fun acc k ci => if TagAttribute.hasTag targetAttribute env k then ci::acc else acc) []
  let mut out : List DeclarationDescriptor := []
  for decl in tagged_decls do
    let modidx := env.getModuleIdxFor? decl.name
    let mod := env.header.moduleNames.get! modidx.get!
    let fp ← findLean mod
    let source ← IO.FS.readFile fp
    let location := declRangeExt.find? (env) decl.name |>.getD ⟨default, default⟩


    out := (toDeclDescriptor decl (FileMap.ofString source) location.range true (some fp)) :: out

  return out


unsafe def getAllTargetsCLI (args : Cli.Parsed) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%

  let importFiles := (args.flag! "importFiles" |>.as! String).splitOn ","|>.map (fun s => s.trim)


  let importPaths ← importFiles.mapM getFileOrModuleContents
  let mut descriptors : List DeclarationDescriptor := []
  for (_, mod, _) in importPaths do
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
]


unsafe def main (args : List String) : IO UInt32 :=
  getAllTargets.validate args
