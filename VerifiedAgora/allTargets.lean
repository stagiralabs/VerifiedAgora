import Cli.Extensions
import VerifiedAgora.tagger
import VerifiedAgora.Frontend
import VerifiedAgora.TacticInvocation
open Lean Core Elab IO Meta Term Command Tactic Cli


/-- Examines the lakefile to determine the root module name -/
def getRootModule (lakefile : System.FilePath) : IO Name := do
  if !(← lakefile.pathExists) then
    throw <| IO.userError s!"Lakefile not found at {lakefile}"
  let contents ← IO.FS.readFile lakefile
  match lakefile.extension with
  | some "lean" =>
    let lines := contents.splitOn "\n" |>.filter (fun s => s.startsWith "package")
    match lines.head? with
    | none => throw <| IO.userError s!"Could not find package declaration in lakefile.lean"
    | some line =>
      let parts := line.splitOn " "
      if parts.length < 2 then
        throw <| IO.userError s!"Could not parse package declaration in lakefile.lean: {line}"
      let pkgName := parts[1]!.trim
      return pkgName.toName
  | some "toml" =>
    let lines := contents.splitOn "\n"
    let mut next := false
    for line in lines do
      if line.trim == "[[package]]" then
        next := true
      else if next && line.trim.startsWith "name =" then
        let parts := line.splitOn "="
        if parts.length < 2 then
          throw <| IO.userError s!"Could not parse package name in lakefile.toml: {line}"
        let pkgName := parts[1]!.replace "\"" "" |>.trim
        return pkgName.toName
    throw <| IO.userError s!"Could not find package declaration in lakefile.toml"
  | _ =>
    throw <| IO.userError s!"Unknown lakefile extension: {lakefile.extension}"


def toJson (ci : ConstantInfo) (source : FileMap) (range : DeclarationRange) (msgs : List (MessageSeverity × String)) (target? : Bool) : Json :=

    Json.mkObj [
    ("name", Json.str ci.name.toString),
    ("contents", Json.str <| (Substring.mk source.source (source.ofPosition range.pos) (source.ofPosition range.endPos)).toString),
    ("isTarget", Json.bool target?),
    ("context", Json.str <| (Substring.mk source.source ⟨0⟩ (source.ofPosition range.pos)).toString),
    ("msgs", Json.arr <| msgs.toArray.map (fun (sev, data) => Json.mkObj [("severity", (ToJson.toJson sev)), ("data", Json.str data)]) )
  ]


/-- Imports the entire project (in the way `lake build` would) and gets all tagged declarations. Requires project to be `lake build`-ed first. -/
unsafe def getAllTargetsInProject (lakefile : System.FilePath) : IO (List Json) := do
  let rootFile ← getRootModule lakefile
  let ⟨env, msgs, _⟩  ← IO.processInput (← moduleSource rootFile)
  for msg in msgs do
    if msg.severity == MessageSeverity.error then
      throw <| IO.userError s!"Build failed: {rootFile}: {← msg.data.toString}"

  let tagged_decls := env.constants.fold (fun acc k ci => if TagAttribute.hasTag targetAttribute env k then ci::acc else acc) []
  let mut out : List Json := []
  for decl in tagged_decls do
    let modidx := env.getModuleIdxFor? decl.name
    let mod := env.header.moduleNames.get! modidx.get!
    let source ← IO.FS.readFile (← findLean mod)
    let location := declRangeExt.find? (env) decl.name |>.getD ⟨default, default⟩

    out := (toJson decl (FileMap.ofString source) location.range [] true) :: out

  return out


unsafe def getAllTargetsCLI (args : Cli.Parsed) : IO UInt32 := do
  let lakefile := System.FilePath.mk (args.flag! "lakefile" |>.as! String)
  let targets ← getAllTargetsInProject lakefile
  for json in targets do
    IO.println "<DESCRIPTOR>"
    IO.println json.pretty
    IO.println "</DESCRIPTOR>"
  return 0



unsafe def getAllTargets : Cmd := `[Cli|
  get_all_targets VIA getAllTargetsCLI; ["0.0.1"]
"Get targets from a string."

  FLAGS:
    lakefile : String; "Path to the lakefile."
]


unsafe def main (args : List String) : IO UInt32 :=
  getAllTargets.validate args
