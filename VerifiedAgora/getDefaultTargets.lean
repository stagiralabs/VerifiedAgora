import Lake.CLI.Main
import Lean

open Lake Lean

def loadLakeWorkspace : IO Workspace := do
  let (elan?, lean?, lake?) ← findInstall?
  let cfg ← MonadError.runEIO <|
    mkLoadConfig { elanInstall? := elan?, leanInstall? := lean?, lakeInstall? := lake? }
  MonadError.runEIO <| MainM.runLoggerIO (loadWorkspace cfg)
def resolveDefaultRootModules : IO (Array Name) := do
  let ws ← loadLakeWorkspace
  let specs ←
    match resolveDefaultPackageTarget ws ws.root with
    | Except.error e => throw <| IO.userError s!"[Error] Error resolving default package target: {e}"
    | Except.ok ts   => pure ts

  let mods :=
    specs.flatMap (fun t =>
      match t.info with
      | BuildInfo.libraryFacet lib _ => lib.roots
      | BuildInfo.leanExe exe        => #[exe.config.root]
      | _                            => #[])

  return mods





unsafe def main (_args : List String) : IO UInt32 := do
  let mods ← resolveDefaultRootModules
  let js := Json.arr <| mods.map (fun n => Json.str n.toString)
  IO.println js.pretty
  return 0
