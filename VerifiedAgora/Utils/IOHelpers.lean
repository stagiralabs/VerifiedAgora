import Cli.Extensions
import VerifiedAgora.Utils.Frontend

open Lean IO

def getFileOrModuleContents (name : String) : IO (String × Name × System.FilePath) := do
  let modName := name.toName
  try
    let contents ← Lean.Elab.IO.moduleSource modName
    let filePath ← Lean.Elab.IO.findLean modName
    pure (contents, modName, filePath)
  catch e =>
    try
      let contents ← IO.FS.readFile name
      let moduleName ← moduleNameOfFileName (System.FilePath.mk name) none
      let filePath := System.FilePath.mk name
      pure (contents, moduleName, filePath)
    catch e2 =>
      throw <| IO.userError s!"Could not find module or file: {name}:\n  as module: {e}\n  as file: {e2}"


def getFileOrModuleName (name : String) : IO (Name × System.FilePath × Bool) := do
  let modName := name.toName
  try
    let filePath ← Lean.Elab.IO.findLean modName
    pure (modName, filePath, false)
  catch e =>
    try
      let filePath := System.FilePath.mk name
      let moduleName ← moduleNameOfFileName (filePath) none
      let ex ← filePath.pathExists
      pure (moduleName, filePath, ex)
    catch e2 =>
      throw <| IO.userError s!"Could not find module or file: {name}:\n  as module: {e}\n  as file: {e2}"


def parseBoolFlag (flagName : String) (raw : String) : IO Bool := do
  match raw.trim.toLower with
  | "true" => pure true
  | "false" => pure false
  | _ => throw <| IO.userError s!"Invalid boolean value for --{flagName}: \"{raw}\". Expected true or false."

def descriptorCachePathForModule (mod : Name) : IO System.FilePath := do
  pure ((← findOLean mod).withExtension "descriptor")

def systemTimeLe (a b : IO.FS.SystemTime) : Bool :=
  a.sec < b.sec || (a.sec == b.sec && a.nsec <= b.nsec)

def isDescriptorCacheFresh (mod : Name) (descriptorPath : System.FilePath) : IO Bool := do
  if !(← descriptorPath.pathExists) then
    return false
  try
    let descriptorMeta ← descriptorPath.metadata
    let sourceMeta ← (← Lean.Elab.IO.findLean mod).metadata
    let oleanMeta ← (← findOLean mod).metadata
    let t := descriptorMeta.modified
    pure (systemTimeLe sourceMeta.modified t && systemTimeLe oleanMeta.modified t)
  catch _ =>
    pure false
