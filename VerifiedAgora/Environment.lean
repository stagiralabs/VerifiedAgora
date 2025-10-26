import Lean.Elab.Frontend
import Lean.Util.CollectAxioms
import Lean.Environment
import Batteries.Tactic.OpenPrivate


open Lean Elab



def init : IO Unit := do
  initSearchPath (← getLibDir (← findSysroot))
  unsafe Lean.enableInitializersExecution


def importModulesPartial (imports : Array Import)
    (plugins : Array System.FilePath := #[])
    (level := OLeanLevel.private) : IO ImportState :=
  withImporting do
    for imp in imports do
      if imp.module matches .anonymous then
        throw <| IO.userError "import failed, trying to import module with anonymous name"
    plugins.forM Lean.loadPlugin
    let (_, s) ← importModulesCore (forceImportAll := level == .private) imports |>.run
    pure s

def finalizeEnv (imports : Array Import) (opts : Options)
    (trustLevel : UInt32 := 0) (state : ImportState)
    (leakEnv := false) (loadExts := false) (level := OLeanLevel.private) : IO Environment := do
    withImporting do
      finalizeImport (leakEnv := leakEnv) (loadExts := loadExts) (level := level) (state) imports opts trustLevel

def addImportedModulesCore (imports : Array Import) (forceImportAll := true) (prevState : ImportState) :
    ImportStateM Unit := do
    set prevState
    importModulesCore (forceImportAll := forceImportAll) imports




open private ImportState.moduleNames from Lean.Environment
open private ImportState.moduleNameMap from Lean.Environment
open private ImportedModule.parts from Lean.Environment
/- Removes exactly the imported modules specified by <imports>, changing the ImportState accordingly -/
unsafe def removeImportedModulesCore (imports : Array Import) (prevState : ImportState) :
    ImportStateM Unit := do
    set prevState
    let toRemove := imports.map (fun imp => imp.module)

    modify fun s =>
      let names := ImportState.moduleNames s
      let map := ImportState.moduleNameMap s
      let out := { s with
        moduleNameMap := map.filter (fun k _ => !toRemove.contains k),
        moduleNames := names.filter (fun mod => !toRemove.contains mod) }
      out

    -- Free unused memory regions regions associated to removed modules
    let to_free := (ImportState.moduleNameMap (← get)).filter (fun k _ => toRemove.contains k)
    for ⟨_, imp⟩ in to_free do
      for ⟨_, region⟩ in (ImportedModule.parts imp) do
        region.free


def addImportedModulesPartial (imports : Array Import)
    (prevState : ImportState)
    (forceImportAll := true) : IO ImportState := do
  withImporting do
    for imp in imports do
      if imp.module matches .anonymous then
        throw <| IO.userError "import failed, trying to import module with anonymous name"
    let (_, s) ← (addImportedModulesCore imports forceImportAll prevState).run
    pure s

unsafe def removeImportedModulesPartial (imports : Array Import)
    (prevState : ImportState) : IO ImportState := do
  withImporting do
    let (_, s) ← (removeImportedModulesCore imports prevState).run
    pure s



unsafe def test : IO Unit := do
  init
  let imports := #[
    { module := `VerifiedAgora.Test1 },
  ]
  let t1 := (← IO.monoMsNow)
  let mut state ← importModulesPartial imports
  -- IO.println s!"Imported modules: {state.moduleNames}"
  let t2 := (← IO.monoMsNow)
  IO.println s!"Imported first in {t2 - t1} ms."

  -- let state2 ← importModulesPartial #[{ module := `Lean.Util.CollectAxioms}]
  state ← addImportedModulesPartial #[{ module := `VerifiedAgora.Test2 }] state
  let t3 := (← IO.monoMsNow)
  IO.println s!"Imported second in {t3 - t2} ms."

  state ← removeImportedModulesPartial #[{ module := `VerifiedAgora.Test1 }] state

  let env ← finalizeEnv imports Options.empty 0 state
  let t4 := (← IO.monoMsNow)
  IO.println s!"Finalized in {t4 - t3} ms."

  IO.println s!"Environment has {env.constants.toList.length} constants."
  -- IO.println s!"env 1 present: {env.constants.contains `test1}"
  -- IO.println s!"env 2 present: {env.constants.contains `test2}"

-- #eval test

def getAllDependencies (imports : Array Import) : Array Import := imports -- TODO: implement


structure ImportClosure where
  toplevel : Array Import -- Should be sorted
  state : ImportState
  removed : Array Import := #[]

instance : BEq Import where
  beq imp1 imp2 := imp1.module == imp2.module

instance : LT Import where
  lt imp1 imp2 := imp1.module.toString < imp2.module.toString

instance : Inhabited ImportClosure where
  default := { toplevel := #[], state := {} }

def makeImportClosure (imports : Array Import) (prevClosure : Option ImportClosure) : IO ImportClosure := do
  match prevClosure with
  | none => -- Fresh environment
    let state ← importModulesPartial imports
    return { toplevel := imports.insertionSort (fun imp1 imp2 => imp1.module.toString < imp2.module.toString), state := state } -- TODO: dependencies of imports
  | some prev =>
    let addedImports := imports.filter (fun imp => !prev.toplevel.contains imp)
    let removedImports := prev.toplevel.filter (fun imp => !imports.contains imp)

    let mut state := prev.state
    let mut toplevel := prev.toplevel
    let mut removed := prev.removed

    -- If we need to add more imports, run through ImportM to add them, and modify toplevel accordingly
    if !addedImports.isEmpty then
      state ← addImportedModulesPartial addedImports state
      toplevel := (toplevel ++ addedImports).insertionSort (fun imp1 imp2 => imp1.module.toString < imp2.module.toString)

    -- If we need to remove imports, keep track of all dependencies that they alone require; these will be removed manually from the environment b/c I can't figure out how to do this with ImportM yet
    if !removedImports.isEmpty then
      toplevel := toplevel.filter (fun imp => !removedImports.contains imp)
      let remove_tree := getAllDependencies removedImports |>.filter (fun imp => !toplevel.contains imp)
      removed := (removed ++ remove_tree).insertionSort (fun imp1 imp2 => imp1.module.toString < imp2.module.toString)

    return { toplevel := toplevel, state := state, removed := removed }




def default_ : IO (Environment × Option ImportClosure) := do
  let env ← mkEmptyEnvironment
  return (env, none)

unsafe def makeEnvFor (input : String) (curr : IO (Environment × Option ImportClosure) := default_) : IO (Environment × Option ImportClosure × String) := do
  let ⟨imports, pos, msgs⟩ ← parseImports input
  for msg in msgs.toList do
    if msg.severity == MessageSeverity.error then
      throw <| IO.userError s!"failed to parse imports: {← msg.toString}"

  let pos := FileMap.ofString input |>.ofPosition pos
  let rest := input.extract pos input.endPos

  let ⟨old_env, old_closure⟩ ← curr

  -- IO.println s!"Imports to process: {imports.map (fun imp => imp.module.toString)}"
  if old_env.imports.foldl (fun ok x => ok && imports.contains x) true && imports.foldl (fun ok x => ok && old_env.imports.contains x) true then -- Shortcut if the environment is exactly the same; we don't need to rebuild it
    IO.println s!"Reusing environment with {old_env.constants.toList.length} constants."
    return (old_env, old_closure, rest)
  old_env.freeRegions -- If not, free the old environment

  -- Otherwise, modify the closure as little as possible to account for the changed imports
  let closure ← makeImportClosure imports old_closure
  let mut env ← finalizeEnv imports Options.empty 0 closure.state (leakEnv := false) (loadExts := true)
  -- let env ← importModules imports Options.empty (leakEnv := false) (loadExts := true)


  IO.println s!"Made environment with {env.constants.toList.length} constants."

  return (env, closure, rest)

-- #check Lean.Meta.realizeConst

-- unsafe def makeEnvForOld (input : String) (curr : IO Environment := mkEmptyEnvironment) : IO (Environment × String) := do
--   let ⟨imports, pos, msgs⟩ ← parseImports input
--   if !msgs.toList.isEmpty then
--     throw <| IO.userError s!"failed to parse imports"

--   let pos := FileMap.ofString input |>.ofPosition pos
--   let rest := input.extract pos input.endPos

--   let old_env ← curr
--   if (old_env.imports.map (fun x => x.module.toString) |>.insertionSort) = (imports.map (fun x => x.module.toString) |>.insertionSort) then
--     return (old_env, rest)
--   old_env.freeRegions

--   let env ← importModules imports Options.empty (leakEnv := false) (loadExts := true)

--   return (env, rest)



unsafe def testing : IO Unit := do
  let (env, closure, rest) ← makeEnvFor "import VerifiedAgora.Test1\ndef test3 : Nat := test1"
  IO.println s!"Rest of input: {rest}"
  IO.println s!"Environment has {env.constants.toList.length} constants."
  IO.println s!"Has test1: {env.constants.contains `test1}"
  IO.println s!"Has test2: {env.constants.contains `test2}"

  let (env2, closure2, rest2) ← makeEnvFor "import VerifiedAgora.Test2\ndef test4 : Nat := test2" (pure (env, closure))
  IO.println s!"Rest of input: {rest2}"
  IO.println s!"Environment has {env2.constants.toList.length} constants."
  IO.println s!"Has test2: {env2.constants.contains `test2}"
  IO.println s!"Has test1: {env2.constants.contains `test1}"
  IO.println s!"Removed imports: {closure2.get!.removed.map (fun imp => imp.module.toString)}"

-- #eval testing
