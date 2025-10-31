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
open private ImportedModule from Lean.Environment
open private ImportedModule.mk from Lean.Environment
open private ImportedModule.parts from Lean.Environment
/- Removes exactly the imported modules specified by <imports>, changing the ImportState accordingly -/
unsafe def removeImportedModulesCore (imports : Array Import) (prevState : ImportState) : ImportStateM Unit := do
    set prevState
    let toRemove := imports.map (fun imp => imp.module)

    let t1 ← IO.monoMsNow
    modify fun s =>
      let names := ImportState.moduleNames s
      let map := ImportState.moduleNameMap s
      let out := { s with
        moduleNameMap := map.filter (fun k _ => !toRemove.contains k),
        moduleNames := names.filter (fun mod => !toRemove.contains mod) }
      out
    let t2 ← IO.monoMsNow
    IO.println s!"Modified ImportState in {t2 - t1} ms."

    let t3 ← IO.monoMsNow
    -- Free unused memory regions regions associated to removed modules
    let to_free := (ImportState.moduleNameMap (← get)).filter (fun k _ => toRemove.contains k)
    for ⟨_, imp⟩ in to_free do
      for ⟨_, region⟩ in (ImportedModule.parts imp) do
        region.free
    let t4 ← IO.monoMsNow
    IO.println s!"Freed regions in {t4 - t3} ms."


def addImportedModulesPartial (imports : Array Import)
    (prevState : ImportState)
    (forceImportAll := true) : IO ImportState := do
  withImporting do
    for imp in imports do
      if imp.module matches .anonymous then
        throw <| IO.userError "import failed, trying to import module with anonymous name"
    let (_, s) ← (addImportedModulesCore imports forceImportAll prevState).run
    pure s

unsafe def removeImportedModulesPartial (toRemove : Array Import)
    (prevState : ImportState) : IO ImportState := do
  withImporting do
    let (_, s) ← (removeImportedModulesCore toRemove prevState).run
    pure s

instance : Inhabited ImportedModule where
  default := ImportedModule.mk ({ module := `anonymous}) #[]
instance : BEq Import where
  beq m1 m2 := m1.module == m2.module

/-- Given an array of toplevel imports, remove all the imported modules not directly or indirectly depended on by them -/
unsafe def pruneImportedModulesPartial
    (toKeep : Array Import)
    (prevState : ImportState) : IO ImportState := do
  let t1 ← IO.monoMsNow

  let out ← withImporting do
    let t1 ← IO.monoMsNow
    let rec go : Import → Array Import → Array Import := fun n current =>
      match ImportState.moduleNameMap prevState |>.get? n.module with
      | none => current
      | some mod =>
        let imports := ImportedModule.parts mod |>.map (fun ⟨data, _⟩ => data.imports) |>.flatten |>.filter (fun imp => !current.contains imp)
        imports.foldl (fun acc imp => go imp acc) (current.push n)
    let tree := toKeep.foldl (fun acc imp => go imp acc) #[]
    let all := ImportState.moduleNames prevState |>.map (fun n => { module := n})
    let toRemove := all.filter (fun imp => !tree.contains imp)

    let t2 ← IO.monoMsNow
    IO.println s!"Computed modules to remove in {t2 - t1} ms."

    -- pure prevState
    if toRemove.isEmpty then
      return prevState
    else

      let t3 ← IO.monoMsNow
      let (_, s) ← (removeImportedModulesCore toRemove prevState).run
      IO.println s!"{ImportState.moduleNames s}"
      let t4 ← IO.monoMsNow
      IO.println s!"Core fxn runs in {t4 - t3} ms"
      return s

  let t2 ← IO.monoMsNow
  IO.println s!"PruneImportedModulesPartial total time: {t2 - t1} ms."
  return out




structure ImportClosure where
  toplevel : Array Import -- Should be sorted
  state : ImportState

instance : BEq Import where
  beq imp1 imp2 := imp1.module == imp2.module

instance : LT Import where
  lt imp1 imp2 := imp1.module.toString < imp2.module.toString

instance : Inhabited ImportClosure where
  default := { toplevel := #[], state := {} }

unsafe def makeImportClosure (imports : Array Import) (prevClosure : Option ImportClosure) : IO ImportClosure := do
  match prevClosure with
  | none => -- Fresh environment
    let state ← importModulesPartial imports
    return { toplevel := imports.insertionSort (fun imp1 imp2 => imp1.module.toString < imp2.module.toString), state := state } -- TODO: dependencies of imports
  | some prev =>
    let addedImports := imports.filter (fun imp => !prev.toplevel.contains imp)
    let removedImports := prev.toplevel.filter (fun imp => !imports.contains imp)

    let mut state := prev.state
    let mut toplevel := prev.toplevel

    -- If we need to add more imports, run through ImportM to add them, and modify toplevel accordingly
    if !addedImports.isEmpty then
      state ← addImportedModulesPartial addedImports state
      toplevel := (toplevel ++ addedImports).insertionSort (fun imp1 imp2 => imp1.module.toString < imp2.module.toString)

    -- If we need to remove imports, keep track of all dependencies that they alone require; these will be removed manually from the environment b/c I can't figure out how to do this with ImportM yet
    if !removedImports.isEmpty then
      -- IO.println s!"Removing imports: {removedImports.map (fun imp => imp.module.toString)}"
      toplevel := toplevel.filter (fun imp => !removedImports.contains imp)
      let t1 ← IO.monoMsNow
      state ← pruneImportedModulesPartial toplevel state
      let t2 ← IO.monoMsNow
      IO.println s!"Pruned environment took {t2 - t1} ms in total."

    return { toplevel := toplevel, state := state }




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
  -- old_env.freeRegions -- If not, free the old environment
  -- For some reason causes issues when running using #eval

  -- Otherwise, modify the closure as little as possible to account for the changed imports
  let closure ← makeImportClosure imports old_closure

  let mut env ← finalizeEnv imports Options.empty 0 closure.state (leakEnv := false) (loadExts := true)

  IO.println s!"Made environment with {env.constants.toList.length} constants."

  return (env, closure, rest)





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
  let t1 ← IO.monoMsNow
  let (env, closure, rest) ← makeEnvFor "import VerifiedAgora.Test1\ndef test3 : Nat := test1"
  let t2 ← IO.monoMsNow
  IO.println s!"Built environment in {t2 - t1} ms."
  IO.println s!"Rest of input: {rest}"
  IO.println s!"Environment has {env.constants.toList.length} constants."
  IO.println s!"Has test1: {env.constants.contains `test1}"
  IO.println s!"Has test2: {env.constants.contains `test2}"

  let t3 ← IO.monoMsNow
  let (env2, closure2, rest2) ← makeEnvFor "def test4 : Nat := test2" (pure (env, closure))


  -- let (env2, closure2, rest2) ← makeEnvFor "import VerifiedAgora.Test1\nimport VerifiedAgora.Test2\ndef test4 : Nat := test2" (pure (env, closure))
  -- let (env2, closure2, rest2) ← makeEnvFor "import VerifiedAgora.Test1\nimport VerifiedAgora.Test2\ndef test4 : Nat := test2"

  let t4 ← IO.monoMsNow
  IO.println s!"Rebuilt environment in {t4 - t3} ms."
  IO.println s!"Rest of input: {rest2}"
  IO.println s!"Environment has {env2.constants.toList.length} constants."
  IO.println s!"Has test1: {env2.constants.contains `test1}"
  IO.println s!"Has test2: {env2.constants.contains `test2}"

-- #eval testing
