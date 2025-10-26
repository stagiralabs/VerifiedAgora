import Lean.Elab.Frontend
import Lean.Util.CollectAxioms
import Lean.Environment
import Batteries.Tactic.OpenPrivate

open Lean Elab

def init : IO Unit := do
  initSearchPath (← getLibDir (← findSysroot))
  unsafe Lean.enableInitializersExecution


/-From Lean.Environment (I had to make some of the attributes non-private) -/

private structure ImportedModule2 extends Import where
  /-- All loaded incremental compacted regions. -/
  parts     : Array (ModuleData × CompactedRegion)

/-- The main module data that will eventually be used to construct the kernel environment. -/
private def ImportedModule2.mainModule? (self : ImportedModule2) : Option ModuleData := do
  let (baseMod, _) ← self.parts[0]?
  self.parts[if baseMod.isModule && self.importAll then 2 else 0]?.map (·.1)

structure ImportState2 where
  moduleNameMap : Std.HashMap Name ImportedModule2 := {}
  moduleNames   : Array Name := #[]

abbrev ImportStateM2 := StateRefT ImportState2 IO
@[inline] nonrec def ImportStateM2.run (x : ImportStateM2 α) (s : ImportState2 := {}) : IO (α × ImportState2) :=
  x.run s

partial def importModulesCore2 (imports : Array Import) (forceImportAll := true) :
    ImportStateM2 Unit := go
where go := do
  for i in imports do
    -- import private info if (transitively) used by a non-`module` on any import path, or with
    -- `import all` (non-transitively)
    let importAll := forceImportAll || i.importAll
    if let some mod := (← get).moduleNameMap[i.module]? then
      -- when module is already imported, bump `importPrivate`
      if importAll && !mod.importAll then
        modify fun s => { s with moduleNameMap := s.moduleNameMap.insert i.module { mod with
          importAll := true }}
        if forceImportAll then
          -- bump entire closure
          if let some mod := mod.mainModule? then
            importModulesCore2 (forceImportAll := true) mod.imports
      continue
    let mFile ← findOLean i.module
    unless (← mFile.pathExists) do
      throw <| IO.userError s!"object file '{mFile}' of module {i.module} does not exist"
    let mut fnames := #[mFile]
    -- opportunistically load all available parts in case `importPrivate` is upgraded by a later
    -- import
    -- TODO: use Lake data to retrieve ultimate import level immediately
    let sFile := OLeanLevel.server.adjustFileName mFile
    if (← sFile.pathExists) then
      fnames := fnames.push sFile
      let pFile := OLeanLevel.private.adjustFileName mFile
      if (← pFile.pathExists) then
        fnames := fnames.push pFile
    let parts ← readModuleDataParts fnames
    -- `imports` is identical for each part
    let some (baseMod, _) := parts[0]? | unreachable!
    -- exclude `private import`s from transitive importing, except through `import all`
    let imports := baseMod.imports.filter (·.isExported || importAll)
    importModulesCore2 (forceImportAll := forceImportAll || !baseMod.isModule) imports
    if baseMod.isModule && !forceImportAll then
      for i' in imports do
        if let some mod := (← get).moduleNameMap[i'.module]?.bind (·.mainModule?) then
          if !mod.isModule then
            throw <| IO.userError s!"cannot import non`-module` {i'.module} from `module` {i.module}"
    modify fun s => { s with
      moduleNameMap := s.moduleNameMap.insert i.module { i with importAll, parts }
      moduleNames := s.moduleNames.push i.module
    }

/-- The main module data that will eventually be used to construct the publically accessible constants. -/
private def ImportedModule.publicModule? (self : ImportedModule2) : Option ModuleData := do
  let (baseMod, _) ← self.parts[0]?
  return baseMod

/--
Returns `true` if `cinfo₁` and `cinfo₂` represent the same theorem/axiom, with `cinfo₁` potentially
being a richer representation; under the module system, a theorem may be weakened to an axiom when
exported. We allow different modules to prove the same theorem.

Motivation: We want to generate equational theorems on demand and potentially
in different files, and we want them to have non-private names.
We may add support for other kinds of definitions in the future. For now, theorems are
sufficient for our purposes.

We may have to revise this design decision and eagerly generate equational theorems when
we implement the module system.

Remark: we do not check whether the theorem `value` field match. This feature is useful and
ensures the proofs for equational theorems do not need to be identical. This decision
relies on the fact that theorem types are propositions, we have proof irrelevance,
and theorems are (mostly) opaque in Lean. For `Acc.rec`, we may unfold theorems
during type-checking, but we are assuming this is not an issue in practice,
and we are planning to address this issue in the future.
-/
private def subsumesInfo (cinfo₁ cinfo₂ : ConstantInfo) : Bool :=
  cinfo₁.name == cinfo₂.name &&
    cinfo₁.type == cinfo₂.type &&
    cinfo₁.levelParams == cinfo₂.levelParams &&
    match cinfo₁, cinfo₂ with
    | .thmInfo tval₁, .thmInfo tval₂ => tval₁.all == tval₂.all
    | .thmInfo tval₁, .axiomInfo aval₂ => tval₁.all == [aval₂.name] && !aval₂.isUnsafe
    | .axiomInfo aval₁, .axiomInfo aval₂ => aval₁.isUnsafe == aval₂.isUnsafe
    | _, _ => false

private def mkInitialExtensionStates : IO (Array EnvExtensionState) := EnvExtension.mkInitialExtStates

open private Lean.ImportedModule from Lean.Environment
open private Lean.ImportedModule.mk from Lean.Environment
open private Lean.ImportState.moduleNames from Lean.Environment
open private Lean.ImportState.moduleNameMap from Lean.Environment
#check Lean.ImportedModule

def toImportModule (m : ImportedModule2) : Lean.ImportedModule := Lean.ImportedModule.mk m.module m.parts

def toImportState (s : ImportState2) : ImportState := {
  moduleNameMap := s.moduleNameMap
  moduleNames := s.moduleNames
}


-- open private Lean.Kernel.Environment.mk from Lean.Environment
/--
Constructs environment from `importModulesCore` results.

See also `importModules` for parameter documentation.
-/
def finalizeImport (s : ImportState2) (imports : Array Import) (opts : Options) (trustLevel : UInt32 := 0)
    (leakEnv loadExts : Bool) (level := OLeanLevel.private) : IO Environment := do
  let isModule := level != .private
  let modules := s.moduleNames.filterMap (s.moduleNameMap[·]?)
  let moduleData ← modules.mapM fun mod => do
    let some data := mod.mainModule? |
      throw <| IO.userError s!"missing data file for module {mod.module}"
    return data
  let numPrivateConsts := moduleData.foldl (init := 0) fun numPrivateConsts data => Id.run do
    numPrivateConsts + data.constants.size + data.extraConstNames.size
  let numPublicConsts := modules.foldl (init := 0) fun numPublicConsts mod => Id.run do
    if !mod.isExported then numPublicConsts else
      let some data := mod.publicModule? | numPublicConsts
      numPublicConsts + data.constants.size
  let mut const2ModIdx : Std.HashMap Name ModuleIdx := Std.HashMap.emptyWithCapacity (capacity := numPrivateConsts + numPublicConsts)
  let mut privateConstantMap : Std.HashMap Name ConstantInfo := Std.HashMap.emptyWithCapacity (capacity := numPrivateConsts)
  let mut publicConstantMap : Std.HashMap Name ConstantInfo := Std.HashMap.emptyWithCapacity (capacity := numPublicConsts)
  for h : modIdx in [0:moduleData.size] do
    let data := moduleData[modIdx]
    for cname in data.constNames, cinfo in data.constants do
      match privateConstantMap.getThenInsertIfNew? cname cinfo with
      | (cinfoPrev?, constantMap') =>
        privateConstantMap := constantMap'
        if let some cinfoPrev := cinfoPrev? then
          -- Recall that the map has not been modified when `cinfoPrev? = some _`.
          if subsumesInfo cinfo cinfoPrev then
            privateConstantMap := privateConstantMap.insert cname cinfo
          else if !subsumesInfo cinfoPrev cinfo then
            -- throwAlreadyImported s const2ModIdx modIdx cname
            throw <| IO.userError s!"constant '{cname}' has been imported multiple times with different definitions"
      const2ModIdx := const2ModIdx.insertIfNew cname modIdx
    for cname in data.extraConstNames do
      const2ModIdx := const2ModIdx.insertIfNew cname modIdx

  if isModule then
    for mod in modules.filter (·.isExported) do
      let some data := mod.publicModule? | continue
      for cname in data.constNames, cinfo in data.constants do
        match publicConstantMap.getThenInsertIfNew? cname cinfo with
        | (cinfoPrev?, constantMap') =>
          publicConstantMap := constantMap'
          if let some cinfoPrev := cinfoPrev? then
            if subsumesInfo cinfo cinfoPrev then
              publicConstantMap := publicConstantMap.insert cname cinfo
            -- no need to check for duplicates again, `privateConstMap` should be a superset

  let exts ← mkInitialExtensionStates
  let privateConstants : ConstMap := SMap.fromHashMap privateConstantMap false
  let privateBase : Kernel.Environment := Kernel.Environment.mk {
    const2ModIdx, constants := privateConstants
    quotInit        := !imports.isEmpty -- We assume `Init.Prelude` initializes quotient module
    extraConstNames := {}
    extensions      := exts
    header     := {
      trustLevel, imports, moduleData
      isModule
      regions      := modules.flatMap (·.parts.map (·.2))
      moduleNames  := s.moduleNames
    }
  }
  let publicConstants : ConstMap := SMap.fromHashMap publicConstantMap false
  let publicBase := { privateBase with constants := publicConstants, header.regions := #[] }
  let mut env : Environment := {
    base.private := privateBase
    base.public  := publicBase
    realizedImportedConsts? := none
  }
  env := env.setCheckedSync { env.base.private with extensions := (← setImportedEntries env.base.private.extensions moduleData) }
  let serverData := modules.filterMap (·.serverData? level)
  env := { env with serverBaseExts := (← setImportedEntries env.base.private.extensions serverData) }
  if leakEnv then
    /- Mark persistent a first time before `finalizePersistenExtensions`, which
       avoids costly MT markings when e.g. an interpreter closure (which
       contains the environment) is put in an `IO.Ref`. This can happen in e.g.
       initializers of user environment extensions and is wasteful because the
       environment is marked persistent immediately afterwards anyway when the
       constructed extension including the closure is ultimately stored in the
       initialized constant. We have seen significant savings in `open Mathlib`
       timings, where we have both a big environment and interpreted environment
       extensions, from this. There is no significant extra cost to calling
       `markPersistent` multiple times like this.

       Safety: There are no concurrent accesses to `env` at this point. -/
    env ← unsafe Runtime.markPersistent env
  if loadExts then
    env ← finalizePersistentExtensions env moduleData opts
    if leakEnv then
      /- Ensure the final environment including environment extension states is
        marked persistent as documented.

        Safety: There are no concurrent accesses to `env` at this point, assuming
        extensions' `addImportFn`s did not spawn any unbound tasks. -/
      env ← unsafe Runtime.markPersistent env
  return { env with realizedImportedConsts? := some {
    -- safety: `RealizationContext` is private
    env := unsafe unsafeCast env
    opts
    constsRef := (← IO.mkRef {})
  } }




-- def toImportState (s : ImportState2) : ImportState := {
--   moduleNameMap := s.moduleNameMap
--   moduleNames := s.moduleNames
-- }

def importModulesPartial (imports : Array Import)
    (plugins : Array System.FilePath := #[])
    (level := OLeanLevel.private) : IO ImportState2 :=
  withImporting do
    for imp in imports do
      if imp.module matches .anonymous then
        throw <| IO.userError "import failed, trying to import module with anonymous name"
    plugins.forM Lean.loadPlugin
    let (_, s) ← importModulesCore2 (forceImportAll := level == .private) imports |>.run
    pure s

def finalizeEnv (imports : Array Import) (opts : Options)
    (trustLevel : UInt32 := 0) (state : ImportState2)
    (leakEnv := false) (loadExts := false) (level := OLeanLevel.private) : IO Environment := do
    withImporting do
      finalizeImport (leakEnv := leakEnv) (loadExts := loadExts) (level := level) (state) imports opts trustLevel

def addImportedModulesCore (imports : Array Import) (forceImportAll := true) (prevState : ImportState2) :
    ImportStateM2 Unit := do
    set prevState
    importModulesCore2 (forceImportAll := forceImportAll) imports

def addImportedModulesPartial (imports : Array Import)
    (prevState : ImportState2)
    (forceImportAll := true) : IO ImportState2 := do
  withImporting do
    for imp in imports do
      if imp.module matches .anonymous then
        throw <| IO.userError "import failed, trying to import module with anonymous name"
    let (_, s) ← (addImportedModulesCore imports forceImportAll prevState).run
    pure s


def test : IO Unit := do
  init
  let imports := #[
    { module := `VerifiedAgora.Test1 },
  ]
  let t1 := (← IO.monoMsNow)
  let state ← importModulesPartial imports
  -- IO.println s!"Imported modules: {state.moduleNames}"
  let t2 := (← IO.monoMsNow)
  IO.println s!"Imported first in {t2 - t1} ms."

  -- let state2 ← importModulesPartial #[{ module := `Lean.Util.CollectAxioms}]
  let state2 ← addImportedModulesPartial #[{ module := `VerifiedAgora.Test2 }] state
  let t3 := (← IO.monoMsNow)
  IO.println s!"Imported second in {t3 - t2} ms."

  let env ← finalizeEnv imports Options.empty 0 state2
  let t4 := (← IO.monoMsNow)
  IO.println s!"Finalized in {t4 - t3} ms."

  IO.println s!"Environment has {env.constants.toList.length} constants."
  -- IO.println s!"env 1 present: {env.constants.contains `test1}"
  -- IO.println s!"env 2 present: {env.constants.contains `test2}"

-- #eval test

-- def getAllDependencies (imports : Array Import) : Array Import := do


structure ImportClosure where
  toplevel : Array Import
  allImports : Array Import
  removed : Array Import
  state : ImportState

def makeImportClosure (imports : Array Import) (prevClosure : Option ImportClosure) : IO ImportClosure := do
  match prevClosure with
  | none =>
    let state ← importModulesPartial imports
    return { toplevel := imports, allImports := imports, removed := #[], state := state } -- TODO: dependencies of imports
  | some prev =>


unsafe def makeEnvFor (input : String) (curr : IO Environment := mkEmptyEnvironment) : IO (Environment × String) := do
  let ⟨imports, pos, msgs⟩ ← parseImports input
  if !msgs.toList.isEmpty then
    throw <| IO.userError s!"failed to parse imports"

  let pos := FileMap.ofString input |>.ofPosition pos
  let rest := input.extract pos input.endPos

  let old_env ← curr
  if (old_env.imports.map (fun x => x.module.toString) |>.insertionSort) = (imports.map (fun x => x.module.toString) |>.insertionSort) then
    return (old_env, rest)
  old_env.freeRegions

  let env ← importModules imports Options.empty (leakEnv := false) (loadExts := true)

  return (env, rest)
