import Lean

open Lean Core IO

instance : Hashable ModuleIdx where
  hash s := @Hashable.hash Nat _ s

def batchHumanDecls
    (names : Array Name)
    (env : Environment)
    (excludeInternal : Bool := false) : IO (Std.HashMap Name DeclarationRanges) := do
  let ctx := { fileName := "", fileMap := default }
  let state : Core.State := { env := env }
  let fn : CoreM (Std.HashMap Name DeclarationRanges) := do
    let mut out : Std.HashMap Name DeclarationRanges := {}
    for name in names do
      let hasDeclRange := (← Lean.findDeclarationRanges? name)
      let notProjFn := !(← Lean.isProjectionFn name)
      let notInternal := !excludeInternal || !name.isInternal
      match (hasDeclRange, notProjFn, notInternal) with
      | (some rng, true, true) =>
        out := out.insert name rng
      | _ =>
        pure ()
    pure out

  let result? ← CoreM.run' fn ctx state |>.toIO'
  match result?.toOption with
  | some out => pure out
  | none => pure {}

def getConstantsInModule (env : Environment) (mod? : Option Name) : IO (Std.HashMap Name ConstantInfo) := do
  if let some mod := mod? then
    let modIdx? : Option ModuleIdx := env.getModuleIdx? mod
    let mut ciMap : Std.HashMap Name ConstantInfo := {}
    for (n, ci) in env.constants do
      let ownedByModule := match modIdx?, env.getModuleIdxFor? n with
        | some modIdx, some declIdx => modIdx == declIdx
        | _, _ => false
      if ownedByModule then
        ciMap := ciMap.insert n ci
    pure ciMap
  else
    pure <| env.constants.map₂.toList.foldl (fun m (n, ci) => m.insert n ci) {}


def getConstantsInModules
    (env : Environment)
    (mods : Array Name)
    (includeRoots : Bool := true) : IO (Std.HashMap Name ConstantInfo) := do
  let mut allowed : Std.HashSet ModuleIdx := {}
  for m in mods do
    if let some rootIdx := env.getModuleIdx? m then
      if includeRoots then
        allowed := allowed.insert rootIdx
      if let some md := env.header.moduleData.get? rootIdx.toNat then
        for imp in md.imports do
          if let some impIdx := env.getModuleIdx? imp.module then
            allowed := allowed.insert impIdx

  let mut out : Std.HashMap Name ConstantInfo := {}
  for (n, ci) in env.constants do
    if let some owner := env.getModuleIdxFor? n then
      if allowed.contains owner then
        out := out.insert n ci
  pure out
