import Lean.Elab.Frontend

open Lean Elab

def init : IO Unit := do
  initSearchPath (← getLibDir (← findSysroot))
  unsafe Lean.enableInitializersExecution


unsafe def makeEnv (input : String) (curr : IO Environment := mkEmptyEnvironment) : IO (Environment × String) := do
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

def check_input (env : Environment) (input : String) : IO Unit := do
  let ⟨_, msgs⟩ ← process input env Options.empty
  if !msgs.toList.isEmpty then
    throw <| IO.userError s!"failed to process input. Error: {← msgs.toList[0]!.toString}"
  -- IO.println "Processed input successfully."

unsafe def process_inputs (inputs : Array String) : IO Unit := do
  let mut env ← mkEmptyEnvironment
  for input in inputs do
    let mut (new_env, decl) ← makeEnv input (pure env)
    check_input new_env decl
    env := new_env






def test_input := "import Lean

def test := (1 : Nat)

def test2 := test + 1"


unsafe def stress_test (total : Nat) : IO Unit := do
  init
  let inputs := Array.replicate total test_input
  let t1 := (← IO.monoMsNow)
  process_inputs inputs
  let t2 := (← IO.monoMsNow)
  IO.println s!"Processed {total} inputs in {t2 - t1} ms."

-- #eval stress_test 1000
