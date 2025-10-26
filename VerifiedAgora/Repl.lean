import Lean.Elab.Frontend
import Lean.Util.CollectAxioms
import VerifiedAgora.Frontend
import VerifiedAgora.Environment


open Lean Elab

def new_constants (old : Environment) (new : Environment) : List ConstantInfo :=
  new.constants.map₂.toList.filterMap
    fun (c, i) => if old.constants.map₂.contains c then none else some i

def collectAxiomsButBetter (env : Environment) (constName : Name) : IO (Array Name) := do
  let (_, s) := ((CollectAxioms.collect constName).run env).run {}
  pure s.axioms

def AllowedAxioms := [`propext, `Quot.sound, `Classical.choice]

def ensureClean (old : Environment) (new : Environment) : IO Unit := do
  let cis := new_constants old new
  for ci in cis do
    -- IO.println s!"New constant: {ci.name}"
    let axioms := (← collectAxiomsButBetter new ci.name).toList
    for ax in axioms do
      -- IO.println s!"{ci.name} uses axiom {ax}"
      if !AllowedAxioms.contains ax then
        throw <| IO.userError s!"environment is not clean, new axiom {ax} used in {ci.name}"

    -- if ci.isUnsafe then
    --   throw <| IO.userError s!"environment is not clean, new unsafe definition: {ci.name}"




def check_input (env : Environment) (input : String) : IO Unit := do
  -- let steps := IO.processInput' input (some env) Options.empty
  -- let cis ← steps.foldM (init := []) (fun cis step => do
  --   let curr := IO.CompilationStep.diff step
  --   pure (curr ++ cis))

  -- let ⟨new, msgs, trees⟩ ← IO.processInput input (some env) Options.empty

  let ⟨new, msgs⟩ ← process input env Options.empty

  for msg in msgs.toList do
    if msg.severity == MessageSeverity.error then
      throw <| IO.userError s!"failed to process input: {← msg.toString}"

  ensureClean env new
  -- let cis := new_constants env new

  -- for ci in cis do
  --   IO.println s!"{ci.name}"



unsafe def process_inputs (inputs : Array String) : IO Unit := do
  let mut env ← mkEmptyEnvironment
  for input in inputs do
    let mut (new_env, decl) ← makeEnv input (pure env)
    check_input new_env decl
    env := new_env



def test_input := "import Lean

def test := (1 : Nat)

def test2 : Nat := 1
-- axiom test_ax : False
"


unsafe def stress_test (total : Nat) : IO Unit := do
  init
  let inputs := Array.replicate total test_input
  let t1 := (← IO.monoMsNow)
  process_inputs inputs
  let t2 := (← IO.monoMsNow)
  IO.println s!"Processed {total} inputs in {t2 - t1} ms."

-- #eval stress_test 1
