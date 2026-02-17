import Lean

open Lean

def AllowedAxioms : List Name := [`propext, `Quot.sound, `Classical.choice]
def TargetsAllowedAxioms : List Name := AllowedAxioms ++ [`sorryAx]

def collectAxiomsRaw (env : Environment) (n : Name) : Array Name :=
  let (_, s) := (CollectAxioms.collect n).run env |>.run {}
  s.axioms
