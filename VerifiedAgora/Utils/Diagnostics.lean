import Lean
import VerifiedAgora.Utils.Axioms

open Lean


structure CollectedFailure where
  declName : String
  moduleName : String
  kind : String
  summary : String
  detail : String
  deriving Inhabited, BEq, ToJson

def diagnosticErrorMessage (label : String) (data : Json) : IO.Error :=
  IO.userError s!"{label}\n<AGORA_DIAGNOSTICS>\n{data.pretty}\n</AGORA_DIAGNOSTICS>"

def appendFailures (failuresRef : IO.Ref (Array CollectedFailure)) (newFailures : Array CollectedFailure) : IO Unit := do
  failuresRef.modify (fun failures =>
    newFailures.foldl (fun acc f => if acc.contains f then acc else acc.push f) failures
  )

def mergeFailures (base : Array CollectedFailure) (extra : Array CollectedFailure) : Array CollectedFailure :=
  extra.foldl (fun acc f => if acc.contains f then acc else acc.push f) base

def collectAxiomViolations
    (n : Name)
    (axioms : Array Name)
    (allow_sorry? : Bool := false)
    (moduleName : String := "<unknown>") : Array CollectedFailure := Id.run do
  let allowedAxioms := if allow_sorry? then TargetsAllowedAxioms else AllowedAxioms
  let mut out : Array CollectedFailure := #[]
  for a in axioms do
    if a ∉ allowedAxioms then
      out := out.push {
        declName := n.toString
        moduleName := moduleName
        kind := "disallowed_axiom"
        summary := "A declaration relies on a disallowed axiom."
        detail := s!"Declaration {n} relies on axiom {a}, which is not in its allowed set ({String.intercalate ", " (allowedAxioms.map Name.toString)})."
      }
  out
