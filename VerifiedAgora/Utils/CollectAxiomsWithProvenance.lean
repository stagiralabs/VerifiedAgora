import Lean.MonadEnv
import Lean.Util.FoldConsts
import Std.Data.HashMap

namespace Lean
namespace CollectAxiomsWithProvenance

structure State where
  visited    : NameSet := {}
  axioms     : Array Name := #[]
  provenance : Std.HashMap Name (Array Name) := {}

/-- Reader carries (Environment, currentDirectDep). -/
abbrev M := ReaderT (Environment × Name) (StateM State)

mutual
  partial def collect (c : Name) : M Unit := do
    let s ← get
    if s.visited.contains c then return
    modify fun s => { s with visited := s.visited.insert c }
    let (env, curDep) := ← read
    match env.find? c with
    | some (ConstantInfo.axiomInfo _) =>
        modify fun s =>
          let alreadySeen := s.provenance.contains c
          let prev := match s.provenance.get? c with
            | some arr => arr
            | none => #[]
          { s with
            axioms     := if alreadySeen then s.axioms else s.axioms.push c
            provenance := s.provenance.insert c (prev.push curDep) }
    | some (ConstantInfo.defnInfo v) =>
        collectExpr v.type; collectExpr v.value
    | some (ConstantInfo.thmInfo v) =>
        collectExpr v.type; collectExpr v.value
    | some (ConstantInfo.opaqueInfo v) =>
        collectExpr v.type; collectExpr v.value
    | some (ConstantInfo.quotInfo _) =>
        pure ()
    | some (ConstantInfo.ctorInfo v) =>
        collectExpr v.type
    | some (ConstantInfo.recInfo v) =>
        collectExpr v.type
    | some (ConstantInfo.inductInfo v) =>
        collectExpr v.type
        for ctor in v.ctors do
          collect ctor
    | none =>
        pure ()

  partial def collectExpr (e : Expr) : M Unit := do
    for c in e.getUsedConstants do
      collect c
end

end CollectAxiomsWithProvenance

/-- Collect all axioms reachable from `name` with provenance tracking.
    Returns `(allAxioms, axiom → directDeps map)` where each axiom is mapped
    to the direct dependencies of `name` through which it was first reached. -/
def collectAxiomsWithProvenance (env : Environment) (name : Name) :
    Array Name × Std.HashMap Name (Array Name) :=
  let directDeps := match env.find? name with
    | some (.defnInfo v)   => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.thmInfo v)    => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | _                    => #[]
  let action : StateM CollectAxiomsWithProvenance.State Unit := do
    for dep in directDeps do
      (CollectAxiomsWithProvenance.collect dep).run (env, dep)
  let (_, s) := action.run {}
  (s.axioms, s.provenance)

end Lean
