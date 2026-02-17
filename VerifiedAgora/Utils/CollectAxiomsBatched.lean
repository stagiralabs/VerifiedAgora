import Lean.MonadEnv
import Lean.Util.FoldConsts
import Std.Data.HashMap

namespace Lean
namespace CollectAxiomsBatched

open Std

def NameSet.union (a b : NameSet) : NameSet :=
  b.fold (init := a) (fun acc n => acc.insert n)

structure State where
  visiting : NameSet := {}
  cache    : Std.HashMap Name NameSet := {}

abbrev M := ReaderT Environment (StateM State)

mutual
  partial def collectExpr (e : Expr) : M NameSet := do
    let mut out : NameSet := {}
    for c in e.getUsedConstants do
      out := out.union (← collectSet c)
    return out

  partial def collectSet (c : Name) : M NameSet := do
    let s ← get
    if let some res := s.cache[c]? then
      return res
    if s.visiting.contains c then
      return {}   -- cycle guard

    modify fun s => { s with visiting := s.visiting.insert c }

    let env ← read
    let res ← match env.find? c with
      | some (ConstantInfo.axiomInfo _) =>
          pure (NameSet.empty.insert c)
      | some (ConstantInfo.defnInfo v) =>
          pure <| (← collectExpr v.type).union (← collectExpr v.value)
      | some (ConstantInfo.thmInfo v) =>
          pure <| (← collectExpr v.type).union (← collectExpr v.value)
      | some (ConstantInfo.opaqueInfo v) =>
          pure <| (← collectExpr v.type).union (← collectExpr v.value)
      | some (ConstantInfo.quotInfo _) =>
          pure {}
      | some (ConstantInfo.ctorInfo v) =>
          pure <| (← collectExpr v.type)
      | some (ConstantInfo.recInfo v) =>
          pure <| (← collectExpr v.type)
      | some (ConstantInfo.inductInfo v) =>
          let base ← collectExpr v.type
          let mut out := base
          for ctor in v.ctors do
            out := out.union (← collectSet ctor)
          pure out
      | none =>
          pure {}

    modify fun s =>
      { s with
        visiting := s.visiting.erase c
        cache := s.cache.insert c res }

    return res
end


def collectAxiomsBatched (env : Environment) (roots : Array Name) :
    Std.HashMap Name (Array Name) :=
  let action : M (Std.HashMap Name (Array Name)) := do
    let mut out : Std.HashMap Name (Array Name) := {}
    for r in roots do
      let axSet ← collectSet r
      out := out.insert r (axSet.toList.toArray)
    return out
  ((action.run env).run {}).1


end CollectAxiomsBatched
end Lean
