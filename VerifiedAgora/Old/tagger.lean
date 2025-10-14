import Lean.Attributes
open Lean Core Elab IO Meta Tactic

initialize targetAttribute : Lean.TagAttribute ←
  Lean.registerTagAttribute `target "Marks a declaration as a target."
