import Lean.Attributes

open Lean

initialize targetAttribute : Lean.TagAttribute ←
  Lean.registerTagAttribute `target "Marks a declaration as a target."
