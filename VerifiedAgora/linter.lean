import Lean.Elab.Command
import VerifiedAgora.TargetAttr
import VerifiedAgora.Utils.Axioms
import VerifiedAgora.Utils.CollectAxiomsWithProvenance

open Lean Elab

register_option VerifiedAgora.showAxiomUsage : Bool := {
  defValue := false
  descr := "Check axiom usage for each declaration and report violations"
}

/-- Linter cache: tracks checked declarations and the last-seen map₂ size
    to detect file re-elaboration (where map₂ resets to a smaller size). -/
structure LinterCache where
  checkedDecls : NameSet := {}
  lastMap₂Size : Nat := 0
  deriving Inhabited

initialize linterCacheRef : IO.Ref LinterCache ←
  IO.mkRef {}

/-- Create a synthetic Syntax node positioned at a declaration's selection range. -/
private def mkSelectionStx (fileMap : FileMap) (declRanges : DeclarationRanges) : Syntax :=
  let sel := declRanges.selectionRange
  let startPos := fileMap.ofPosition sel.pos
  let endPos := fileMap.ofPosition sel.endPos
  Syntax.atom (SourceInfo.synthetic startPos endPos) ""

/-- Format provenance messages for disallowed axioms using the provenance map. -/
private def formatAxiomMessages (directDepSet : Std.HashSet Name)
    (provenance : Std.HashMap Name (Array Name))
    (disallowed : Array Name) : Array MessageData := Id.run do
  let mut msgs : Array MessageData := #[]
  for ax in disallowed do
    if directDepSet.contains ax then
      msgs := msgs.push m!"  · {ax} — used directly in the declaration"
    else
      match provenance.get? ax with
      | some sources =>
          let sources := Std.HashSet.ofArray sources |>.toArray
          msgs := msgs.push m!"  · {ax} — introduced transitively via {sources.toList}"
      | none =>
          msgs := msgs.push m!"  · {ax} — introduced transitively (source unknown)"
  return msgs

def checkAxiomUsageLinter : Linter where run := fun stx => do
  unless Linter.getLinterValue VerifiedAgora.showAxiomUsage (← getOptions) do return
  let env ← getEnv
  let fileMap ← getFileMap
  let cache ← linterCacheRef.get
  let map₂List := env.constants.map₂.toList
  let curSize := map₂List.length
  -- If map₂ shrank, the file was re-elaborated; reset cache
  let checkedDecls := if curSize < cache.lastMap₂Size then {} else cache.checkedDecls

  -- Collect unchecked human-written declarations:
  -- must have declaration ranges (source location) and not be a projection function
  let mut uncheckedNames : Array (Name × DeclarationRanges) := #[]
  let mut newCheckedDecls := checkedDecls
  for (name, _) in map₂List do
    if checkedDecls.contains name then continue
    newCheckedDecls := newCheckedDecls.insert name
    if name.isInternalDetail then continue
    let some declRanges ← findDeclarationRanges? name | continue
    if ← isProjectionFn name then continue
    uncheckedNames := uncheckedNames.push (name, declRanges)

  if uncheckedNames.isEmpty then
    linterCacheRef.set { checkedDecls := newCheckedDecls, lastMap₂Size := curSize }
    return

  for (name, declRanges) in uncheckedNames do
    let (axioms, provenance) := collectAxiomsWithProvenance env name
    if axioms.isEmpty then continue
    let nameStx := mkSelectionStx fileMap declRanges
    let isTarget := targetAttribute.hasTag env name
    let disallowedTarget := axioms.filter (fun a => a ∉ TargetsAllowedAxioms)
    let disallowedGeneral := axioms.filter (fun a => a ∉ AllowedAxioms)
    -- Build direct dep set for provenance formatting
    let directDeps := match env.find? name with
      | some (.defnInfo v)   => v.type.getUsedConstants ++ v.value.getUsedConstants
      | some (.thmInfo v)    => v.type.getUsedConstants ++ v.value.getUsedConstants
      | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
      | _                    => #[]
    let directDepSet := Std.HashSet.ofArray directDeps
    if isTarget && disallowedTarget.size > 0 then
      let traces := formatAxiomMessages directDepSet provenance disallowedTarget
      let detail := MessageData.joinSep traces.toList "\n"
      logErrorAt nameStx m!"@[target] declaration '{name}' uses axioms not in TargetsAllowedAxioms:\n{detail}"
    else if !isTarget && disallowedGeneral.size > 0 then
      let traces := formatAxiomMessages directDepSet provenance disallowedGeneral
      let detail := MessageData.joinSep traces.toList "\n"
      logErrorAt nameStx m!"declaration '{name}' uses axioms not in AllowedAxioms:\n{detail}"
    else if disallowedGeneral.size > 0 then
      let traces := formatAxiomMessages directDepSet provenance disallowedGeneral
      let detail := MessageData.joinSep traces.toList "\n"
      logWarningAt nameStx m!"@[target] declaration '{name}' uses axioms outside AllowedAxioms:\n{detail}"
  linterCacheRef.set { checkedDecls := newCheckedDecls, lastMap₂Size := curSize }

initialize addLinter checkAxiomUsageLinter
