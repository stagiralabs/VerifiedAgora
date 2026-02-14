import Cli.Extensions
import VerifiedAgora.tagger
import VerifiedAgora.Frontend
import VerifiedAgora.TacticInvocation
import VerifiedAgora.Utils
open Lean Core Elab IO Meta Term Command Tactic Cli Environment


def printExpr (ex : Expr) (env : Environment) : IO Format := do
  let ctx:={fileName:="", fileMap:=default}
  Prod.fst <$> (CoreM.toIO (MetaM.run' do ppExpr ex) ctx {env:=env})

def isHumanDecl (name : Name) (env : Environment) : IO (Option DeclarationRanges) := do
  let ctx := {fileName:="", fileMap:=default}
  let state : Core.State := {env := env}
  let fn : CoreM (Option DeclarationRanges) := do
    let hasDeclRange := (← Lean.findDeclarationRanges? name)
    let notProjFn := !(← Lean.isProjectionFn name)

    match (hasDeclRange, notProjFn) with
    | (some rng, true) => return (some rng)
    | _ => return none

  let result? ← CoreM.run' fn ctx state |>.toIO'
  match result?.toOption with
  | some x => pure x
  | none => pure none

def getDescriptorForModule (mod : Name) (targetDescriptor? : Option FileDescriptor := none) (sourceFile? : Option System.FilePath := none) : IO FileDescriptor := do

  let (moduleData, _) ← readModuleData (← findOLean mod)
  let env ← importModules moduleData.imports {} 0
  -- IO.println s!"Imported module data."

  let mut newConstants := {}
  for name in moduleData.constNames, ci in moduleData.constants do
    newConstants := newConstants.insert name ci
  let mut env' ← env.replay newConstants
  -- IO.println s!"Replayed constants."

  let env'' ← importModules #[{ module := mod }] {} 0
  let tagged_decls := env''.constants.fold (fun acc k ci => if TagAttribute.hasTag targetAttribute env'' k then ci::acc else acc) []
  let tagged_decl_names : Std.HashSet Name := tagged_decls.foldl (fun s ci => s.insert ci.name) {}
  -- IO.println s!"Found {tagged_decls.length} tagged declarations in the environment."

  let mut ret:Array (DeclarationDescriptor × DeclarationRanges) := #[]
  for (n,ci) in env'.constants.map₂  do
    -- IO.println s!"Processing declaration {n} of kind {ci.kind}..."
    if ci.kind ∈ ["theorem", "def"] then
      if let .defnInfo dv := ci then
        if dv.safety != .safe then
          let str_safety := match dv.safety with
            | .safe => "safe"
            | .unsafe => "unsafe"
            | .partial => "partial"
          throw <| diagnosticErrorMessage s!"unsafe/partial declaration detected" <| Json.mkObj [
            ("summary", Json.str "The attempted contribution contains unsafe or partial declarations, which are not allowed. Please change the declaration to be safe/total or remove it from the submission/target."),
            ("offending declaration", Json.str s!"Declaration {n} ({ci.kind}) has safety \"{str_safety}\".")
            ]

      if let some rng ← isHumanDecl n env'' then
        ret:=ret.push ({
          ci := ci,
          contents := default, -- we fill this in later since we need the file map for it
          context := default, -- we fill this in later since we need the file map for it
          target? := tagged_decl_names.contains n,
          sourceFile? := sourceFile?,
          axioms := default, -- we fill this in later when we do regression and axiom checking
          resolved? := default -- same
        },rng)

  let mut axiomMap : Std.HashMap Name (Array Name) := {}
  let baselineMode := (targetDescriptor?.isNone)
  let exprPrinter (e : Expr) := printExpr e env'

  if (targetDescriptor?.getD []).length > 0 then
    for target in targetDescriptor?.getD [] do
      if (← isHumanDecl target.ci.name env'').isSome then
        if let some ci':=env'.constants.map₂.find? target.ci.name then
          if target.ci.kind ≠ ci'.kind then
            throw <| diagnosticErrorMessage s!"Declaration kind mismatch between current and attempted contribution" <|
            Json.mkObj [
              ("summary", Json.str "The declaration kind in the attempted contribution does not match the corresponding declaration in the current version."),
              ("offending declaration", Json.str s!"Declaration {target.ci.name} has kind \"{ci'.kind}\" in the attempted contribution, but is expected to have kind \"{target.ci.kind}\".")
            ]
          if ci'.kind=="theorem" then
            if Not (equivThm target.ci ci') then
              throw <| diagnosticErrorMessage s!"Theorem statement mismatch between current and attempted contribution" <|
              Json.mkObj [
                ("summary", Json.str "A theorem statement in the attempted contribution does not match the corresponding theorem statement in the current version. Please ensure that the statement (type, name, etc.) of the theorem is exactly the same as in the current version."),
                ("offending declaration", Json.str s!"Theorem {target.ci.name} has type \"{← exprPrinter ci'.type}\" in the attempted contribution, but is expected to have type \"{← exprPrinter target.ci.type}\".")
              ]
          if ci'.kind=="def" then
            if Not (equivDefn target.ci ci' (`sorryAx ∉ target.axioms)) then
              let valStr ← if `sorryAx ∉ target.axioms then
                pure s!" \n\nAdditionally, the definitions have the following values:\n\nThe attempted contribution has value: \"{← exprPrinter ci'.value!}\"\n\nThe contribution is expected to have value: \"{← exprPrinter target.ci.value!}\""
              else pure ""
              throw <| diagnosticErrorMessage s!"Definition statement mismatch between current and attempted contribution" <| Json.mkObj [
                ("summary", Json.str "A definition statement in the attempted contribution does not match the corresponding definition statement in the current version. Please ensure that the statement (type, name, etc.) of the definition is exactly the same as in the current version. Additionally, unless the definition's value relies on the `sorry` axiom, the value of the definition must also be exactly the same."),
                ("offending declaration", Json.str <| s!"Definition {target.ci.name} has type:\n\n \"{← exprPrinter ci'.type}\" \n\nin the attempted contribution, and is expected to have type \n\n \"{← exprPrinter target.ci.type}\"" ++ valStr)
              ]

          let allow_sorry? := (`sorryAx ∈ target.axioms)
          -- Preserve baseline axiom status for existing declarations:
          -- if the target descriptor previously depended on sorryAx, allow that
          -- dependency in the submitted descriptor as well. This prevents
          -- unrelated pre-existing unresolved declarations from blocking
          -- verification of a focused contribution.
          axiomMap := axiomMap.insert target.ci.name (← checkAxioms env' target.ci.name allow_sorry?)
        else
          throw <| diagnosticErrorMessage s!"Missing declaration in attempted contribution." <| Json.mkObj [
            ("summary", Json.str s!"A declaration in the current file version was not found in the attempted contribution. Please ensure that all declarations in the current file version are still included in the your contribution (i.e. no deletions are allowed)."),
            ("offending declaration", Json.str s!"Declaration {target.ci.name} was found in the current file version, but no declaration with this name was found in the attempted contribution.")
          ]


  -- if we got here, we haven't failed! So now fill in contents and context and axioms!
  let trueSourceFile ← findLean mod
  let source ← IO.FS.readFile trueSourceFile
  let fileMap := FileMap.ofString source
  let output ← ret.mapM (fun (desc, rng) => do
    let axioms ← match axiomMap.get? desc.ci.name with
      | some a => pure a
      | none => checkAxioms env' desc.ci.name (if baselineMode then true else desc.target?)
    let emitSourceContext := desc.target?
    pure {desc with
      contents := if emitSourceContext
        then Substring.mk fileMap.source (fileMap.ofPosition rng.range.pos) (fileMap.ofPosition rng.range.endPos)
        else default,
      context := if emitSourceContext
        then Substring.mk fileMap.source ⟨0⟩ (fileMap.ofPosition rng.range.pos)
        else default,
      axioms := axioms,
      resolved? := axioms.all (fun a => a ∈ AllowedAxioms) -- we consider a declaration resolved if it relies only on allowed axioms, meaning it doesn't rely on sorry or any disallowed axioms
    })

  return output.toList


unsafe def getTargets' (submission_module : Name) (target_module : Option Name := none) (source_file : Option System.FilePath := none): IO FileDescriptor := do


  let targetDescriptor ← getDescriptorForModule (target_module.getD submission_module) (sourceFile? := source_file)
  let submittedDescriptor ← getDescriptorForModule submission_module targetDescriptor (sourceFile? := source_file)
  return submittedDescriptor



unsafe def getTargetsCLI (args : Cli.Parsed) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  enableInitializersExecution

  let submission := args.flag! "submission" |>.as! String
  let target := args.flag! "target" |>.as! String

  let target? := if target == "" then none else some target

  let savePath := args.flag! "save" |>.as! String
  let save? := if savePath == "" then none else some savePath

  try
    let targetContent? ← target?.mapM (fun t => getFileOrModuleContents t)

    let (_, target_mod?, fp?) := match targetContent? with
      | some (c, m, fp) => (some c, some m, some fp)
      | none => (none, none, none)


    let (_,sub_mod, _) ← getFileOrModuleContents submission
    let descriptor ← getTargets' sub_mod target_mod? fp?
    let json := ToJson.toJson descriptor
    if save?.isSome then
        let _ ← IO.FS.writeFile save?.get! (json.pretty)
        IO.println s!"Wrote file descriptor to {save?.get!}"
    else
      IO.println "<DESCRIPTOR>"
      IO.println json.pretty
      IO.println "</DESCRIPTOR>"

    IO.println "Finished with no errors."
    return 0
  catch e =>
    IO.eprintln s!"Error: {e}"
    return 1


unsafe def getTargets : Cmd := `[Cli|
  get_targets VIA getTargetsCLI; ["0.0.1"]
"Get targets from a string."

  FLAGS:
    submission : String; "In file mode, the submission module name."
    target : String; "The target module name. Optional; if not provided, then target=submission is assumed."
    save : String; "If provided, save the file descriptor to this file as json to specified path. Default is no save."

  EXTENSIONS:
    defaultValues! #[("target", ""), ("save", "")]
]


unsafe def main (args : List String) : IO UInt32 :=
  getTargets.validate args
