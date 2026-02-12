import Cli.Extensions
import VerifiedAgora.tagger
import VerifiedAgora.Frontend
import VerifiedAgora.TacticInvocation
open Lean Core Elab IO Meta Term Command Tactic Cli




def diagnosticErrorMessage (label : String) (data : Json) : Error :=
  IO.userError s!"{label}\n<AGORA_DIAGNOSTICS>\n{data.pretty}\n</AGORA_DIAGNOSTICS>"


def getFileOrModuleContents (name : String) : IO (String × Name × System.FilePath) := do
    --first attempt as module name
    let modName := name.toName
    try
      let contents? ← moduleSource modName
      let file_path ← findLean modName
      return (contents?, modName, file_path)
    catch e =>
      try
        -- attempt as file name
        let contents? ← IO.FS.readFile name
        let moduleName ← moduleNameOfFileName (System.FilePath.mk name) none
        let file_path := System.FilePath.mk name
        return (contents?, moduleName, file_path)
      catch e2 =>
        throw <| IO.userError s!"Could not find module or file: {name}:\n  as module: {e}\n  as file: {e2}"



/-
  From Batteries.Lean.TagAttribute
-/

/-- Get the list of declarations tagged with the tag attribute `attr`. -/
def Lean.TagAttribute.getDecls (attr : TagAttribute) (env : Environment) : Array Name :=
  core <| attr.ext.toEnvExtension.getState env
where
  /-- Implementation of `TagAttribute.getDecls`. -/
  core (st : PersistentEnvExtensionState Name NameSet) : Array Name := Id.run do
    let mut decls := st.state.toArray
    for ds in st.importedEntries do
      decls := decls ++ ds
    decls




def Lean.ConstantInfo.kind : ConstantInfo → String
  | .axiomInfo  _ => "axiom"
  | .defnInfo   _ => "def"
  | .thmInfo    _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo   _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo   _ => "constructor"
  | .recInfo    _ => "recursor"

def AllowedAxioms := [`propext, `Quot.sound, `Classical.choice]
def TargetsAllowedAxioms := AllowedAxioms ++ [`sorryAx]

def checkAxioms (env: Environment) (n: Name) (allow_sorry? : Bool := false) : IO (Array Name):= do
  let (_,s):=(CollectAxioms.collect n).run env |>.run {}
  for a in s.axioms do
    let ax := if allow_sorry? then TargetsAllowedAxioms else AllowedAxioms
    if a ∉ ax then
      throw <| diagnosticErrorMessage s!"Declaration relies on disallowed axiom." <| Json.mkObj [
        ("summary", Json.str s!"A declaration in the attempted contribution relies on a disallowed axiom. Remember, standard declarations must only rely on the allowed set of standard axioms ({String.intercalate ", " (AllowedAxioms.map Name.toString)}) for Agora contributions. Declarations tagged as targets are allowed to additionally rely on \"sorryAx\", but only if the previous proof of said target also relied on \"sorryAx\" - meaning that contributions cannot regress already resolved targets to once again be unresolved."),
        ("offending axiom", Json.str s!"Declaration {n} relies on axiom {a}, which is not in its allowed set of axioms ({String.intercalate ", " (ax.map Name.toString)})")
      ]
      -- throw <| IO.userError s!"{a} is not in the allowed set of standard axioms ({n})"
  return s.axioms

-- /-- Returns `(usesSorry, disallowedAxioms, syntheticMsgs)` for declaration `n` in `env`.
-- Synthetic messages classify `sorryAx` as warning and disallowed axioms as error. -/
-- def axiomAudit (env : Environment) (n : Name) :
--     (Bool × Array Name × List (MessageSeverity × String)) := Id.run do
--   let (_, s) := (CollectAxioms.collect n).run env |>.run {}
--   let axioms := s.axioms

--   let usesSorry := axioms.contains `sorryAx
--   let disallowed := axioms.filter (fun a => a ∉ TargetsAllowedAxioms)

--   let mut msgs : List (MessageSeverity × String) := []
--   if usesSorry then
--     msgs := msgs ++ [(MessageSeverity.warning, "[Agora Warning] relies on sorryAx")]

--   if disallowed.size > 0 then
--     msgs := msgs ++ [(
--       MessageSeverity.error,
--       s!"[Agora Error] relies on disallowed axioms: {String.intercalate ", " (disallowed.toList.map Name.toString)}"
--     )]

--   (usesSorry, disallowed, msgs)

/-- Removes duplicate `(severity, message)` pairs while preserving order. -/
def dedupMessages (msgs : List (MessageSeverity × String)) : List (MessageSeverity × String) :=
  msgs.foldl (fun acc msg => if acc.contains msg then acc else acc ++ [msg]) []

structure Info where
  name: Name
  constInfo: ConstantInfo
  axioms: Array Name
  --nonComputable: Bool

instance : Inhabited _root_.Info where
  default := { name := Name.anonymous, constInfo := default, axioms := #[] }

/-
From Lean.Environment
Check if two theorems have the same type and name
-/
def equivThm (cinfo₁ cinfo₂ : ConstantInfo) : Bool := Id.run do
  let .thmInfo tval₁ := cinfo₁ | false
  let .thmInfo tval₂ := cinfo₂ | false
  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams

/-
Check if two definitions have the same type and name.
If checkVal is true, then also check their values are the same
-/
def equivDefn (ctarget cnew : ConstantInfo)(checkVal:Bool:=false) : Bool := Id.run do
  let .defnInfo tval₁ := ctarget | false
  let .defnInfo tval₂ := cnew | false

  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.safety == tval₂.safety
    && (if checkVal then tval₁.value==tval₂.value else true)



structure DeclarationDescriptor where
  ci : ConstantInfo
  contents : Substring
  context : Substring
  -- msgs? : Option (List (MessageSeverity × String))
  axioms : Array Name
  target? : Bool
  resolved? : Bool
  sourceFile? : Option System.FilePath


instance: BEq DeclarationDescriptor where
  beq d1 d2 :=
    d1.ci.name == d2.ci.name &&
    d1.ci.type == d2.ci.type &&
    d1.ci.kind == d2.ci.kind &&
    d1.sourceFile? == d2.sourceFile? &&
    d1.target? == d2.target? &&
    d1.axioms == d2.axioms &&
    d1.contents == d2.contents &&
    d1.context == d2.context

def DeclarationDescriptor.toJson (desc : DeclarationDescriptor) : Json :=

    Json.mkObj [
    ("name", Json.str desc.ci.name.toString),
    -- ("type", Json.str desc.ci.type.dbgToString),
    ("kind", Json.str desc.ci.kind),
    ("sourceFile", Json.str (match desc.sourceFile? with
      | some fp => toString (fp.normalize)
      | none    => "<unknown>"
      )
    ),
    ("contents", Json.str desc.contents.toString),
    ("target?", Json.bool desc.target?),
    ("context", Json.str desc.context.toString),
    -- ("msgs", match desc.msgs? with
    --   | some msgs => Json.arr <| msgs.toArray.map (fun (sev, data) => Json.mkObj [("severity", (ToJson.toJson sev)), ("data", Json.str data)])
    --   | none => Json.str "<unable to extract messages>"
    -- )
    ("resolved?", Json.bool desc.resolved?),
    ("axioms", Json.arr <| desc.axioms.map (fun ax => Json.str ax.toString))
  ]


instance : ToJson DeclarationDescriptor where
  toJson fd := fd.toJson

instance : ToString DeclarationDescriptor where
  toString fd := ToJson.toJson fd |>.pretty



abbrev FileDescriptor := List DeclarationDescriptor
