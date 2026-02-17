import Cli.Extensions
import VerifiedAgora.tagger
import VerifiedAgora.Frontend
import VerifiedAgora.TacticInvocation
import VerifiedAgora.constantData
open Lean Core Elab IO Meta Term Command Tactic Cli ConstantData




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


def Lean.ConstantInfo.kind (cd : ConstantInfo) : String := match cd with
  | .axiomInfo  _ => "axiom"
  | .defnInfo   _ => "def"
  | .thmInfo    _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo   _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo   _ => "constructor"
  | .recInfo    _ => "recursor"


/-- Removes duplicate `(severity, message)` pairs while preserving order. -/
def dedupMessages (msgs : List (MessageSeverity × String)) : List (MessageSeverity × String) :=
  msgs.foldl (fun acc msg => if acc.contains msg then acc else acc ++ [msg]) []

structure Info where
  name: Name
  constInfo: ConstantData
  axioms: Array Name
  --nonComputable: Bool

instance : Inhabited _root_.Info where
  default := { name := Name.anonymous, constInfo := default, axioms := #[] }


/-
From Lean.Environment
Check if two theorems have the same type and name
-/
def equivThm (cinfo₁ cinfo₂ : ConstantData) : Bool := Id.run do
  let .thmData tval₁ := cinfo₁ | false
  let .thmData tval₂ := cinfo₂ | false
  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams

/-
Check if two definitions have the same type and name.
If checkVal is true, then also check their values are the same
-/
def equivDefn (ctarget cnew : ConstantData)(checkVal:Bool:=false) : Bool := Id.run do
  let .defnData tval₁ := ctarget | false
  let .defnData tval₂ := cnew | false

  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.safety == tval₂.safety
    && (if checkVal then tval₁.value==tval₂.value else true)

def normalizeSerializedExprForModules (s : String) (submissionMod : Name) (targetMod? : Option Name) : String :=match targetMod? with
  | none => s
  | some targetMod =>
    let s := s.replace submissionMod.toString "<MODULE>"
    s.replace targetMod.toString "<MODULE>"

def equivThmDataNormalized (a b : ConstantData) (submissionMod : Name) (targetMod? : Option Name) : Bool := match a, b with
  | .thmData t1, .thmData t2 =>
      t1.name == t2.name &&
      normalizeSerializedExprForModules t1.type submissionMod targetMod? ==
        normalizeSerializedExprForModules t2.type submissionMod targetMod? &&
      t1.levelParams == t2.levelParams
  | _, _ => false

def equivDefnDataNormalized (a b : ConstantData) (submissionMod : Name) (targetMod? : Option Name) (checkVal : Bool := false) : Bool := match a, b with
  | .defnData d1, .defnData d2 =>
      d1.name == d2.name &&
      normalizeSerializedExprForModules d1.type submissionMod targetMod? ==
        normalizeSerializedExprForModules d2.type submissionMod targetMod? &&
      d1.levelParams == d2.levelParams &&
      d1.all == d2.all &&
      d1.safety == d2.safety &&
      (if checkVal then
        normalizeSerializedExprForModules d1.value submissionMod targetMod? ==
          normalizeSerializedExprForModules d2.value submissionMod targetMod?
      else true)
  | _, _ => false



structure DeclarationDescriptor where
  ci : ConstantData
  contents : String
  context : String
  axioms : Array Name
  target? : Bool
  resolved? : Bool
  deriving Inhabited, BEq



def DeclarationDescriptor.toJson (desc : DeclarationDescriptor) : Json :=

    Json.mkObj [
    ("name", Json.str desc.ci.name.toString),
    ("kind", Json.str desc.ci.kind),
    ("contents", Json.str desc.contents),
    ("target?", Json.bool desc.target?),
    ("context", Json.str desc.context),
    ("resolved?", Json.bool desc.resolved?),
    ("axioms", Json.arr <| desc.axioms.map (fun ax => Json.str ax.toString)),
    ("ci", ToJson.toJson desc.ci)
  ]

def DeclarationDescriptor.fromJson (json : Json) : Except String DeclarationDescriptor := do
  -- let name ← json.getObjValAs? String "name"
  -- let kind ← json.getObjValAs? String "kind"
  let contents ← json.getObjValAs? String "contents"
  let context ← json.getObjValAs? String "context"
  let target? ← json.getObjValAs? Bool "target?"
  let resolved? ← json.getObjValAs? Bool "resolved?"
  -- let sourceFile? := match (← json.getObjValAs? (Option String) "sourceFile") with
  --   | some s => some (System.FilePath.mk s)
  --   | none   => none
  let axiomsJson ← json.getObjValAs? (Array Json) "axioms"
  let axioms ← axiomsJson.mapM (fun axJson => do
    let axStr ← axJson.getStr?
    return Name.mkSimple axStr
  )

  let ci ← FromJson.fromJson? (← json.getObjValAs? Json "ci") |>.mapError (fun e => s!"Error parsing 'ci': {e}")

  return {
    ci := ci,
    contents := contents,
    context := context,
    target? := target?,
    resolved? := resolved?,
    -- sourceFile? := sourceFile?,
    axioms := axioms
  }

instance : ToJson DeclarationDescriptor where
  toJson fd := fd.toJson

instance : FromJson DeclarationDescriptor where
  fromJson? json := DeclarationDescriptor.fromJson json

instance : ToString DeclarationDescriptor where
  toString fd := ToJson.toJson fd |>.pretty



-- abbrev FileDescriptor := List DeclarationDescriptor
structure FileDescriptor where
  decls : List DeclarationDescriptor
  path : System.FilePath
  moduleName : Name
  contents : String
  deriving Inhabited, BEq, ToJson, FromJson
