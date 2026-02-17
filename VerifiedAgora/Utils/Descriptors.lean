import Lean
import VerifiedAgora.Utils.ConstantData

open Lean ConstantData

def Lean.ConstantInfo.kind (cd : ConstantInfo) : String := match cd with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def equivThm (cinfo₁ cinfo₂ : ConstantData) : Bool := Id.run do
  let .thmData tval₁ := cinfo₁ | false
  let .thmData tval₂ := cinfo₂ | false
  return tval₁.name == tval₂.name
    && tval₁.typeKey == tval₂.typeKey
    && tval₁.levelParams == tval₂.levelParams

def equivDefn (ctarget cnew : ConstantData) (checkVal : Bool := false) : Bool := Id.run do
  let .defnData tval₁ := ctarget | false
  let .defnData tval₂ := cnew | false

  return tval₁.name == tval₂.name
    && tval₁.typeKey == tval₂.typeKey
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.safety == tval₂.safety
    && (if checkVal then tval₁.valueKey == tval₂.valueKey else true)

def equivThmDataNormalized (a b : ConstantData) (_submissionMod : Name) (_targetMod? : Option Name) : Bool :=
  equivThm a b

def equivDefnDataNormalized (a b : ConstantData) (_submissionMod : Name) (_targetMod? : Option Name) (checkVal : Bool := false) : Bool :=
  equivDefn a b checkVal

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
  let contents ← json.getObjValAs? String "contents"
  let context ← json.getObjValAs? String "context"
  let target? ← json.getObjValAs? Bool "target?"
  let resolved? ← json.getObjValAs? Bool "resolved?"
  let axiomsJson ← json.getObjValAs? (Array Json) "axioms"
  let axioms ← axiomsJson.mapM (fun axJson => do
    let axStr ← axJson.getStr?
    return Name.mkSimple axStr
  )

  let ci ← FromJson.fromJson? (← json.getObjValAs? Json "ci") |>.mapError (fun e => s!"Error parsing 'ci': {e}")

  pure {
    ci := ci,
    contents := contents,
    context := context,
    target? := target?,
    resolved? := resolved?,
    axioms := axioms
  }

instance : ToJson DeclarationDescriptor where
  toJson fd := fd.toJson

instance : FromJson DeclarationDescriptor where
  fromJson? json := DeclarationDescriptor.fromJson json

instance : ToString DeclarationDescriptor where
  toString fd := ToJson.toJson fd |>.pretty

structure FileDescriptor where
  decls : List DeclarationDescriptor
  path : System.FilePath
  moduleName : Name
  contents : String
  deriving Inhabited, BEq, ToJson, FromJson
