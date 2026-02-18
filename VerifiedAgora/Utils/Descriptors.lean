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
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams

def equivDefn (ctarget cnew : ConstantData) (checkVal : Bool := false) : Bool := Id.run do
  let .defnData tval₁ := ctarget | false
  let .defnData tval₂ := cnew | false

  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.safety == tval₂.safety
    && (if checkVal then tval₁.value == tval₂.value else true)

instance : ToJson DeclarationRange where
  toJson r := Json.mkObj [
    ("pos", ToJson.toJson r.pos),
    ("endPos", ToJson.toJson r.endPos),
    ("charUtf16", ToJson.toJson r.charUtf16),
    ("endCharUtf16", ToJson.toJson r.endCharUtf16)
  ]
instance : FromJson DeclarationRange where
  fromJson? j := do
    let pos ← j.getObjValAs? Position "pos"
    let endPos ← j.getObjValAs? Position "endPos"
    let charUtf16 ← j.getObjValAs? Nat "charUtf16"
    let endCharUtf16 ← j.getObjValAs? Nat "endCharUtf16"
    return {
      pos := pos,
      endPos := endPos,
      charUtf16 := charUtf16,
      endCharUtf16 := endCharUtf16
    }

instance : Hashable Position where
  hash p := hash (p.line, p.column)

instance : Hashable DeclarationRange where
  hash r := hash (r.pos, r.endPos, r.charUtf16, r.endCharUtf16)

instance : ToJson AttributeKind where
  toJson k := Json.str <| match k with
    | AttributeKind.global => "global"
    | AttributeKind.local => "local"
    | AttributeKind.scoped => "scoped"
instance : FromJson AttributeKind where
  fromJson? j := do
    let s ← j.getStr?
    match s with
    | "global" => Except.ok AttributeKind.global
    | "local" =>  Except.ok AttributeKind.local
    | "scoped" => Except.ok AttributeKind.scoped
    | _ => Except.error "Invalid AttributeKind value"

instance : Hashable AttributeKind where
  hash k := match k with
    | AttributeKind.global => 0
    | AttributeKind.local => 1
    | AttributeKind.scoped => 2

structure DeclarationDescriptor where
  name : Name -- Redundant with `ci.<whatever>.name`, but makes some code simpler
  ci : ConstantData
  contents : String
  range : DeclarationRange
  -- context : String
  axioms : Array Name
  target : Bool
  resolved : Bool
  modified : Bool
  new : Bool
  attributes : Array Name
  isInstance : (Bool × Option Nat × Option AttributeKind)
  deriving Inhabited, BEq, ToJson, FromJson, Hashable

instance [BEq α] [Hashable α]: BEq (Std.HashSet α) where
  beq s1 s2 := s1.all (fun x => s2.contains x) && s2.all (fun x => s1.contains x)

structure FileDescriptor where
  decls : Array DeclarationDescriptor
  path : System.FilePath
  moduleName : Name
  contents : String
  deriving Inhabited, BEq, ToJson, FromJson
