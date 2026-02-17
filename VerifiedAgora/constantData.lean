import Cli.Extensions
import VerifiedAgora.tagger
import VerifiedAgora.Frontend
import VerifiedAgora.TacticInvocation
open Lean Core Elab IO Meta Term Command Tactic Cli

abbrev SerializedExpr := String
def Lean.Expr.serialize (e : Expr) : SerializedExpr := e.dbgToString

def normalizeHygSegment (s : String) : String :=
  match s.splitOn "_hyg." with
  | [] => s
  | head :: tail =>
    tail.foldl (fun acc part =>
      let stripped := String.mk (part.data.dropWhile (fun c => c.isDigit))
      acc ++ "_hyg.0" ++ stripped
    ) head

def normalizeNameSegment (modStr : String) (s : String) : String :=
  normalizeHygSegment (s.replace modStr "<MODULE>")

partial def lastStrComponent? : Name → Option String
  | .anonymous => none
  | .str _ s => some s
  | .num p _ => lastStrComponent? p

partial def normalizeNameForModule (mod : Name) : Name → Name
  | .anonymous => .anonymous
  | .str p s =>
    let p' := normalizeNameForModule mod p
    .str p' (normalizeNameSegment mod.toString s)
  | .num p n =>
    let p' := normalizeNameForModule mod p
    let n' := match lastStrComponent? p' with
      | some s => if s == "_hyg" || s.endsWith "_hyg" then 0 else n
      | none => n
    .num p' n'

partial def normalizeLevelForModule (mod : Name) : Level → Level
  | .zero => .zero
  | .succ l => .succ (normalizeLevelForModule mod l)
  | .max l₁ l₂ => .max (normalizeLevelForModule mod l₁) (normalizeLevelForModule mod l₂)
  | .imax l₁ l₂ => .imax (normalizeLevelForModule mod l₁) (normalizeLevelForModule mod l₂)
  | .param n => .param (normalizeNameForModule mod n)
  | .mvar n => .mvar n

partial def normalizeExprForModule (mod : Name) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar id => .fvar id
  | .mvar id => .mvar id
  | .sort l => .sort (normalizeLevelForModule mod l)
  | .const n ls => .const (normalizeNameForModule mod n) (ls.map (normalizeLevelForModule mod))
  | .app f a => .app (normalizeExprForModule mod f) (normalizeExprForModule mod a)
  | .lam _ t b bi => .lam `_ (normalizeExprForModule mod t) (normalizeExprForModule mod b) bi
  | .forallE _ t b bi => .forallE `_ (normalizeExprForModule mod t) (normalizeExprForModule mod b) bi
  | .letE _ t v b nonDep =>
      .letE `_ (normalizeExprForModule mod t) (normalizeExprForModule mod v) (normalizeExprForModule mod b) nonDep
  | .lit l => .lit l
  | .mdata _ b => normalizeExprForModule mod b
  | .proj n i b => .proj (normalizeNameForModule mod n) i (normalizeExprForModule mod b)

def exprKeyForModule (mod : Name) (e : Expr) : UInt64 :=
  hash (normalizeExprForModule mod e)



structure ConstantDataVal where
  name : Name
  levelParams : List Name
  type : SerializedExpr
  typeKey : UInt64
  deriving Inhabited, BEq, ToJson, FromJson

structure AxiomDataVal extends ConstantDataVal where
  isUnsafe : Bool
  deriving Inhabited, BEq, ToJson, FromJson


instance : ToJson DefinitionSafety where
  toJson
    | DefinitionSafety.safe => Json.str "safe"
    | DefinitionSafety.unsafe => Json.str "unsafe"
    | DefinitionSafety.partial => Json.str "partial"

instance : FromJson DefinitionSafety where
  fromJson? json := match json with
    | Json.str s => match s with
      | "safe" => pure DefinitionSafety.safe
      | "unsafe" => pure DefinitionSafety.unsafe
      | "partial" => pure DefinitionSafety.partial
      | _ => .error "Invalid DefinitionSafety value"
    | _ => .error "Expected string value for DefinitionSafety"

structure DefinitionDataVal extends ConstantDataVal where
  value  : SerializedExpr
  valueKey : UInt64
  safety : DefinitionSafety
  all : List Name := [name]
  deriving Inhabited, BEq, ToJson, FromJson


structure TheoremDataVal extends ConstantDataVal where
  value : SerializedExpr
  valueKey : UInt64
  all : List Name := [name]
  deriving Inhabited, BEq, ToJson, FromJson

structure OpaqueDataVal extends ConstantDataVal where
  value : SerializedExpr
  valueKey : UInt64
  isUnsafe : Bool
  all : List Name := [name]
  deriving Inhabited, BEq, ToJson, FromJson


/-
inductive QuotKind where
  | type  -- `Quot`
  | ctor  -- `Quot.mk`
  | lift  -- `Quot.lift`
  | ind   -- `Quot.ind`
  deriving Inhabited
-/
instance : ToJson QuotKind where
  toJson
    | QuotKind.type => Json.str "type"
    | QuotKind.ctor => Json.str "ctor"
    | QuotKind.lift => Json.str "lift"
    | QuotKind.ind  => Json.str "ind"

instance : FromJson QuotKind where
  fromJson? json := match json with
    | Json.str s => match s with
      | "type" => pure QuotKind.type
      | "ctor" => pure QuotKind.ctor
      | "lift" => pure QuotKind.lift
      | "ind"  => pure QuotKind.ind
      | _ => .error "Invalid QuotKind value"
    | _ => .error "Expected string value for QuotKind"

instance : BEq QuotKind where
  beq k1 k2 := match (k1, k2) with
    | (QuotKind.type, QuotKind.type) => true
    | (QuotKind.ctor, QuotKind.ctor) => true
    | (QuotKind.lift, QuotKind.lift) => true
    | (QuotKind.ind, QuotKind.ind) => true
    | _ => false


structure QuotDataVal extends ConstantDataVal where
  kind : QuotKind
  deriving Inhabited, BEq, ToJson, FromJson

structure InductiveDataVal extends ConstantDataVal where
  numParams : Nat
  numIndices : Nat
  all : List Name
  ctors : List Name
  numNested : Nat
  isRec : Bool
  isUnsafe : Bool
  isReflexive : Bool
  deriving Inhabited, BEq, ToJson, FromJson

structure ConstructorDataVal extends ConstantDataVal where
  induct  : Name
  cidx    : Nat
  numParams : Nat
  numFields : Nat
  isUnsafe : Bool
  deriving Inhabited, BEq, ToJson, FromJson


/-
/-- Information for reducing a recursor -/
structure RecursorRule where
  /-- Reduction rule for this Constructor -/
  ctor : Name
  /-- Number of fields (i.e., without counting inductive datatype parameters) -/
  nfields : Nat
  /-- Right hand side of the reduction rule -/
  rhs : Expr
  deriving Inhabited, BEq
-/

structure SerializedRecursorRule where
  ctor : Name
  nfields : Nat
  rhs : SerializedExpr
  deriving Inhabited, BEq, ToJson, FromJson

structure RecursorDataVal extends ConstantDataVal where
  all : List Name
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : List SerializedRecursorRule
  k : Bool
  isUnsafe : Bool
  deriving Inhabited, BEq, ToJson, FromJson


inductive ConstantData where
  | axiomData  (ax : AxiomDataVal) : ConstantData
  | defnData   (defn : DefinitionDataVal) : ConstantData
  | thmData    (thm : TheoremDataVal) : ConstantData
  | opaqueData (op : OpaqueDataVal) : ConstantData
  | quotData   (quot : QuotDataVal)   : ConstantData
  | inductData (ind : InductiveDataVal) : ConstantData
  | ctorData   (ctor : ConstructorDataVal)   : ConstantData
  | recData    (rec : RecursorDataVal)     : ConstantData
  deriving Inhabited, BEq, ToJson, FromJson


namespace ConstantData
def fromConstantInfo (mod : Name) (ci : ConstantInfo) : ConstantData := match ci with
  | .axiomInfo ax => ConstantData.axiomData {
      name := ax.name,
      levelParams := ax.levelParams.map (normalizeNameForModule mod),
      type := ax.type.serialize,
      typeKey := exprKeyForModule mod ax.type,
      isUnsafe := ax.isUnsafe
    }
  | .defnInfo defn => ConstantData.defnData {
      name := defn.name,
      levelParams := defn.levelParams.map (normalizeNameForModule mod),
      type := defn.type.serialize,
      typeKey := exprKeyForModule mod defn.type,
      value := defn.value.serialize,
      valueKey := exprKeyForModule mod defn.value,
      safety := defn.safety
    }
  | .thmInfo thm => ConstantData.thmData {
      name := thm.name,
      levelParams := thm.levelParams.map (normalizeNameForModule mod),
      type := thm.type.serialize,
      typeKey := exprKeyForModule mod thm.type,
      value := thm.value.serialize,
      valueKey := exprKeyForModule mod thm.value
    }
  | .opaqueInfo op => ConstantData.opaqueData {
      name := op.name,
      levelParams := op.levelParams.map (normalizeNameForModule mod),
      type := op.type.serialize,
      typeKey := exprKeyForModule mod op.type,
      value := op.value.serialize,
      valueKey := exprKeyForModule mod op.value,
      isUnsafe := op.isUnsafe
    }
  | .quotInfo quot => ConstantData.quotData {
      name := quot.name,
      levelParams := quot.levelParams.map (normalizeNameForModule mod),
      type := quot.type.serialize,
      typeKey := exprKeyForModule mod quot.type,
      kind := match quot.kind with
        | QuotKind.type => QuotKind.type
        | QuotKind.ctor => QuotKind.ctor
        | QuotKind.lift => QuotKind.lift
        | QuotKind.ind  => QuotKind.ind
    }
  | .inductInfo ind => ConstantData.inductData {
      name := ind.name,
      levelParams := ind.levelParams.map (normalizeNameForModule mod),
      type := ind.type.serialize,
      typeKey := exprKeyForModule mod ind.type,
      numParams := ind.numParams,
      numIndices := ind.numIndices,
      all := ind.all
      ctors := ind.ctors
      numNested := ind.numNested,
      isRec := ind.isRec,
      isUnsafe := ind.isUnsafe,
      isReflexive := ind.isReflexive
    }
  | .ctorInfo ctor => ConstantData.ctorData {
      name := ctor.name,
      levelParams := ctor.levelParams.map (normalizeNameForModule mod),
      type := ctor.type.serialize,
      typeKey := exprKeyForModule mod ctor.type,
      induct  := ctor.induct,
      cidx    := ctor.cidx,
      numParams := ctor.numParams,
      numFields := ctor.numFields,
      isUnsafe := ctor.isUnsafe
    }
  | .recInfo rec => ConstantData.recData {
      name := rec.name,
      levelParams := rec.levelParams.map (normalizeNameForModule mod),
      type := rec.type.serialize,
      typeKey := exprKeyForModule mod rec.type,
      all := rec.all,
      numParams := rec.numParams,
      numIndices := rec.numIndices,
      numMotives := rec.numMotives,
      numMinors := rec.numMinors,
      rules := rec.rules.map (fun r => {
        ctor := r.ctor,
        nfields := r.nfields,
        rhs := r.rhs.serialize
      }),
      k := rec.k,
      isUnsafe := rec.isUnsafe
    }

  def kind (cd : ConstantData) : String := match cd with
  | .axiomData  _ => "axiom"
  | .defnData   _ => "def"
  | .thmData    _ => "theorem"
  | .opaqueData _ => "opaque"
  | .quotData   _ => "quot"
  | .inductData _ => "inductive"
  | .ctorData   _ => "constructor"
  | .recData    _ => "recursor"


  def toConstantDataVal : ConstantData → ConstantDataVal
  | .defnData     {toConstantDataVal := d, ..} => d
  | .axiomData    {toConstantDataVal := d, ..} => d
  | .thmData      {toConstantDataVal := d, ..} => d
  | .opaqueData   {toConstantDataVal := d, ..} => d
  | .quotData     {toConstantDataVal := d, ..} => d
  | .inductData   {toConstantDataVal := d, ..} => d
  | .ctorData     {toConstantDataVal := d, ..} => d
  | .recData      {toConstantDataVal := d, ..} => d

def isUnsafe : ConstantData → Bool
  | .defnData   v => v.safety == .unsafe
  | .axiomData  v => v.isUnsafe
  | .thmData    _ => false
  | .opaqueData v => v.isUnsafe
  | .quotData   _ => false
  | .inductData v => v.isUnsafe
  | .ctorData   v => v.isUnsafe
  | .recData    v => v.isUnsafe

def isPartial : ConstantData → Bool
  | .defnData v => v.safety == .partial
  | _ => false

def name (d : ConstantData) : Name :=
  d.toConstantDataVal.name

def levelParams (d : ConstantData) : List Name :=
  d.toConstantDataVal.levelParams


def numLevelParams (d : ConstantData) : Nat :=
  d.levelParams.length

def type (d : ConstantData) : SerializedExpr :=
  d.toConstantDataVal.type

def typeKey (d : ConstantData) : UInt64 :=
  d.toConstantDataVal.typeKey

def value? (info : ConstantData) (allowOpaque := false) : Option SerializedExpr :=
  match info with
  | .defnData {value, ..}   => some value
  | .thmData  {value, ..}   => some value
  | .opaqueData {value, ..} => if allowOpaque then some value else none
  | _                       => none

def valueKey? (info : ConstantData) (allowOpaque := false) : Option UInt64 :=
  match info with
  | .defnData {valueKey, ..}   => some valueKey
  | .thmData  {valueKey, ..}   => some valueKey
  | .opaqueData {valueKey, ..} => if allowOpaque then some valueKey else none
  | _                          => none


end ConstantData
