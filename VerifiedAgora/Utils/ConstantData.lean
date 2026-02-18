import Lean

open Lean Core Elab IO Meta Term Command Tactic Environment

abbrev SerializedExpr := String
def Lean.Expr.serialize (e : Expr) (env : Environment) : IO SerializedExpr := do
  let ctx := { fileName := "", fileMap := default }
  let pp ← Prod.fst <$> (CoreM.toIO (MetaM.run' do ppExpr e) ctx {env:=env})
  pure pp.pretty


structure ConstantDataVal where
  name : Name
  levelParams : List Name
  type : SerializedExpr
  deriving Inhabited, BEq, ToJson, FromJson, Hashable

structure AxiomDataVal extends ConstantDataVal where
  isUnsafe : Bool
  deriving Inhabited, BEq, ToJson, FromJson, Hashable


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

instance : Hashable DefinitionSafety where
  hash s := match s with
    | DefinitionSafety.safe => 0
    | DefinitionSafety.unsafe => 1
    | DefinitionSafety.partial => 2

structure DefinitionDataVal extends ConstantDataVal where
  value  : SerializedExpr
  safety : DefinitionSafety
  all : List Name := [name]
  deriving Inhabited, BEq, ToJson, FromJson, Hashable


structure TheoremDataVal extends ConstantDataVal where
  value : SerializedExpr
  all : List Name := [name]
  deriving Inhabited, BEq, ToJson, FromJson, Hashable

structure OpaqueDataVal extends ConstantDataVal where
  value : SerializedExpr
  isUnsafe : Bool
  all : List Name := [name]
  deriving Inhabited, BEq, ToJson, FromJson, Hashable


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

instance : Hashable QuotKind where
  hash k := match k with
    | QuotKind.type => 0
    | QuotKind.ctor => 1
    | QuotKind.lift => 2
    | QuotKind.ind  => 3

structure QuotDataVal extends ConstantDataVal where
  kind : QuotKind
  deriving Inhabited, BEq, ToJson, FromJson, Hashable

structure InductiveDataVal extends ConstantDataVal where
  numParams : Nat
  numIndices : Nat
  all : List Name
  ctors : List Name
  numNested : Nat
  isRec : Bool
  isUnsafe : Bool
  isReflexive : Bool
  deriving Inhabited, BEq, ToJson, FromJson, Hashable

structure ConstructorDataVal extends ConstantDataVal where
  induct  : Name
  cidx    : Nat
  numParams : Nat
  numFields : Nat
  isUnsafe : Bool
  deriving Inhabited, BEq, ToJson, FromJson, Hashable


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
  deriving Inhabited, BEq, ToJson, FromJson, Hashable

structure RecursorDataVal extends ConstantDataVal where
  all : List Name
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : List SerializedRecursorRule
  k : Bool
  isUnsafe : Bool
  deriving Inhabited, BEq, ToJson, FromJson, Hashable


inductive ConstantData where
  | axiomData  (ax : AxiomDataVal) : ConstantData
  | defnData   (defn : DefinitionDataVal) : ConstantData
  | thmData    (thm : TheoremDataVal) : ConstantData
  | opaqueData (op : OpaqueDataVal) : ConstantData
  | quotData   (quot : QuotDataVal)   : ConstantData
  | inductData (ind : InductiveDataVal) : ConstantData
  | ctorData   (ctor : ConstructorDataVal)   : ConstantData
  | recData    (rec : RecursorDataVal)     : ConstantData
  deriving Inhabited, BEq, ToJson, FromJson, Hashable


namespace ConstantData
def fromConstantInfo (ci : ConstantInfo) (env : Environment): IO ConstantData := do match ci with
  | .axiomInfo ax => pure <|  ConstantData.axiomData {
      name := ax.name,
      levelParams := ax.levelParams
      type := ← ax.type.serialize env,
      isUnsafe := ax.isUnsafe
    }
  | .defnInfo defn => pure <| ConstantData.defnData {
      name := defn.name,
      levelParams := defn.levelParams,
      type := ← defn.type.serialize env,
      value := ← defn.value.serialize env,
      safety := defn.safety
    }
  | .thmInfo thm => pure <| ConstantData.thmData {
      name := thm.name,
      levelParams := thm.levelParams,
      type := ← thm.type.serialize env,
      value := ← thm.value.serialize env,
    }
  | .opaqueInfo op => pure <| ConstantData.opaqueData {
      name := op.name,
      levelParams := op.levelParams,
      type := ← op.type.serialize env,
      value := ← op.value.serialize env,
      isUnsafe := op.isUnsafe
    }
  | .quotInfo quot => pure <| ConstantData.quotData {
      name := quot.name,
      levelParams := quot.levelParams,
      type := ← quot.type.serialize env,
      kind := match quot.kind with
        | QuotKind.type => QuotKind.type
        | QuotKind.ctor => QuotKind.ctor
        | QuotKind.lift => QuotKind.lift
        | QuotKind.ind  => QuotKind.ind
    }
  | .inductInfo ind => pure <| ConstantData.inductData {
      name := ind.name,
      levelParams := ind.levelParams,
      type := ← ind.type.serialize env,
      numParams := ind.numParams,
      numIndices := ind.numIndices,
      all := ind.all
      ctors := ind.ctors
      numNested := ind.numNested,
      isRec := ind.isRec,
      isUnsafe := ind.isUnsafe,
      isReflexive := ind.isReflexive
    }
  | .ctorInfo ctor => pure <| ConstantData.ctorData {
      name := ctor.name,
      levelParams := ctor.levelParams,
      type := ← ctor.type.serialize env,
      induct  := ctor.induct,
      cidx    := ctor.cidx,
      numParams := ctor.numParams,
      numFields := ctor.numFields,
      isUnsafe := ctor.isUnsafe
    }
  | .recInfo rec => pure <| ConstantData.recData {
      name := rec.name,
      levelParams := rec.levelParams,
      type := ← rec.type.serialize env,
      all := rec.all,
      numParams := rec.numParams,
      numIndices := rec.numIndices,
      numMotives := rec.numMotives,
      numMinors := rec.numMinors,
      rules := ← rec.rules.mapM (fun r => do
      let rhs ← r.rhs.serialize env
      pure {
        ctor := r.ctor,
        nfields := r.nfields,
        rhs := rhs
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

def value? (info : ConstantData) (allowOpaque := false) : Option SerializedExpr :=
  match info with
  | .defnData {value, ..}   => some value
  | .thmData  {value, ..}   => some value
  | .opaqueData {value, ..} => if allowOpaque then some value else none
  | _                       => none


end ConstantData
