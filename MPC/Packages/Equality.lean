import MPC.Check

namespace MPC.Packages.Equality

open MPC

def u : Level :=
  .param "u"

def v : Level :=
  .param "v"

def sortU : Expr :=
  .sort u

def sortV : Expr :=
  .sort v

def prop : Expr :=
  .sort .zero

def alphaBinder : Binder :=
  { name := "alpha", type := sortU }

def eqApp (level : Level) (type left right : Expr) : Expr :=
  Expr.mkApps (.const "Eq" [level]) [type, left, right]

def eqReflApp (level : Level) (type value : Expr) : Expr :=
  Expr.mkApps (.const "Eq.refl" [level]) [type, value]

def eqType : Expr :=
  bindForall
    [alphaBinder, { name := "left", type := .bvar 0 }, { name := "right", type := .bvar 1 }]
    prop

def eqReflType : Expr :=
  bindForall
    [alphaBinder, { name := "value", type := .bvar 0 }]
    (eqApp u (.bvar 1) (.bvar 0) (.bvar 0))

def eqRecMotiveType : Expr :=
  .forallE "b" (.bvar 1)
    (.forallE "h" (eqApp u (.bvar 2) (.bvar 1) (.bvar 0)) sortV)

def eqRecMinorType : Expr :=
  Expr.mkApps (.bvar 0) [.bvar 1, eqReflApp u (.bvar 2) (.bvar 1)]

def eqRecProofType : Expr :=
  eqApp u (.bvar 4) (.bvar 3) (.bvar 0)

def eqRecType : Expr :=
  bindForall
    [
      alphaBinder,
      { name := "a", type := .bvar 0 },
      { name := "motive", type := eqRecMotiveType },
      { name := "minor", type := eqRecMinorType },
      { name := "b", type := .bvar 3 },
      { name := "h", type := eqRecProofType }
    ]
    (Expr.mkApps (.bvar 3) [.bvar 1, .bvar 0])

def eqNdRecMotiveType : Expr :=
  .forallE "b" (.bvar 1) sortV

def eqNdRecMinorType : Expr :=
  .app (.bvar 0) (.bvar 1)

def eqNdRecType : Expr :=
  bindForall
    [
      alphaBinder,
      { name := "a", type := .bvar 0 },
      { name := "motive", type := eqNdRecMotiveType },
      { name := "minor", type := eqNdRecMinorType },
      { name := "b", type := .bvar 3 },
      { name := "h", type := eqRecProofType }
    ]
    (.app (.bvar 3) (.bvar 1))

def primitiveInfos : List ConstantInfo :=
  [
    { name := "Eq", levelParams := ["u"], type := eqType, kind := .equalityType },
    { name := "Eq.refl", levelParams := ["u"], type := eqReflType, kind := .equalityRefl },
    { name := "Eq.rec", levelParams := ["v", "u"], type := eqRecType, kind := .equalityRec },
    { name := "Eq.ndrec", levelParams := ["v", "u"], type := eqNdRecType, kind := .equalityNdRec }
  ]

def hasPrimitiveInfo (env : Env) (info : ConstantInfo) : Bool :=
  match env.find? info.name with
  | some found => found.kind == info.kind
  | none => false

def hasPrimitives (env : Env) : Bool :=
  primitiveInfos.all (hasPrimitiveInfo env)

def addPrimitiveInfo (manifest : Manifest) (env : Env) (info : ConstantInfo) : Result Env := do
  match inferSort manifest env info.levelParams [] info.type with
  | .ok _ => pure ()
  | .error error => fail s!"primitive {info.name}: {error.message}"
  Env.add env info

def addPrimitives (manifest : Manifest) : Env → List ConstantInfo → Result Env
  | env, [] => pure env
  | env, info :: rest => do
      let env ← addPrimitiveInfo manifest env info
      addPrimitives manifest env rest

def addEqualityPrimitives (manifest : Manifest) (env : Env) : Result Env := do
  Manifest.validate manifest
  if !manifest.supportsEquality then
    fail "equality primitives are disabled by the manifest"
  else if manifest.prop != .enabled then
    fail "equality primitives require Prop"
  else
    addPrimitives manifest env primitiveInfos

end MPC.Packages.Equality
