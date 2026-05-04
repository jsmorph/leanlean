import MPC.Packages.Equality

namespace MPC.Packages.Quotient

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

def eqApp (level : Level) (type left right : Expr) : Expr :=
  MPC.Packages.Equality.eqApp level type left right

def quotApp (level : Level) (type relation : Expr) : Expr :=
  Expr.mkApps (.const "Quot" [level]) [type, relation]

def quotMkApp (level : Level) (type relation value : Expr) : Expr :=
  Expr.mkApps (.const "Quot.mk" [level]) [type, relation, value]

def relationTypeForAlpha0 : Expr :=
  .forallE "a" (.bvar 0) (.forallE "b" (.bvar 1) prop)

def alphaBinder : Binder :=
  { name := "alpha", type := sortU }

def betaBinder : Binder :=
  { name := "beta", type := sortV }

def relationBinder : Binder :=
  { name := "r", type := relationTypeForAlpha0 }

def quotType : Expr :=
  bindForall [alphaBinder, relationBinder] sortU

def quotMkType : Expr :=
  bindForall
    [
      alphaBinder,
      relationBinder,
      { name := "value", type := .bvar 1 }
    ]
    (quotApp u (.bvar 2) (.bvar 1))

def functionTypeAlphaToBeta : Expr :=
  .forallE "a" (.bvar 2) (.bvar 1)

def liftRespectfulType : Expr :=
  .forallE "a" (.bvar 3)
    (.forallE "b" (.bvar 4)
      (.forallE "rel" (Expr.mkApps (.bvar 4) [.bvar 1, .bvar 0])
        (eqApp v
          (.bvar 4)
          (.app (.bvar 3) (.bvar 2))
          (.app (.bvar 3) (.bvar 1)))))

def quotLiftType : Expr :=
  bindForall
    [
      alphaBinder,
      relationBinder,
      betaBinder,
      { name := "f", type := functionTypeAlphaToBeta },
      { name := "respect", type := liftRespectfulType },
      { name := "q", type := quotApp u (.bvar 4) (.bvar 3) }
    ]
    (.bvar 3)

def quotientMotiveType : Expr :=
  .forallE "q" (quotApp u (.bvar 1) (.bvar 0)) prop

def quotientIndMinorType : Expr :=
  .forallE "a" (.bvar 2) (.app (.bvar 1) (quotMkApp u (.bvar 3) (.bvar 2) (.bvar 0)))

def quotIndType : Expr :=
  bindForall
    [
      alphaBinder,
      relationBinder,
      { name := "motive", type := quotientMotiveType },
      { name := "mkCase", type := quotientIndMinorType },
      { name := "q", type := quotApp u (.bvar 3) (.bvar 2) }
    ]
    (.app (.bvar 2) (.bvar 0))

def quotSoundType : Expr :=
  bindForall
    [
      alphaBinder,
      relationBinder,
      { name := "a", type := .bvar 1 },
      { name := "b", type := .bvar 2 },
      { name := "rel", type := Expr.mkApps (.bvar 2) [.bvar 1, .bvar 0] }
    ]
    (eqApp u
      (quotApp u (.bvar 4) (.bvar 3))
      (quotMkApp u (.bvar 4) (.bvar 3) (.bvar 2))
      (quotMkApp u (.bvar 4) (.bvar 3) (.bvar 1)))

def primitiveInfos : List ConstantInfo :=
  [
    { name := "Quot", levelParams := ["u"], type := quotType, kind := .quotientType },
    { name := "Quot.mk", levelParams := ["u"], type := quotMkType, kind := .quotientMk },
    { name := "Quot.lift", levelParams := ["u", "v"], type := quotLiftType, kind := .quotientLift },
    { name := "Quot.ind", levelParams := ["u"], type := quotIndType, kind := .quotientInd },
    { name := "Quot.sound", levelParams := ["u"], type := quotSoundType, kind := .quotientSound }
  ]

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

def addQuotientPrimitives (manifest : Manifest) (env : Env) : Result Env := do
  Manifest.validate manifest
  if !manifest.supportsQuotients then
    fail "quotient primitives are disabled by the manifest"
  else if manifest.prop != .enabled then
    fail "quotient primitives require Prop"
  else if !MPC.Packages.Equality.hasPrimitives env then
    fail "quotient primitives require equality primitives"
  else
    addPrimitives manifest env primitiveInfos

end MPC.Packages.Quotient
