import MPC.Check

namespace MPC.Packages.Inductive.Prop

def isPropLevel (level : Level) : Bool :=
  level.defEq .zero

def requiresPropPackage (manifest : Manifest) : Result Unit := do
  if manifest.prop == .enabled then
    pure ()
  else
    fail "Prop inductives require the Prop package"

def checkPropInductiveEnabled (manifest : Manifest) : Result Unit := do
  requiresPropPackage manifest
  if manifest.supportsPropInductives then
    pure ()
  else
    fail "proposition-valued inductives are disabled by the manifest"

def extendBinders : Context → List Binder → Context
  | ctx, [] => ctx
  | ctx, binder :: rest => extendBinders (ctx.extend binder.name binder.type) rest

def fieldValueExpr (fieldCount fieldIndex : Nat) : Expr :=
  .bvar (fieldCount - 1 - fieldIndex)

def fieldForcedByTargetIndex (fieldCount fieldIndex : Nat) (targetIndices : List Expr) : Bool :=
  targetIndices.any fun index =>
    index.alphaEq (fieldValueExpr fieldCount fieldIndex)

partial def fieldsEligibleForLargeElim
    (manifest : Manifest)
    (env : Env)
    (levelParams : LevelContext)
    (targetIndices : List Expr)
    (fieldCount : Nat) :
    Nat → Context → List Binder → Result Bool
  | _, _, [] => pure true
  | fieldIndex, ctx, field :: rest => do
      let sort ← inferSort manifest env levelParams ctx field.type
      if sort.defEq .zero || fieldForcedByTargetIndex fieldCount fieldIndex targetIndices then
        fieldsEligibleForLargeElim manifest env levelParams targetIndices fieldCount
          (fieldIndex + 1) (ctx.extend field.name field.type) rest
      else
        pure false

def simpleLargeElimEligible
    (manifest : Manifest) (env : Env) (spec : SimpleInductiveSpec) : Result Bool := do
  if !manifest.supportsPropLargeElimination || !isPropLevel spec.resultLevel then
    pure false
  else
    let paramCtx := extendBinders [] spec.params
    spec.constructors.allM fun ctor =>
      fieldsEligibleForLargeElim manifest env spec.levelParams [] ctor.fields.length 0
        paramCtx ctor.fields

def indexedLargeElimEligible
    (manifest : Manifest) (env : Env) (spec : IndexedInductiveSpec) : Result Bool := do
  if !manifest.supportsPropLargeElimination || !isPropLevel spec.resultLevel then
    pure false
  else
    let paramCtx := extendBinders [] spec.params
    spec.constructors.allM fun ctor =>
      fieldsEligibleForLargeElim manifest env spec.levelParams ctor.targetIndices ctor.fields.length 0
        paramCtx ctor.fields

def recursorMotiveLevel (specResultLevel : Level) (largeElimEligible : Bool) : Level :=
  if isPropLevel specResultLevel && !largeElimEligible then .zero else .param "u"

def recursorLevelParams (motiveLevel : Level) (specLevelParams : LevelContext) : LevelContext :=
  if motiveLevel.defEq .zero then specLevelParams else "u" :: specLevelParams

end MPC.Packages.Inductive.Prop
