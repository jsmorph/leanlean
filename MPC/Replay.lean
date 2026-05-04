import MPC.Check

namespace MPC

def checkSimpleInductiveField
    (manifest : Manifest)
    (env : Env)
    (levelParams : LevelContext)
    (inductiveName : Name)
    (ctx : Context)
    (field : Binder) : Result Context := do
  let _ ← inferSort manifest env levelParams ctx field.type
  if simpleStrictlyPositive inductiveName field.type then
    pure (ctx.extend field.name field.type)
  else
    fail s!"field {field.name} is not strictly positive in {inductiveName}"

partial def checkSimpleInductiveFields
    (manifest : Manifest)
    (env : Env)
    (levelParams : LevelContext)
    (inductiveName : Name)
    (ctx : Context) : List Binder → Result Unit
  | [] => pure ()
  | field :: rest => do
      let ctx ← checkSimpleInductiveField manifest env levelParams inductiveName ctx field
      checkSimpleInductiveFields manifest env levelParams inductiveName ctx rest

def simpleInductiveType (spec : SimpleInductiveSpec) : Expr :=
  bindForall spec.params (.sort spec.resultLevel)

def simpleInductiveLevels (spec : SimpleInductiveSpec) : List Level :=
  spec.levelParams.map .param

def sourceOrderBvars (count offset : Nat) : List Expr :=
  (List.range count).map fun index =>
    .bvar (offset + count - 1 - index)

def simpleParamArgs (spec : SimpleInductiveSpec) (offset : Nat) : List Expr :=
  sourceOrderBvars spec.params.length offset

def simpleInductiveTargetAt (spec : SimpleInductiveSpec) (paramOffset : Nat) : Expr :=
  Expr.mkApps (.const spec.name (simpleInductiveLevels spec)) (simpleParamArgs spec paramOffset)

def simpleInductiveTarget (spec : SimpleInductiveSpec) : Expr :=
  simpleInductiveTargetAt spec 0

def simpleConstructorType (spec : SimpleInductiveSpec) (ctor : SimpleConstructorSpec) : Expr :=
  let target := simpleInductiveTargetAt spec ctor.fields.length
  bindForall (spec.params ++ ctor.fields) target

def simpleMotiveType (spec : SimpleInductiveSpec) : Expr :=
  .forallE "target" (simpleInductiveTarget spec) (.sort (.param "u"))

def simpleCtorAppFromFields (spec : SimpleInductiveSpec) (previousMinors : Nat)
    (ctor : SimpleConstructorSpec) : Expr :=
  let paramArgs := simpleParamArgs spec (ctor.fields.length + previousMinors + 1)
  let fieldArgs := sourceOrderBvars ctor.fields.length 0
  Expr.mkApps (.const ctor.name (simpleInductiveLevels spec)) (paramArgs ++ fieldArgs)

def liftFieldBindersForOuter (amount : Nat) : Nat → List Binder → List Binder
  | _, [] => []
  | boundFields, binder :: rest =>
      { binder with type := binder.type.liftFrom amount boundFields } ::
        liftFieldBindersForOuter amount (boundFields + 1) rest

def simpleMinorType (spec : SimpleInductiveSpec) (previousMinors : Nat)
    (ctor : SimpleConstructorSpec) : Expr :=
  let motiveIndex := ctor.fields.length + previousMinors
  let body := .app (.bvar motiveIndex) (simpleCtorAppFromFields spec previousMinors ctor)
  bindForall (liftFieldBindersForOuter (previousMinors + 1) 0 ctor.fields) body

def simpleRecursorName (spec : SimpleInductiveSpec) : Name :=
  spec.name ++ ".rec"

def enumerateFrom : List α → Nat → List (Nat × α)
  | [], _ => []
  | value :: rest, index => (index, value) :: enumerateFrom rest (index + 1)

def enumerate (values : List α) : List (Nat × α) :=
  enumerateFrom values 0

def simpleRecursorType (spec : SimpleInductiveSpec) : Expr :=
  let motive := { name := "motive", type := simpleMotiveType spec }
  let minorBinders :=
    enumerate spec.constructors |>.map fun pair =>
      {
        name := pair.2.name ++ ".minor"
        type := simpleMinorType spec pair.1 pair.2
      }
  let target := { name := "target", type := simpleInductiveTargetAt spec (minorBinders.length + 1) }
  let body := .app (.bvar (minorBinders.length + 1)) (.bvar 0)
  bindForall spec.params (bindForall (motive :: minorBinders ++ [target]) body)

def extendBinders : Context → List Binder → Context
  | ctx, [] => ctx
  | ctx, binder :: rest => extendBinders (ctx.extend binder.name binder.type) rest

def addSimpleInductive (manifest : Manifest) (env : Env) (spec : SimpleInductiveSpec) :
    Result Env := do
  Manifest.validate manifest
  if !manifest.supportsSimpleInductives then
    fail "simple inductives are disabled by the manifest"
  else if spec.resultLevel.defEq .zero then
    fail "the MPC PoC simple inductive package is data-only"
  else
    let _ ← inferSort manifest env spec.levelParams [] (.sort spec.resultLevel)
    let inductiveInfo : ConstantInfo :=
      {
        name := spec.name
        levelParams := spec.levelParams
        type := simpleInductiveType spec
        kind := .inductiveType spec
    }
    let env ← Env.add env inductiveInfo
    let paramCtx := extendBinders [] spec.params
    for ctor in spec.constructors do
      checkSimpleInductiveFields manifest env spec.levelParams spec.name paramCtx ctor.fields
    let mut env := env
    for pair in enumerate spec.constructors do
      let ctor := pair.2
      let type := simpleConstructorType spec ctor
      let _ ← inferSort manifest env spec.levelParams [] type
      env ← Env.add env
        {
          name := ctor.name
          levelParams := spec.levelParams
          type
          kind := .constructor spec.name pair.1 ctor.fields.length
        }
    let recursorLevelParams := "u" :: spec.levelParams
    let recursorType := simpleRecursorType spec
    let _ ← inferSort manifest env recursorLevelParams [] recursorType
    Env.add env
      {
        name := simpleRecursorName spec
        levelParams := recursorLevelParams
        type := recursorType
        kind :=
          .recursor
            {
              inductiveName := spec.name
              constructors := spec.constructors.map (fun ctor => (ctor.name, ctor.fields.length))
            }
      }

def addDecl (manifest : Manifest) (env : Env) : Declaration → Result Env
  | declaration => do
      Manifest.validate manifest
      match declaration with
      | .axiom name levelParams type => do
          let _ ← inferSort manifest env levelParams [] type
          Env.add env { name, levelParams, type, kind := .axiom }
      | .definition name levelParams type value => do
          let _ ← inferSort manifest env levelParams [] type
          check manifest env levelParams [] value type
          Env.add env { name, levelParams, type, value? := some value, kind := .definition }
      | .opaque name levelParams type value => do
          let _ ← inferSort manifest env levelParams [] type
          check manifest env levelParams [] value type
          Env.add env { name, levelParams, type, value? := some value, kind := .opaque }
      | .theorem name levelParams type value => do
          isPropExpr manifest env levelParams [] type
          check manifest env levelParams [] value type
          Env.add env { name, levelParams, type, value? := some value, kind := .theorem }
      | .inductive spec =>
          addSimpleInductive manifest env spec
      | .indexedInductive _ =>
          fail "indexed inductives are not implemented yet"

def replay (manifest : Manifest) : Env → List Declaration → Result Env
  | env, [] => pure env
  | env, decl :: rest => do
      let env ← addDecl manifest env decl
      replay manifest env rest

end MPC
