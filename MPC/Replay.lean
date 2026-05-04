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

def simpleInductiveTarget (spec : SimpleInductiveSpec) : Expr :=
  Expr.mkApps (.const spec.name (simpleInductiveLevels spec)) []

def simpleConstructorType (spec : SimpleInductiveSpec) (ctor : SimpleConstructorSpec) : Expr :=
  bindForall ctor.fields (simpleInductiveTarget spec)

def simpleMotiveType (spec : SimpleInductiveSpec) : Expr :=
  .forallE "target" (simpleInductiveTarget spec) (.sort (.param "u"))

def simpleCtorAppFromFields (spec : SimpleInductiveSpec) (ctor : SimpleConstructorSpec) : Expr :=
  let fieldArgs :=
    (List.range ctor.fields.length).map fun index =>
      .bvar (ctor.fields.length - 1 - index)
  Expr.mkApps (.const ctor.name (simpleInductiveLevels spec)) fieldArgs

def simpleMinorType (spec : SimpleInductiveSpec) (previousMinors : Nat)
    (ctor : SimpleConstructorSpec) : Expr :=
  let motiveIndex := ctor.fields.length + previousMinors
  let body := .app (.bvar motiveIndex) (simpleCtorAppFromFields spec ctor)
  bindForall ctor.fields body

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
  let target := { name := "target", type := simpleInductiveTarget spec }
  let body := .app (.bvar (minorBinders.length + 1)) (.bvar 0)
  bindForall (motive :: minorBinders ++ [target]) body

def addSimpleInductive (manifest : Manifest) (env : Env) (spec : SimpleInductiveSpec) :
    Result Env := do
  if manifest.inductives != .simple then
    fail "simple inductives are disabled by the manifest"
  else if !spec.params.isEmpty then
    fail "the MPC PoC simple inductive package does not support parameters yet"
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
    for ctor in spec.constructors do
      checkSimpleInductiveFields manifest env spec.levelParams spec.name [] ctor.fields
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

def replay (manifest : Manifest) : Env → List Declaration → Result Env
  | env, [] => pure env
  | env, decl :: rest => do
      let env ← addDecl manifest env decl
      replay manifest env rest

end MPC
