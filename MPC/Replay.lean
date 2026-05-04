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

def indexedInductiveLevels (spec : IndexedInductiveSpec) : List Level :=
  spec.levelParams.map .param

def indexedParamArgs (spec : IndexedInductiveSpec) (offset : Nat) : List Expr :=
  sourceOrderBvars spec.params.length offset

def indexedTargetAt (spec : IndexedInductiveSpec) (paramOffset : Nat) (indices : List Expr) :
    Expr :=
  Expr.mkApps (.const spec.name (indexedInductiveLevels spec))
    (indexedParamArgs spec paramOffset ++ indices)

def indexedInductiveType (spec : IndexedInductiveSpec) : Expr :=
  bindForall spec.params (bindForall spec.indices (.sort spec.resultLevel))

def indexedConstructorType (spec : IndexedInductiveSpec) (ctor : IndexedConstructorSpec) :
    Expr :=
  let target := indexedTargetAt spec ctor.fields.length ctor.targetIndices
  bindForall (spec.params ++ ctor.fields) target

def indexedMotiveType (spec : IndexedInductiveSpec) : Expr :=
  let indexArgs := sourceOrderBvars spec.indices.length 0
  let targetType := indexedTargetAt spec spec.indices.length indexArgs
  bindForall spec.indices (.forallE "target" targetType (.sort (.param "u")))

def indexedRecursorName (spec : IndexedInductiveSpec) : Name :=
  spec.name ++ ".rec"

def fieldTypeUnderAllFields (fieldCount fieldIndex : Nat) (type : Expr) : Expr :=
  type.liftFrom (fieldCount - fieldIndex) 0

def directIndexedRecursiveField? (spec : IndexedInductiveSpec) (fieldCount fieldIndex : Nat)
    (field : Binder) : Option IndexedRecursiveFieldInfo :=
  let type := fieldTypeUnderAllFields fieldCount fieldIndex field.type
  let (head, args) := type.getAppFnArgs
  match head with
  | .const name levels =>
      if name == spec.name &&
          levels.length == spec.levelParams.length &&
          args.length == spec.params.length + spec.indices.length then
        some
          {
            fieldIndex
            indices := args.drop spec.params.length
          }
      else
        none
  | _ => none

def indexedRecursiveFields (spec : IndexedInductiveSpec) (ctor : IndexedConstructorSpec) :
    List IndexedRecursiveFieldInfo :=
  enumerate ctor.fields |>.filterMap fun pair =>
    directIndexedRecursiveField? spec ctor.fields.length pair.1 pair.2

def indexedMotiveApp (motive : Expr) (indices : List Expr) (target : Expr) : Expr :=
  Expr.mkApps motive (indices ++ [target])

def indexedCtorAppFromFields (spec : IndexedInductiveSpec) (previousMinors : Nat)
    (recursiveCount : Nat) (ctor : IndexedConstructorSpec) : Expr :=
  let paramArgs := indexedParamArgs spec (ctor.fields.length + recursiveCount + previousMinors + 1)
  let fieldArgs := sourceOrderBvars ctor.fields.length recursiveCount
  Expr.mkApps (.const ctor.name (indexedInductiveLevels spec)) (paramArgs ++ fieldArgs)

def liftIndexExprForMinor (fieldCount previousMinors recursiveCount : Nat) (expr : Expr) :
    Expr :=
  (expr.liftFrom (previousMinors + 1) fieldCount).liftFrom recursiveCount 0

def indexedRecursiveHypothesisType (previousMinors fieldCount recursiveIndex : Nat)
    (rec : IndexedRecursiveFieldInfo) : Expr :=
  let indices :=
    rec.indices.map fun index =>
      liftIndexExprForMinor fieldCount previousMinors recursiveIndex index
  let motive := .bvar (fieldCount + recursiveIndex + previousMinors)
  let fieldValue := .bvar (recursiveIndex + fieldCount - 1 - rec.fieldIndex)
  indexedMotiveApp motive indices fieldValue

def indexedRecursiveHypothesisBinders (previousMinors fieldCount : Nat)
    (recFields : List IndexedRecursiveFieldInfo) : List Binder :=
  enumerate recFields |>.map fun pair =>
    {
      name := s!"ih{pair.2.fieldIndex}"
      type := indexedRecursiveHypothesisType previousMinors fieldCount pair.1 pair.2
    }

def indexedMinorType (spec : IndexedInductiveSpec) (previousMinors : Nat)
    (ctor : IndexedConstructorSpec) (recFields : List IndexedRecursiveFieldInfo) : Expr :=
  let fieldCount := ctor.fields.length
  let recursiveCount := recFields.length
  let fieldBinders := liftFieldBindersForOuter (previousMinors + 1) 0 ctor.fields
  let recursiveBinders := indexedRecursiveHypothesisBinders previousMinors fieldCount recFields
  let targetIndices :=
    ctor.targetIndices.map fun index =>
      liftIndexExprForMinor fieldCount previousMinors recursiveCount index
  let ctorApp := indexedCtorAppFromFields spec previousMinors recursiveCount ctor
  let motive := .bvar (fieldCount + recursiveCount + previousMinors)
  bindForall (fieldBinders ++ recursiveBinders) (indexedMotiveApp motive targetIndices ctorApp)

def indexedRecursorConstructorInfo (spec : IndexedInductiveSpec)
    (ctor : IndexedConstructorSpec) : IndexedRecursorConstructorInfo :=
  {
    name := ctor.name
    fieldCount := ctor.fields.length
    recursiveFields := indexedRecursiveFields spec ctor
  }

def indexedRecursorType (spec : IndexedInductiveSpec)
    (ctorInfos : List IndexedRecursorConstructorInfo) : Expr :=
  let motive := { name := "motive", type := indexedMotiveType spec }
  let minorBinders :=
    (enumerate spec.constructors).zip ctorInfos |>.map fun pair =>
      {
        name := pair.1.2.name ++ ".minor"
        type := indexedMinorType spec pair.1.1 pair.1.2 pair.2.recursiveFields
      }
  let indexBinders := liftFieldBindersForOuter (minorBinders.length + 1) 0 spec.indices
  let targetIndexArgs := sourceOrderBvars spec.indices.length 0
  let targetType :=
    indexedTargetAt spec (spec.indices.length + minorBinders.length + 1) targetIndexArgs
  let target := { name := "target", type := targetType }
  let bodyIndexArgs := sourceOrderBvars spec.indices.length 1
  let motiveExpr := .bvar (spec.indices.length + 1 + minorBinders.length)
  let body := indexedMotiveApp motiveExpr bodyIndexArgs (.bvar 0)
  bindForall spec.params (bindForall (motive :: minorBinders ++ indexBinders ++ [target]) body)

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

def checkIndexedConstructor
    (manifest : Manifest)
    (env : Env)
    (spec : IndexedInductiveSpec)
    (paramCtx : Context)
    (ctor : IndexedConstructorSpec) : Result Unit := do
  if ctor.targetIndices.length != spec.indices.length then
    fail s!"constructor {ctor.name} has wrong number of target indices"
  checkSimpleInductiveFields manifest env spec.levelParams spec.name paramCtx ctor.fields
  let _ ← inferSort manifest env spec.levelParams [] (indexedConstructorType spec ctor)
  pure ()

def addIndexedInductive (manifest : Manifest) (env : Env) (spec : IndexedInductiveSpec) :
    Result Env := do
  Manifest.validate manifest
  if !manifest.supportsIndexedInductives then
    fail "indexed inductives are disabled by the manifest"
  else if spec.resultLevel.defEq .zero then
    fail "the MPC indexed inductive package is data-only"
  else
    let _ ← inferSort manifest env spec.levelParams [] (indexedInductiveType spec)
    let inductiveInfo : ConstantInfo :=
      {
        name := spec.name
        levelParams := spec.levelParams
        type := indexedInductiveType spec
        kind := .indexedInductiveType spec
      }
    let env ← Env.add env inductiveInfo
    let paramCtx := extendBinders [] spec.params
    for ctor in spec.constructors do
      checkIndexedConstructor manifest env spec paramCtx ctor
    let mut env := env
    for pair in enumerate spec.constructors do
      let ctor := pair.2
      env ← Env.add env
        {
          name := ctor.name
          levelParams := spec.levelParams
          type := indexedConstructorType spec ctor
          kind := .constructor spec.name pair.1 ctor.fields.length
        }
    let ctorInfos := spec.constructors.map (indexedRecursorConstructorInfo spec)
    let recursorLevelParams := "u" :: spec.levelParams
    let recursorType := indexedRecursorType spec ctorInfos
    let _ ← inferSort manifest env recursorLevelParams [] recursorType
    Env.add env
      {
        name := indexedRecursorName spec
        levelParams := recursorLevelParams
        type := recursorType
        kind :=
          .indexedRecursor
            {
              inductiveName := spec.name
              constructors := ctorInfos
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
      | .indexedInductive spec =>
          addIndexedInductive manifest env spec
      | .quotientPrimitives =>
          fail "quotient primitives are not implemented yet"

def replay (manifest : Manifest) : Env → List Declaration → Result Env
  | env, [] => pure env
  | env, decl :: rest => do
      let env ← addDecl manifest env decl
      replay manifest env rest

end MPC
