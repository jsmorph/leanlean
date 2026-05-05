import MPC.Check
import MPC.Packages.Inductive.Prop
import MPC.Packages.Equality
import MPC.Packages.Quotient

namespace MPC

def checkSimpleInductiveField
    (manifest : Manifest)
    (env : Env)
    (levelParams : LevelContext)
    (inductiveName : Name)
    (ctx : Context)
    (field : Binder) : Result Context := do
  let _ ← inferSort manifest env levelParams ctx field.type
  if simpleStrictlyPositive manifest env inductiveName field.type then
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

def simpleMotiveType (spec : SimpleInductiveSpec) (motiveLevel : Level) : Expr :=
  .forallE "target" (simpleInductiveTarget spec) (.sort motiveLevel)

def simpleCtorAppFromFields (spec : SimpleInductiveSpec) (previousMinors recursiveCount : Nat)
    (ctor : SimpleConstructorSpec) : Expr :=
  let paramArgs := simpleParamArgs spec (ctor.fields.length + recursiveCount + previousMinors + 1)
  let fieldArgs := sourceOrderBvars ctor.fields.length recursiveCount
  Expr.mkApps (.const ctor.name (simpleInductiveLevels spec)) (paramArgs ++ fieldArgs)

def liftFieldBindersForOuter (amount : Nat) : Nat → List Binder → List Binder
  | _, [] => []
  | boundFields, binder :: rest =>
      { binder with type := binder.type.liftFrom amount boundFields } ::
        liftFieldBindersForOuter amount (boundFields + 1) rest

def simpleRecursorName (spec : SimpleInductiveSpec) : Name :=
  spec.name ++ ".rec"

def enumerateFrom : List α → Nat → List (Nat × α)
  | [], _ => []
  | value :: rest, index => (index, value) :: enumerateFrom rest (index + 1)

def enumerate (values : List α) : List (Nat × α) :=
  enumerateFrom values 0

def fieldTypeUnderAllFields (fieldCount fieldIndex : Nat) (type : Expr) : Expr :=
  type.liftFrom (fieldCount - fieldIndex) 0

def simpleDirectRecursiveField? (spec : SimpleInductiveSpec) (fieldCount fieldIndex : Nat)
    (field : Binder) : Option SimpleRecursiveFieldInfo :=
  let type := fieldTypeUnderAllFields fieldCount fieldIndex field.type
  let (head, args) := type.getAppFnArgs
  match head with
  | .const name levels =>
      let expectedArgs := simpleParamArgs spec fieldCount
      if name == spec.name &&
          levels.length == spec.levelParams.length &&
          args.length == spec.params.length &&
          (args.zip expectedArgs).all (fun pair => pair.1.alphaEq pair.2) then
        some { fieldIndex }
      else
        none
  | _ => none

def simpleRecursiveFields (spec : SimpleInductiveSpec) (ctor : SimpleConstructorSpec) :
    List SimpleRecursiveFieldInfo :=
  enumerate ctor.fields |>.filterMap fun pair =>
    simpleDirectRecursiveField? spec ctor.fields.length pair.1 pair.2

def simpleRecursiveHypothesisType (previousMinors fieldCount recursiveIndex : Nat)
    (rec : SimpleRecursiveFieldInfo) : Expr :=
  let motive := .bvar (fieldCount + recursiveIndex + previousMinors)
  let fieldValue := .bvar (recursiveIndex + fieldCount - 1 - rec.fieldIndex)
  .app motive fieldValue

def simpleRecursiveHypothesisBinders (previousMinors fieldCount : Nat)
    (recFields : List SimpleRecursiveFieldInfo) : List Binder :=
  enumerate recFields |>.map fun pair =>
    {
      name := s!"ih{pair.2.fieldIndex}"
      type := simpleRecursiveHypothesisType previousMinors fieldCount pair.1 pair.2
    }

def simpleMinorType (spec : SimpleInductiveSpec) (previousMinors : Nat)
    (ctor : SimpleConstructorSpec) (recFields : List SimpleRecursiveFieldInfo) : Expr :=
  let fieldCount := ctor.fields.length
  let recursiveCount := recFields.length
  let fieldBinders := liftFieldBindersForOuter (previousMinors + 1) 0 ctor.fields
  let recursiveBinders := simpleRecursiveHypothesisBinders previousMinors fieldCount recFields
  let motiveIndex := fieldCount + recursiveCount + previousMinors
  let body := .app (.bvar motiveIndex) (simpleCtorAppFromFields spec previousMinors recursiveCount ctor)
  bindForall (fieldBinders ++ recursiveBinders) body

def simpleRecursorConstructorInfo (spec : SimpleInductiveSpec)
    (ctor : SimpleConstructorSpec) : SimpleRecursorConstructorInfo :=
  {
    name := ctor.name
    fieldCount := ctor.fields.length
    recursiveFields := simpleRecursiveFields spec ctor
  }

def simpleRecursorType (spec : SimpleInductiveSpec) (motiveLevel : Level) : Expr :=
  let motive := { name := "motive", type := simpleMotiveType spec motiveLevel }
  let ctorInfos := spec.constructors.map (simpleRecursorConstructorInfo spec)
  let minorBinders :=
    (enumerate spec.constructors).zip ctorInfos |>.map fun pair =>
      {
        name := pair.1.2.name ++ ".minor"
        type := simpleMinorType spec pair.1.1 pair.1.2 pair.2.recursiveFields
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

def indexedMotiveType (spec : IndexedInductiveSpec) (motiveLevel : Level) : Expr :=
  let indexArgs := sourceOrderBvars spec.indices.length 0
  let targetType := indexedTargetAt spec spec.indices.length indexArgs
  bindForall spec.indices (.forallE "target" targetType (.sort motiveLevel))

def indexedRecursorName (spec : IndexedInductiveSpec) : Name :=
  spec.name ++ ".rec"

partial def indexedRecursiveFieldInType? (spec : IndexedInductiveSpec) (fieldIndex : Nat)
    (binders : List Binder) (type : Expr) : Option IndexedRecursiveFieldInfo :=
  let (head, args) := type.getAppFnArgs
  match head with
  | .const name levels =>
      if name == spec.name &&
          levels.length == spec.levelParams.length &&
          args.length == spec.params.length + spec.indices.length then
        some
          {
            fieldIndex
            binders
            indices := args.drop spec.params.length
          }
      else
        none
  | .forallE name domain body =>
      indexedRecursiveFieldInType? spec fieldIndex (binders ++ [{ name, type := domain }]) body
  | _ => none

def indexedRecursiveField? (spec : IndexedInductiveSpec) (fieldCount fieldIndex : Nat)
    (field : Binder) : Option IndexedRecursiveFieldInfo :=
  indexedRecursiveFieldInType? spec fieldIndex []
    (fieldTypeUnderAllFields fieldCount fieldIndex field.type)

def indexedRecursiveFields (spec : IndexedInductiveSpec) (ctor : IndexedConstructorSpec) :
    List IndexedRecursiveFieldInfo :=
  enumerate ctor.fields |>.filterMap fun pair =>
    indexedRecursiveField? spec ctor.fields.length pair.1 pair.2

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

def liftRecursiveFieldExprForMinor (fieldCount previousMinors recursiveIndex localCount : Nat)
    (expr : Expr) : Expr :=
  (expr.liftFrom (previousMinors + 1) (localCount + fieldCount)).liftFrom recursiveIndex localCount

def recursiveFieldLocalArgs (localCount : Nat) : List Expr :=
  sourceOrderBvars localCount 0

def recursiveFieldValue (fieldCount recursiveIndex localCount fieldIndex : Nat) : Expr :=
  .bvar (localCount + recursiveIndex + fieldCount - 1 - fieldIndex)

def recursiveFieldTarget (fieldCount recursiveIndex : Nat) (rec : IndexedRecursiveFieldInfo) : Expr :=
  let localCount := rec.binders.length
  Expr.mkApps
    (recursiveFieldValue fieldCount recursiveIndex localCount rec.fieldIndex)
    (recursiveFieldLocalArgs localCount)

partial def liftRecursiveFieldBindersForMinor
    (fieldCount previousMinors recursiveIndex : Nat) :
    Nat → List Binder → List Binder
  | _, [] => []
  | localCount, binder :: rest =>
      {
        binder with
        type := liftRecursiveFieldExprForMinor fieldCount previousMinors recursiveIndex localCount binder.type
      } ::
        liftRecursiveFieldBindersForMinor fieldCount previousMinors recursiveIndex (localCount + 1) rest

def indexedRecursiveHypothesisType (previousMinors fieldCount recursiveIndex : Nat)
    (rec : IndexedRecursiveFieldInfo) : Expr :=
  let localCount := rec.binders.length
  let indices :=
    rec.indices.map fun index =>
      liftRecursiveFieldExprForMinor fieldCount previousMinors recursiveIndex localCount index
  let motive := .bvar (localCount + fieldCount + recursiveIndex + previousMinors)
  let body := indexedMotiveApp motive indices (recursiveFieldTarget fieldCount recursiveIndex rec)
  bindForall (liftRecursiveFieldBindersForMinor fieldCount previousMinors recursiveIndex 0 rec.binders) body

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
    (ctorInfos : List IndexedRecursorConstructorInfo) (motiveLevel : Level) : Expr :=
  let motive := { name := "motive", type := indexedMotiveType spec motiveLevel }
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
    MPC.Packages.Inductive.Prop.checkPropInductiveEnabled manifest
  else
    pure ()
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
  let largeElimEligible ← MPC.Packages.Inductive.Prop.simpleLargeElimEligible manifest env spec
  let motiveLevel :=
    MPC.Packages.Inductive.Prop.recursorMotiveLevel spec.levelParams spec.resultLevel
      largeElimEligible
  let recursorLevelParams :=
    MPC.Packages.Inductive.Prop.recursorLevelParams motiveLevel spec.levelParams
  let recursorType := simpleRecursorType spec motiveLevel
  let _ ← inferSort manifest env recursorLevelParams [] recursorType
  let ctorInfos := spec.constructors.map (simpleRecursorConstructorInfo spec)
  Env.add env
    {
      name := simpleRecursorName spec
      levelParams := recursorLevelParams
      type := recursorType
      kind :=
        .recursor
          {
            inductiveName := spec.name
            constructors := ctorInfos
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
    MPC.Packages.Inductive.Prop.checkPropInductiveEnabled manifest
  else
    pure ()
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
  let largeElimEligible ← MPC.Packages.Inductive.Prop.indexedLargeElimEligible manifest env spec
  let motiveLevel :=
    MPC.Packages.Inductive.Prop.recursorMotiveLevel spec.levelParams spec.resultLevel
      largeElimEligible
  let recursorLevelParams :=
    MPC.Packages.Inductive.Prop.recursorLevelParams motiveLevel spec.levelParams
  let recursorType := indexedRecursorType spec ctorInfos motiveLevel
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
      | .equalityPrimitives =>
          MPC.Packages.Equality.addEqualityPrimitives manifest env
      | .quotientPrimitives =>
          MPC.Packages.Quotient.addQuotientPrimitives manifest env

def replay (manifest : Manifest) : Env → List Declaration → Result Env
  | env, [] => pure env
  | env, decl :: rest => do
      let env ← addDecl manifest env decl
      replay manifest env rest

end MPC
