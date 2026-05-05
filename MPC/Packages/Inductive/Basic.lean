import MPC.Env

namespace MPC

def extendBinders : Context → List Binder → Context
  | ctx, [] => ctx
  | ctx, binder :: rest => extendBinders (ctx.extend binder.name binder.type) rest

def sourceOrderBvars (count offset : Nat) : List Expr :=
  (List.range count).map fun index =>
    .bvar (offset + count - 1 - index)

partial def liftFieldBindersForOuter (amount : Nat) : Nat → List Binder → List Binder
  | _, [] => []
  | boundFields, binder :: rest =>
      { binder with type := binder.type.liftFrom amount boundFields } ::
        liftFieldBindersForOuter amount (boundFields + 1) rest

def enumerateFrom : List α → Nat → List (Nat × α)
  | [], _ => []
  | value :: rest, index => (index, value) :: enumerateFrom rest (index + 1)

def enumerate (values : List α) : List (Nat × α) :=
  enumerateFrom values 0

def fieldTypeUnderAllFields (fieldCount fieldIndex : Nat) (type : Expr) : Expr :=
  type.liftFrom (fieldCount - fieldIndex) 0

def binderTypesAlphaEq (left right : List Binder) : Bool :=
  left.length == right.length &&
    (left.zip right).all fun pair => pair.1.type.alphaEq pair.2.type

def simpleInductiveType (spec : SimpleInductiveSpec) : Expr :=
  bindForall spec.params (.sort spec.resultLevel)

def simpleInductiveLevels (spec : SimpleInductiveSpec) : List Level :=
  spec.levelParams.map .param

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

def simpleRecursorName (spec : SimpleInductiveSpec) : Name :=
  spec.name ++ ".rec"

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

end MPC
