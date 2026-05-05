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

partial def dropBVarsFrom (amount cutoff : Nat) : Expr → Option Expr
  | .bvar index =>
      if index < cutoff then
        some (.bvar index)
      else if index < cutoff + amount then
        none
      else
        some (.bvar (index - amount))
  | .sort level => some (.sort level)
  | .const name levels => some (.const name levels)
  | .lit literal => some (.lit literal)
  | .app fn arg => do
      some (.app (← dropBVarsFrom amount cutoff fn) (← dropBVarsFrom amount cutoff arg))
  | .lam name type body => do
      some
        (.lam name
          (← dropBVarsFrom amount cutoff type)
          (← dropBVarsFrom amount (cutoff + 1) body))
  | .forallE name type body => do
      some
        (.forallE name
          (← dropBVarsFrom amount cutoff type)
          (← dropBVarsFrom amount (cutoff + 1) body))
  | .letE name type value body => do
      some
        (.letE name
          (← dropBVarsFrom amount cutoff type)
          (← dropBVarsFrom amount cutoff value)
          (← dropBVarsFrom amount (cutoff + 1) body))
  | .proj structureName fieldIndex target => do
      some (.proj structureName fieldIndex (← dropBVarsFrom amount cutoff target))

def dropBVars (amount : Nat) (expr : Expr) : Option Expr :=
  dropBVarsFrom amount 0 expr

def nestedRecursorName (rootName : Name) (targetIndex : Nat) : Name :=
  if targetIndex == 0 then
    rootName ++ ".rec"
  else
    rootName ++ ".rec_" ++ toString targetIndex

structure PendingNestedTargetSchema where
  locals : List Binder := []
  target : Expr
  deriving BEq, Repr, Inhabited

def binderTypesAlphaEq (left right : List Binder) : Bool :=
  left.length == right.length &&
    (left.zip right).all fun pair => pair.1.type.alphaEq pair.2.type

def pendingNestedTargetSchemaEq (left right : PendingNestedTargetSchema) : Bool :=
  binderTypesAlphaEq left.locals right.locals && left.target.alphaEq right.target

def findNestedSchemaIndex? (target : PendingNestedTargetSchema) :
    List PendingNestedTargetSchema → Nat → Option Nat
  | [], _ => none
  | entry :: rest, index =>
      if pendingNestedTargetSchemaEq entry target then
        some index
      else
        findNestedSchemaIndex? target rest (index + 1)

def internNestedSchema (schemas : List PendingNestedTargetSchema)
    (target : PendingNestedTargetSchema) : Nat × List PendingNestedTargetSchema :=
  match findNestedSchemaIndex? target schemas 0 with
  | some index => (index, schemas)
  | none => (schemas.length, schemas ++ [target])

def rootRecursiveTarget? (spec : SimpleInductiveSpec) (localCount : Nat) (expr : Expr) : Bool :=
  let (head, args) := expr.getAppFnArgs
  match head with
  | .const name levels =>
      name == spec.name &&
        levels.length == spec.levelParams.length &&
        args.length == spec.params.length &&
        (args.zip (simpleParamArgs spec localCount)).all fun pair => pair.1.alphaEq pair.2
  | _ => false

structure NestedContainerOccurrence where
  schema : PendingNestedTargetSchema
  targetArgs : List Expr := []
  deriving BEq, Repr, Inhabited

def instantiateIndexBinders (levelSubst : List (Name × Level)) (targetArgs : List Expr) :
    Nat → List Binder → List Binder
  | _, [] => []
  | bound, binder :: rest =>
      let type :=
        (binder.type.instantiateLevels levelSubst).instantiateManyFrom bound targetArgs
      { binder with type } :: instantiateIndexBinders levelSubst targetArgs (bound + 1) rest

def nestedContainerOccurrence? (manifest : Manifest) (env : Env) (rootName : Name)
    (fieldCount localCount : Nat) (expr : Expr) :
    Result (Option NestedContainerOccurrence) := do
  let (head, args) := expr.getAppFnArgs
  let lowerTargetParameter (arg : Expr) : Result Expr := do
    let some withoutFields := dropBVarsFrom fieldCount localCount arg
      | fail s!"nested target parameter depends on constructor fields: {repr arg}"
    let some lowered := dropBVars localCount withoutFields
      | fail s!"nested target parameter depends on local binders: {repr arg}"
    pure lowered
  match head with
  | .const name levels =>
      match availableCovariantContainer? manifest env name with
      | some info =>
          if args.length != info.positiveArgs.length then
            pure none
          else
            let mut hasPositiveOccurrence := false
            for pair in enumerate args do
              if listGetD info.positiveArgs pair.1 then
                if containsConst rootName pair.2 then
                  hasPositiveOccurrence := true
              else if containsConst rootName pair.2 then
                fail s!"recursive occurrence appears in non-positive nested target argument: {repr expr}"
              else
                pure ()
            if !hasPositiveOccurrence then
              pure none
            else
              match env.find? name with
              | some { kind := .indexedInductiveType spec, .. } =>
                  if levels.length != spec.levelParams.length then
                    fail s!"nested indexed target {name} has wrong universe arity"
                  else if args.length != spec.params.length + spec.indices.length then
                    fail s!"nested indexed target {name} has wrong argument arity"
                  else if !(listTakeD info.positiveArgs spec.params.length).any id then
                    fail s!"recursive occurrence appears outside a positive parameter of {name}"
                  else
                    let params ←
                      (args.take spec.params.length).mapM lowerTargetParameter
                    let levelSubst := spec.levelParams.zip levels
                    let locals := instantiateIndexBinders levelSubst params 0 spec.indices
                    let localArgs := sourceOrderBvars locals.length 0
                    let targetParams := params.map (·.lift locals.length)
                    let target :=
                      Expr.mkApps (.const name levels) (targetParams ++ localArgs)
                    pure
                      (some
                        {
                          schema := { locals, target }
                          targetArgs := args.drop spec.params.length
                        })
              | _ =>
                  let schemaArgs ←
                    args.mapM lowerTargetParameter
                  let target := Expr.mkApps (.const name levels) schemaArgs
                  pure (some { schema := { target }, targetArgs := [] })
      | none => pure none
  | _ => pure none

def nestedTargetExpr (target : NestedRecursorTargetInfo) : Expr :=
  target.target

def instantiateTargetFields (levelSubst : List (Name × Level)) (targetArgs : List Expr) :
    Nat → List Binder → List Binder
  | _, [] => []
  | boundFields, field :: rest =>
      let type :=
        (field.type.instantiateLevels levelSubst).instantiateManyFrom boundFields targetArgs
      { field with type } :: instantiateTargetFields levelSubst targetArgs (boundFields + 1) rest

partial def nestedRecursiveFieldInType?
    (manifest : Manifest)
    (env : Env)
    (spec : SimpleInductiveSpec)
    (fieldCount fieldIndex : Nat)
    (binders : List Binder)
    (localCount : Nat)
    (type : Expr)
    (schemas : List PendingNestedTargetSchema) :
    Result (Option NestedRecursiveFieldInfo × List PendingNestedTargetSchema) := do
  if !containsConst spec.name type then
    pure (none, schemas)
  else
    match type with
    | .forallE name domain body =>
        if containsConst spec.name domain then
          fail s!"non-positive recursive occurrence in nested recursive field domain: {repr domain}"
        else
          nestedRecursiveFieldInType? manifest env spec fieldCount fieldIndex
            (binders ++ [{ name, type := domain }]) (localCount + 1) body schemas
    | _ =>
        let lowered? := dropBVarsFrom fieldCount localCount type
        match lowered? with
        | some lowered =>
            if rootRecursiveTarget? spec localCount lowered then
              pure (some { fieldIndex, binders, targetIndex := 0, targetArgs := [] }, schemas)
            else
              match ←
                nestedContainerOccurrence? manifest env spec.name fieldCount localCount type
              with
              | some occurrence =>
                  let (targetIndex, schemas) := internNestedSchema schemas occurrence.schema
                  pure
                    (some
                      {
                        fieldIndex
                        binders
                        targetIndex
                        targetArgs := occurrence.targetArgs
                      },
                      schemas)
              | none => fail s!"unsupported nested recursive field shape: {repr lowered}"
        | none =>
            match ← nestedContainerOccurrence? manifest env spec.name fieldCount localCount type with
            | some occurrence =>
                let (targetIndex, schemas) := internNestedSchema schemas occurrence.schema
                pure
                  (some
                    {
                      fieldIndex
                      binders
                      targetIndex
                      targetArgs := occurrence.targetArgs
                    },
                    schemas)
            | none =>
                fail s!"nested recursor field depends on constructor fields at target: {repr type}"

def nestedRecursiveField?
    (manifest : Manifest)
    (env : Env)
    (spec : SimpleInductiveSpec)
    (fieldCount fieldIndex : Nat)
    (field : Binder)
    (schemas : List PendingNestedTargetSchema) :
    Result (Option NestedRecursiveFieldInfo × List PendingNestedTargetSchema) := do
  nestedRecursiveFieldInType? manifest env spec fieldCount fieldIndex [] 0
    (fieldTypeUnderAllFields fieldCount fieldIndex field.type)
    schemas

partial def nestedRecursiveFields
    (manifest : Manifest)
    (env : Env)
    (spec : SimpleInductiveSpec)
    (fields : List Binder)
    (schemas : List PendingNestedTargetSchema) :
    Result (List NestedRecursiveFieldInfo × List PendingNestedTargetSchema) := do
  let fieldCount := fields.length
  let rec loop
      (schemas : List PendingNestedTargetSchema)
      (acc : List NestedRecursiveFieldInfo) :
      List (Nat × Binder) → Result (List NestedRecursiveFieldInfo × List PendingNestedTargetSchema)
    | [] => pure (acc, schemas)
    | pair :: rest => do
        let (info?, schemas) ←
          nestedRecursiveField? manifest env spec fieldCount pair.1 pair.2 schemas
        let acc :=
          match info? with
          | some info => acc ++ [info]
          | none => acc
        loop schemas acc rest
  loop schemas [] (enumerate fields)

inductive NestedTargetSpec where
  | simple : SimpleInductiveSpec → NestedTargetSpec
  | indexed : IndexedInductiveSpec → NestedTargetSpec

def specForNestedTarget
    (env : Env)
    (root : SimpleInductiveSpec)
    (headName : Name) : Result NestedTargetSpec := do
  if headName == root.name then
    pure (.simple root)
  else
    match env.find? headName with
    | some { kind := .inductiveType spec, .. } => pure (.simple spec)
    | some { kind := .indexedInductiveType spec, .. } => pure (.indexed spec)
    | some _ => fail s!"nested recursor helper target {headName} is not an inductive"
    | none => fail s!"unknown nested recursor helper target: {headName}"

partial def buildNestedRecursorTargets
    (manifest : Manifest)
    (env : Env)
    (root : SimpleInductiveSpec)
    (schemas : List PendingNestedTargetSchema)
    (built : List NestedRecursorTargetInfo) : Result (List NestedRecursorTargetInfo) := do
  if built.length == schemas.length then
    pure built
  else
    let some schema := listGet? schemas built.length
      | fail s!"internal error: missing nested recursor target {built.length}"
    let targetExpr := schema.target
    let (head, targetArgs) := targetExpr.getAppFnArgs
    let (headName, levels) ←
      match head with
      | .const name levels => pure (name, levels)
      | _ => fail s!"nested recursor target is not a constant application: {repr targetExpr}"
    let mut schemas := schemas
    let mut ctors : List NestedRecursorConstructorInfo := []
    let (paramCount, params) ←
      match ← specForNestedTarget env root headName with
      | .simple targetSpec =>
          if !schema.locals.isEmpty then
            fail s!"simple nested target {headName} has local target arguments"
          else if levels.length != targetSpec.levelParams.length then
            fail s!"nested recursor target {headName} has wrong universe arity"
          else if targetArgs.length != targetSpec.params.length then
            fail s!"nested recursor target {headName} has wrong argument arity"
          else
            let targetParams := targetArgs.take targetSpec.params.length
            let levelSubst := targetSpec.levelParams.zip levels
            for ctor in targetSpec.constructors do
              let fields := instantiateTargetFields levelSubst targetParams 0 ctor.fields
              let (recursiveFields, nextSchemas) ←
                nestedRecursiveFields manifest env root fields schemas
              schemas := nextSchemas
              ctors :=
                ctors ++
                  [
                    {
                      name := ctor.name
                      fields
                      targetArgs := []
                      recursiveFields
                    }
                  ]
            pure (targetSpec.params.length, targetParams)
      | .indexed targetSpec =>
          if levels.length != targetSpec.levelParams.length then
            fail s!"nested recursor target {headName} has wrong universe arity"
          else if schema.locals.length != targetSpec.indices.length then
            fail s!"nested recursor target {headName} has wrong local arity"
          else if targetArgs.length != targetSpec.params.length + targetSpec.indices.length then
            fail s!"nested recursor target {headName} has wrong argument arity"
          else
            let targetParams ←
              (targetArgs.take targetSpec.params.length).mapM fun arg =>
                match dropBVars schema.locals.length arg with
                | some lowered => pure lowered
                | none =>
                    fail s!"nested recursor target parameter depends on target locals: {repr arg}"
            let levelSubst := targetSpec.levelParams.zip levels
            for ctor in targetSpec.constructors do
              let fields := instantiateTargetFields levelSubst targetParams 0 ctor.fields
              let ctorTargetArgs :=
                ctor.targetIndices.map fun index =>
                  (index.instantiateLevels levelSubst).instantiateManyFrom fields.length targetParams
              let (recursiveFields, nextSchemas) ←
                nestedRecursiveFields manifest env root fields schemas
              schemas := nextSchemas
              ctors :=
                ctors ++
                  [
                    {
                      name := ctor.name
                      fields
                      targetArgs := ctorTargetArgs
                      recursiveFields
                    }
                  ]
            pure (targetSpec.params.length, targetParams)
    let info : NestedRecursorTargetInfo :=
      {
        recursorName := nestedRecursorName root.name built.length
        locals := schema.locals
        headName
        levels
        target := targetExpr
        paramCount
        params
        constructors := ctors
      }
    buildNestedRecursorTargets manifest env root schemas (built ++ [info])

def buildNestedRecursorFamily?
    (manifest : Manifest)
    (env : Env)
    (spec : SimpleInductiveSpec) : Result (Option (List NestedRecursorTargetInfo)) := do
  if !manifest.supportsLean429NestedContainers then
    pure none
  else
    let rootTarget : PendingNestedTargetSchema := { target := simpleInductiveTarget spec }
    let targets ← buildNestedRecursorTargets manifest env spec [rootTarget] []
    if targets.length <= 1 then
      pure none
    else
      pure (some targets)

structure NestedMinorEntry where
  targetIndex : Nat
  target : NestedRecursorTargetInfo
  ctor : NestedRecursorConstructorInfo
  deriving BEq, Repr, Inhabited

def nestedMinorEntries (targets : List NestedRecursorTargetInfo) : List NestedMinorEntry :=
  (enumerate targets).foldl
    (fun entries pair =>
      entries ++ pair.2.constructors.map fun ctor =>
        { targetIndex := pair.1, target := pair.2, ctor })
    []

def nestedMotiveOffset (motiveCount targetIndex : Nat) : Result Nat := do
  if targetIndex < motiveCount then
    pure (motiveCount - 1 - targetIndex)
  else
    fail s!"nested recursor target index {targetIndex} is out of range"

def liftNestedRecursiveFieldExprForMinor
    (fieldCount motiveCount previousMinors recursiveIndex localCount : Nat)
    (expr : Expr) : Expr :=
  (expr.liftFrom (previousMinors + motiveCount) (localCount + fieldCount)).liftFrom
    recursiveIndex
    localCount

partial def liftNestedRecursiveFieldBindersForMinor
    (fieldCount motiveCount previousMinors recursiveIndex : Nat) :
    Nat → List Binder → List Binder
  | _, [] => []
  | localCount, binder :: rest =>
      {
        binder with
        type :=
          liftNestedRecursiveFieldExprForMinor
            fieldCount
            motiveCount
            previousMinors
            recursiveIndex
            localCount
            binder.type
      } ::
        liftNestedRecursiveFieldBindersForMinor
          fieldCount
          motiveCount
          previousMinors
          recursiveIndex
          (localCount + 1)
          rest

def nestedRecursiveFieldValue (fieldCount recursiveIndex localCount fieldIndex : Nat) : Expr :=
  .bvar (localCount + recursiveIndex + fieldCount - 1 - fieldIndex)

def nestedRecursiveFieldTarget (fieldCount recursiveIndex : Nat)
    (rec : NestedRecursiveFieldInfo) : Expr :=
  let localCount := rec.binders.length
  Expr.mkApps
    (nestedRecursiveFieldValue fieldCount recursiveIndex localCount rec.fieldIndex)
    (sourceOrderBvars localCount 0)

partial def nestedRecursiveHypothesisType
    (motiveCount previousMinors fieldCount recursiveIndex : Nat)
    (rec : NestedRecursiveFieldInfo) : Result Expr := do
  let localCount := rec.binders.length
  let motiveIndex :=
    localCount + fieldCount + recursiveIndex + previousMinors +
      (← nestedMotiveOffset motiveCount rec.targetIndex)
  let targetArgs :=
    rec.targetArgs.map
      (liftNestedRecursiveFieldExprForMinor
        fieldCount
        motiveCount
        previousMinors
        recursiveIndex
        localCount)
  let body :=
    Expr.mkApps
      (.bvar motiveIndex)
      (targetArgs ++ [nestedRecursiveFieldTarget fieldCount recursiveIndex rec])
  pure
    (bindForall
      (liftNestedRecursiveFieldBindersForMinor
        fieldCount
        motiveCount
        previousMinors
        recursiveIndex
        0
        rec.binders)
      body)

def nestedRecursiveHypothesisBinders
    (motiveCount previousMinors fieldCount : Nat)
    (recFields : List NestedRecursiveFieldInfo) : Result (List Binder) := do
  (enumerate recFields).mapM fun pair => do
    pure
      {
        name := s!"ih{pair.2.fieldIndex}"
        type := (← nestedRecursiveHypothesisType motiveCount previousMinors fieldCount pair.1 pair.2)
      }

def nestedCtorParamArgs
    (target : NestedRecursorTargetInfo)
    (offset : Nat) : List Expr :=
  target.params.map (·.lift offset)

def nestedCtorAppFromFields
    (motiveCount previousMinors recursiveCount : Nat)
    (target : NestedRecursorTargetInfo)
    (ctor : NestedRecursorConstructorInfo) : Expr :=
  let offset := ctor.fields.length + recursiveCount + previousMinors + motiveCount
  let paramArgs := nestedCtorParamArgs target offset
  let fieldArgs := sourceOrderBvars ctor.fields.length recursiveCount
  Expr.mkApps (.const ctor.name target.levels) (paramArgs ++ fieldArgs)

def nestedMinorType
    (motiveCount previousMinors targetIndex : Nat)
    (target : NestedRecursorTargetInfo)
    (ctor : NestedRecursorConstructorInfo) : Result Expr := do
  let fieldCount := ctor.fields.length
  let recursiveCount := ctor.recursiveFields.length
  let fieldBinders := liftFieldBindersForOuter (previousMinors + motiveCount) 0 ctor.fields
  let recursiveBinders ←
    nestedRecursiveHypothesisBinders motiveCount previousMinors fieldCount ctor.recursiveFields
  let motiveIndex :=
    fieldCount + recursiveCount + previousMinors + (← nestedMotiveOffset motiveCount targetIndex)
  let targetArgs :=
    ctor.targetArgs.map fun arg =>
      (arg.liftFrom (previousMinors + motiveCount) fieldCount).liftFrom recursiveCount 0
  let body :=
    Expr.mkApps
      (.bvar motiveIndex)
      (targetArgs ++ [nestedCtorAppFromFields motiveCount previousMinors recursiveCount target ctor])
  pure (bindForall (fieldBinders ++ recursiveBinders) body)

def nestedMotiveBinders
    (targets : List NestedRecursorTargetInfo)
    (motiveLevel : Level) : List Binder :=
  (enumerate targets).map fun pair =>
    {
      name := s!"motive_{pair.1 + 1}"
      type :=
        let target := pair.2
        let localCount := target.locals.length
        bindForall (liftFieldBindersForOuter pair.1 0 target.locals)
          (.forallE "target"
            ((nestedTargetExpr target).liftFrom
              pair.1
              localCount)
            (.sort motiveLevel))
    }

def nestedTargetBinderType
    (motiveCount minorCount : Nat)
    (target : NestedRecursorTargetInfo)
    (body : Expr) : Expr :=
  let outerCount := motiveCount + minorCount
  bindForall (liftFieldBindersForOuter outerCount 0 target.locals)
    (.forallE "target"
      ((nestedTargetExpr target).liftFrom outerCount target.locals.length)
      body)

def nestedRecursorType
    (spec : SimpleInductiveSpec)
    (targets : List NestedRecursorTargetInfo)
    (targetIndex : Nat)
    (motiveLevel : Level) : Result Expr := do
  let motiveCount := targets.length
  let minorEntries := nestedMinorEntries targets
  let motiveBinders := nestedMotiveBinders targets motiveLevel
  let minorBinders ←
    (enumerate minorEntries).mapM fun pair => do
      pure
        {
          name := pair.2.ctor.name ++ ".minor"
          type :=
            (← nestedMinorType motiveCount pair.1 pair.2.targetIndex pair.2.target pair.2.ctor)
        }
  let some target := listGet? targets targetIndex
    | fail s!"nested recursor target {targetIndex} is out of range"
  let localCount := target.locals.length
  let targetVar := .bvar 0
  let localArgs := (sourceOrderBvars localCount 1)
  let motiveIndex :=
    localCount + 1 + minorBinders.length + (← nestedMotiveOffset motiveCount targetIndex)
  let body := Expr.mkApps (.bvar motiveIndex) (localArgs ++ [targetVar])
  let targetType := nestedTargetBinderType motiveCount minorBinders.length target body
  pure (bindForall spec.params (bindForall (motiveBinders ++ minorBinders) targetType))

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
  match ← buildNestedRecursorFamily? manifest env spec with
  | some targets => do
      let mut nextEnv := env
      for pair in enumerate targets do
        let recursorType ← nestedRecursorType spec targets pair.1 motiveLevel
        let _ ← inferSort manifest nextEnv recursorLevelParams [] recursorType
        nextEnv ← Env.add nextEnv
          {
            name := pair.2.recursorName
            levelParams := recursorLevelParams
            type := recursorType
            kind :=
              .nestedRecursor
                {
                  rootName := spec.name
                  targetIndex := pair.1
                  targets
                }
          }
      pure nextEnv
  | none => do
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

structure MutualConstructorEntry where
  inductiveIndex : Nat
  constructorIndex : Nat
  spec : SimpleInductiveSpec
  ctor : SimpleConstructorSpec
  deriving BEq, Repr, Inhabited

def mutualBlockNames (block : InductiveBlockSpec) : List Name :=
  block.specs.map (·.name)

def mutualConstructorEntriesFrom :
    List SimpleInductiveSpec → Nat → List MutualConstructorEntry
  | [], _ => []
  | spec :: rest, index =>
      (enumerate spec.constructors |>.map fun pair =>
        { inductiveIndex := index, constructorIndex := pair.1, spec, ctor := pair.2 }) ++
        mutualConstructorEntriesFrom rest (index + 1)

def mutualConstructorEntries (block : InductiveBlockSpec) : List MutualConstructorEntry :=
  mutualConstructorEntriesFrom block.specs 0

def mutualSpecIndex? (name : Name) : List SimpleInductiveSpec → Nat → Option Nat
  | [], _ => none
  | spec :: rest, index =>
      if spec.name == name then
        some index
      else
        mutualSpecIndex? name rest (index + 1)

def checkMutualInductiveField
    (manifest : Manifest)
    (env : Env)
    (levelParams : LevelContext)
    (blockNames : List Name)
    (ctx : Context)
    (field : Binder) : Result Context := do
  let _ ← inferSort manifest env levelParams ctx field.type
  if mutualStrictlyPositive manifest env blockNames field.type then
    pure (ctx.extend field.name field.type)
  else
    fail s!"field {field.name} is not strictly positive in mutual block"

partial def checkMutualInductiveFields
    (manifest : Manifest)
    (env : Env)
    (levelParams : LevelContext)
    (blockNames : List Name)
    (ctx : Context) : List Binder → Result Unit
  | [] => pure ()
  | field :: rest => do
      let ctx ← checkMutualInductiveField manifest env levelParams blockNames ctx field
      checkMutualInductiveFields manifest env levelParams blockNames ctx rest

def mutualDirectRecursiveField? (block : InductiveBlockSpec)
    (fieldCount fieldIndex : Nat) (field : Binder) : Option MutualRecursiveFieldInfo :=
  let type := fieldTypeUnderAllFields fieldCount fieldIndex field.type
  let (head, args) := type.getAppFnArgs
  match head with
  | .const name levels =>
      match mutualSpecIndex? name block.specs 0, block.specs.find? (fun spec => spec.name == name) with
      | some targetIndex, some targetSpec =>
          let expectedArgs := simpleParamArgs targetSpec fieldCount
          if levels.length == targetSpec.levelParams.length &&
              args.length == targetSpec.params.length &&
              (args.zip expectedArgs).all (fun pair => pair.1.alphaEq pair.2) then
            some { fieldIndex, targetIndex }
          else
            none
      | _, _ => none
  | _ => none

def mutualRecursiveFields (block : InductiveBlockSpec) (ctor : SimpleConstructorSpec) :
    List MutualRecursiveFieldInfo :=
  enumerate ctor.fields |>.filterMap fun pair =>
    mutualDirectRecursiveField? block ctor.fields.length pair.1 pair.2

def mutualRecursiveHypothesisType
    (motiveCount previousMinors fieldCount recursiveIndex : Nat)
    (rec : MutualRecursiveFieldInfo) : Expr :=
  let motiveIndex :=
    fieldCount + recursiveIndex + previousMinors + motiveCount - 1 - rec.targetIndex
  let motive := .bvar motiveIndex
  let fieldValue := .bvar (recursiveIndex + fieldCount - 1 - rec.fieldIndex)
  .app motive fieldValue

def mutualRecursiveHypothesisBinders
    (motiveCount previousMinors fieldCount : Nat)
    (recFields : List MutualRecursiveFieldInfo) : List Binder :=
  enumerate recFields |>.map fun pair =>
    {
      name := s!"ih{pair.2.fieldIndex}"
      type :=
        mutualRecursiveHypothesisType motiveCount previousMinors fieldCount pair.1 pair.2
    }

def mutualCtorAppFromFields
    (motiveCount previousMinors recursiveCount : Nat)
    (spec : SimpleInductiveSpec)
    (ctor : SimpleConstructorSpec) : Expr :=
  let paramArgs :=
    simpleParamArgs spec (ctor.fields.length + recursiveCount + previousMinors + motiveCount)
  let fieldArgs := sourceOrderBvars ctor.fields.length recursiveCount
  Expr.mkApps (.const ctor.name (simpleInductiveLevels spec)) (paramArgs ++ fieldArgs)

def mutualMinorType (block : InductiveBlockSpec) (motiveCount previousMinors : Nat)
    (entry : MutualConstructorEntry) : Expr :=
  let ctor := entry.ctor
  let fieldCount := ctor.fields.length
  let recFields := mutualRecursiveFields block ctor
  let recursiveCount := recFields.length
  let fieldBinders := liftFieldBindersForOuter (previousMinors + motiveCount) 0 ctor.fields
  let recursiveBinders :=
    mutualRecursiveHypothesisBinders motiveCount previousMinors fieldCount recFields
  let motiveIndex :=
    fieldCount + recursiveCount + previousMinors + motiveCount - 1 - entry.inductiveIndex
  let body :=
    .app (.bvar motiveIndex)
      (mutualCtorAppFromFields motiveCount previousMinors recursiveCount entry.spec ctor)
  bindForall (fieldBinders ++ recursiveBinders) body

def mutualRecursorConstructorInfo (block : InductiveBlockSpec)
    (entry : MutualConstructorEntry) : MutualRecursorConstructorInfo :=
  {
    inductiveIndex := entry.inductiveIndex
    name := entry.ctor.name
    fieldCount := entry.ctor.fields.length
    recursiveFields := mutualRecursiveFields block entry.ctor
  }

def mutualRecursorType (block : InductiveBlockSpec) (targetIndex : Nat)
    (motiveLevel : Level) : Result Expr := do
  let some targetSpec := listGet? block.specs targetIndex
    | fail s!"mutual recursor target index {targetIndex} is out of range"
  let motiveCount := block.specs.length
  let entries := mutualConstructorEntries block
  let motiveBinders :=
    block.specs.map fun spec =>
      { name := spec.name ++ ".motive", type := simpleMotiveType spec motiveLevel }
  let minorBinders :=
    enumerate entries |>.map fun pair =>
      {
        name := pair.2.ctor.name ++ ".minor"
        type := mutualMinorType block motiveCount pair.1 pair.2
      }
  let target :=
    {
      name := "target"
      type := simpleInductiveTargetAt targetSpec (minorBinders.length + motiveCount)
    }
  let motiveIndex := minorBinders.length + motiveCount - 1 - targetIndex + 1
  let body := .app (.bvar motiveIndex) (.bvar 0)
  pure (bindForall targetSpec.params (bindForall (motiveBinders ++ minorBinders ++ [target]) body))

def mutualBlockMotiveLevel
    (block : InductiveBlockSpec)
    (largeElimEligible : Bool) : Level :=
  if block.specs.all (fun spec => spec.resultLevel.defEq .zero) && !largeElimEligible then
    .zero
  else
    .param (MPC.Packages.Inductive.Prop.freshLevelParam block.levelParams)

def checkInductiveBlockHeader
    (manifest : Manifest)
    (env : Env)
    (block : InductiveBlockSpec)
    (sharedParams : List Binder)
    (spec : SimpleInductiveSpec) : Result Unit := do
  if spec.levelParams != block.levelParams then
    fail s!"inductive {spec.name} must use the block universe parameters"
  else if !binderTypesAlphaEq spec.params sharedParams then
    fail s!"inductive {spec.name} must use the block parameter telescope"
  else if spec.resultLevel.defEq .zero then
    MPC.Packages.Inductive.Prop.checkPropInductiveEnabled manifest
  else
    pure ()
  let _ ← inferSort manifest env block.levelParams [] (.sort spec.resultLevel)
  let _ ← inferSort manifest env block.levelParams [] (simpleInductiveType spec)
  pure ()

def addInductiveBlock (manifest : Manifest) (env : Env) (block : InductiveBlockSpec) :
    Result Env := do
  Manifest.validate manifest
  if !manifest.supportsInductiveBlocks then
    fail "mutual inductive blocks are disabled by the manifest"
  else if !manifest.supportsSimpleInductives then
    fail "simple inductives are disabled by the manifest"
  else
    pure ()
  let firstSpec ←
    match block.specs with
    | [] => fail "mutual inductive block must contain at least one inductive"
    | spec :: _ => pure spec
  for spec in block.specs do
    checkInductiveBlockHeader manifest env block firstSpec.params spec
  let mut provisionalEnv := env
  for spec in block.specs do
    provisionalEnv ← Env.add provisionalEnv
      {
        name := spec.name
        levelParams := block.levelParams
        type := simpleInductiveType spec
        kind := .inductiveType spec
      }
  let blockNames := mutualBlockNames block
  let paramCtx := extendBinders [] firstSpec.params
  for spec in block.specs do
    for ctor in spec.constructors do
      checkMutualInductiveFields manifest provisionalEnv block.levelParams blockNames
        paramCtx ctor.fields
      let _ ← inferSort manifest provisionalEnv block.levelParams []
        (simpleConstructorType spec ctor)
      pure ()
  let mut env := provisionalEnv
  for entry in mutualConstructorEntries block do
    env ← Env.add env
      {
        name := entry.ctor.name
        levelParams := block.levelParams
        type := simpleConstructorType entry.spec entry.ctor
        kind := .constructor entry.spec.name entry.constructorIndex entry.ctor.fields.length
      }
  let largeElimEligible := false
  let motiveLevel := mutualBlockMotiveLevel block largeElimEligible
  let recursorLevelParams :=
    MPC.Packages.Inductive.Prop.recursorLevelParams motiveLevel block.levelParams
  let ctorInfos := (mutualConstructorEntries block).map (mutualRecursorConstructorInfo block)
  let inductiveNames := mutualBlockNames block
  for pair in enumerate block.specs do
    let recursorType ← mutualRecursorType block pair.1 motiveLevel
    let _ ← inferSort manifest env recursorLevelParams [] recursorType
    env ← Env.add env
      {
        name := simpleRecursorName pair.2
        levelParams := recursorLevelParams
        type := recursorType
        kind :=
          .mutualRecursor
            {
              targetIndex := pair.1
              inductiveNames
              constructors := ctorInfos
            }
      }
  pure env

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
      | .inductiveBlock block =>
          addInductiveBlock manifest env block
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
