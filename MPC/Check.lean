import MPC.Declaration
import MPC.Normalize

namespace MPC

def checkLevelsClosed (ctx : LevelContext) (levels : List Level) : Result Unit := do
  for level in levels do
    if level.closedIn ctx then
      pure ()
    else
      fail s!"level is not closed in active universe context: {repr level}"

def inferPiSort (manifest : Manifest) (domain codomain : Level) : Level :=
  if manifest.prop == .enabled && codomain.defEq .zero then
    .zero
  else
    .imax domain codomain

def sortLevel? : Expr → Option Level
  | .sort level => some level
  | _ => none

def requireNatLiteralSupport (env : Env) : Result Unit := do
  if env.contains "Nat" && env.contains "Nat.zero" && env.contains "Nat.succ" then
    pure ()
  else
    fail "natural literals require Nat, Nat.zero, and Nat.succ in the environment"

def requireStringLiteralSupport (env : Env) : Result Unit := do
  if env.contains "String" then
    pure ()
  else
    fail "string literals require String in the environment"

def natLiteralConstructorSpine (env : Env) : Nat → Result Expr
  | 0 => do
      requireNatLiteralSupport env
      pure (.const "Nat.zero" [])
  | n + 1 => do
      requireNatLiteralSupport env
      pure (.app (.const "Nat.succ" []) (← natLiteralConstructorSpine env n))

def projectionFieldType (env : Env) (structureName : Name) (fieldIndex : Nat)
    (target targetType : Expr) : Result Expr := do
  let (head, targetArgs) := targetType.getAppFnArgs
  match head with
  | .const targetName levels =>
      if targetName != structureName then
        fail s!"projection target has type {targetName}, expected {structureName}"
      else
        match env.find? structureName with
        | some { kind := .inductiveType spec, levelParams, .. } =>
            if levels.length != levelParams.length then
              fail s!"projection target has wrong universe arity for {structureName}"
            else if targetArgs.length != spec.params.length then
              fail s!"projection target has wrong parameter arity for {structureName}"
            else
              match spec.constructors with
              | [ctor] =>
                  let some field := listGet? ctor.fields fieldIndex
                    | fail s!"projection field {fieldIndex} is out of range for {structureName}"
                  let previousFields :=
                    (List.range fieldIndex).map fun index =>
                      .proj structureName index target
                  pure (field.type.instantiateSourceArgs (targetArgs ++ previousFields))
              | _ => fail s!"projection target {structureName} is not a one-constructor structure"
        | some _ => fail s!"projection target {structureName} is not an inductive type"
        | none => fail s!"unknown projection structure: {structureName}"
  | _ => fail s!"projection target type is not a structure application: {repr targetType}"

mutual

partial def infer (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (ctx : Context) : Expr → Result Expr
  | .bvar index =>
      match ctx.lookup? index with
      | some binder => pure binder.type
      | none => fail s!"unbound de Bruijn index: {index}"
  | .sort level => do
      if level.closedIn levelParams then
        pure (.sort (.succ level))
      else
        fail s!"sort level is not closed in active universe context: {repr level}"
  | .const name levels => do
      checkLevelsClosed levelParams levels
      let some info := env.find? name
        | fail s!"unknown constant: {name}"
      let some type := info.instantiateType? levels
        | fail s!"constant {name} expects {info.levelParams.length} universe levels, got {levels.length}"
      pure type
  | .lit (.nat _) => do
      if !manifest.supportsNatLiterals then
        fail "natural literals are disabled by the manifest"
      else
        requireNatLiteralSupport env
        pure (.const "Nat" [])
  | .lit (.str _) => do
      if !manifest.supportsStringLiterals then
        fail "string literals are disabled by the manifest"
      else
        requireStringLiteralSupport env
        pure (.const "String" [])
  | .app fn arg => do
      let fnType ← whnf manifest env levelParams (← infer manifest env levelParams ctx fn)
      match fnType with
      | .forallE _ domain body => do
          check manifest env levelParams ctx arg domain
          pure (Expr.instantiate1 body arg)
      | _ => fail s!"function expected, got {repr fnType}"
  | .lam name domain body => do
      let _ ← inferSort manifest env levelParams ctx domain
      let bodyType ← infer manifest env levelParams (ctx.extend name domain) body
      pure (.forallE name domain bodyType)
  | .forallE name domain body => do
      let domainSort ← inferSort manifest env levelParams ctx domain
      let bodySort ← inferSort manifest env levelParams (ctx.extend name domain) body
      pure (.sort (inferPiSort manifest domainSort bodySort))
  | .letE _ type value body => do
      let _ ← inferSort manifest env levelParams ctx type
      check manifest env levelParams ctx value type
      infer manifest env levelParams ctx (Expr.instantiate1 body value)
  | .proj structureName fieldIndex target => do
      if !manifest.supportsProjections then
        fail "projection expressions are disabled by the manifest"
      else
        let targetType ← whnf manifest env levelParams (← infer manifest env levelParams ctx target)
        projectionFieldType env structureName fieldIndex target targetType

partial def inferSort (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (ctx : Context) (expr : Expr) : Result Level := do
  let type ← whnf manifest env levelParams (← infer manifest env levelParams ctx expr)
  match type with
  | .sort level => pure level
  | _ => fail s!"sort expected for {repr expr}, got {repr type}"

partial def check (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (ctx : Context) (expr expectedType : Expr) : Result Unit := do
  match expr with
  | .lam name domain body => do
      let expectedType ← whnf manifest env levelParams expectedType
      match expectedType with
      | .forallE _ expectedDomain expectedBody => do
          let _ ← inferSort manifest env levelParams ctx domain
          defEq manifest env levelParams ctx domain expectedDomain
          check manifest env levelParams (ctx.extend name domain) body expectedBody
      | _ =>
          let inferred ← infer manifest env levelParams ctx expr
          defEq manifest env levelParams ctx inferred expectedType
  | .letE _ type value body => do
      let _ ← inferSort manifest env levelParams ctx type
      check manifest env levelParams ctx value type
      check manifest env levelParams ctx (Expr.instantiate1 body value) expectedType
  | _ =>
      let inferred ← infer manifest env levelParams ctx expr
      defEq manifest env levelParams ctx inferred expectedType

partial def structuralDefEq (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (ctx : Context) (left right : Expr) : Result Unit := do
  let left ← whnf manifest env levelParams left
  let right ← whnf manifest env levelParams right
  match left, right with
  | .bvar left, .bvar right =>
      if left == right then pure () else fail "bound variables differ"
  | .sort left, .sort right =>
      if left.defEq right then pure () else fail "sort levels differ"
  | .const leftName leftLevels, .const rightName rightLevels =>
      if leftName != rightName || leftLevels.length != rightLevels.length then
        fail "constants differ"
      else
        for pair in leftLevels.zip rightLevels do
          if pair.1.defEq pair.2 then pure () else fail "constant levels differ"
  | .lit left, .lit right =>
      if left == right then pure () else fail "literals differ"
  | .lit (.nat value), _ =>
      if !manifest.supportsNatLiterals then
        fail "natural literals are disabled by the manifest"
      else
        structuralDefEq manifest env levelParams ctx (← natLiteralConstructorSpine env value) right
  | _, .lit (.nat value) =>
      if !manifest.supportsNatLiterals then
        fail "natural literals are disabled by the manifest"
      else
        structuralDefEq manifest env levelParams ctx left (← natLiteralConstructorSpine env value)
  | .app leftFn leftArg, .app rightFn rightArg =>
      defEq manifest env levelParams ctx leftFn rightFn
      defEq manifest env levelParams ctx leftArg rightArg
  | .lam _ leftType leftBody, .lam _ rightType rightBody =>
      defEq manifest env levelParams ctx leftType rightType
      defEq manifest env levelParams (ctx.extend "_" leftType) leftBody rightBody
  | .forallE _ leftType leftBody, .forallE _ rightType rightBody =>
      defEq manifest env levelParams ctx leftType rightType
      defEq manifest env levelParams (ctx.extend "_" leftType) leftBody rightBody
  | .letE _ _ leftValue leftBody, _ =>
      defEq manifest env levelParams ctx (Expr.instantiate1 leftBody leftValue) right
  | _, .letE _ _ rightValue rightBody =>
      defEq manifest env levelParams ctx left (Expr.instantiate1 rightBody rightValue)
  | .proj leftStruct leftIndex leftTarget, .proj rightStruct rightIndex rightTarget =>
      if leftStruct == rightStruct && leftIndex == rightIndex then
        defEq manifest env levelParams ctx leftTarget rightTarget
      else
        fail "projections differ"
  | _, _ => fail s!"not definitionally equal: {repr left} and {repr right}"

partial def isPropExpr (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (ctx : Context) (expr : Expr) : Result Unit := do
  if manifest.prop != .enabled then
    fail "Prop is disabled by the manifest"
  else
    let sort ← inferSort manifest env levelParams ctx expr
    if sort.defEq .zero then pure () else fail s!"not a proposition: {repr expr}"

partial def proofIrrelevanceDefEq (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (ctx : Context) (left right : Expr) : Result Unit := do
  if manifest.prop != .enabled then
    fail "proof irrelevance is disabled by the manifest"
  else
    let leftType ← infer manifest env levelParams ctx left
    let rightType ← infer manifest env levelParams ctx right
    isPropExpr manifest env levelParams ctx leftType
    defEq manifest env levelParams ctx leftType rightType

partial def functionEtaDefEq (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (ctx : Context) (etaExpanded other : Expr) : Result Unit := do
  if !manifest.supportsFunctionEta then
    fail "function eta is disabled by the manifest"
  else
    let etaExpanded ← whnf manifest env levelParams etaExpanded
    match etaExpanded with
    | .lam name domain body => do
        let otherType ← whnf manifest env levelParams (← infer manifest env levelParams ctx other)
        match otherType with
        | .forallE _ expectedDomain _ => do
            defEq manifest env levelParams ctx domain expectedDomain
            let expectedBody := .app (other.lift 1) (.bvar 0)
            defEq manifest env levelParams (ctx.extend name domain) body expectedBody
        | _ => fail "function eta target is not a function"
    | _ => fail "function eta expansion is not a lambda"

partial def defEq (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (ctx : Context) (left right : Expr) : Result Unit := do
  if left.alphaEq right then
    pure ()
  else
    match structuralDefEq manifest env levelParams ctx left right with
    | .ok () => pure ()
    | .error structuralError =>
        match proofIrrelevanceDefEq manifest env levelParams ctx left right with
        | .ok () => pure ()
        | .error proofError =>
            match functionEtaDefEq manifest env levelParams ctx left right with
            | .ok () => pure ()
            | .error _ =>
                match functionEtaDefEq manifest env levelParams ctx right left with
                | .ok () => pure ()
                | .error _ =>
                    fail s!"{structuralError.message}; proof irrelevance fallback failed: {proofError.message}"

end

def bindForall (binders : List Binder) (body : Expr) : Expr :=
  binders.foldr (fun binder body => .forallE binder.name binder.type body) body

partial def containsConst (target : Name) : Expr → Bool
  | .bvar _ => false
  | .sort _ => false
  | .const name _ => name == target
  | .lit _ => false
  | .app fn arg => containsConst target fn || containsConst target arg
  | .lam _ type body => containsConst target type || containsConst target body
  | .forallE _ type body => containsConst target type || containsConst target body
  | .letE _ type value body =>
      containsConst target type || containsConst target value || containsConst target body
  | .proj _ _ projectionTarget => containsConst target projectionTarget

partial def containsAnyConst (targets : List Name) : Expr → Bool
  | .bvar _ => false
  | .sort _ => false
  | .const name _ => targets.contains name
  | .lit _ => false
  | .app fn arg => containsAnyConst targets fn || containsAnyConst targets arg
  | .lam _ type body => containsAnyConst targets type || containsAnyConst targets body
  | .forallE _ type body => containsAnyConst targets type || containsAnyConst targets body
  | .letE _ type value body =>
      containsAnyConst targets type ||
        containsAnyConst targets value ||
        containsAnyConst targets body
  | .proj _ _ projectionTarget => containsAnyConst targets projectionTarget

def getAppHeadName? (expr : Expr) : Option Name :=
  match expr.getAppFnArgs.1 with
  | .const name _ => some name
  | _ => none

structure CovariantContainerInfo where
  positiveArgs : List Bool
  deriving BEq, Repr, Inhabited

def lean429CovariantContainerInfo? : Name → Option CovariantContainerInfo
  | "Array" => some { positiveArgs := [true] }
  | "List" => some { positiveArgs := [true] }
  | "Vec" => some { positiveArgs := [true, false] }
  | _ => none

def availableFixedCovariantContainer? (manifest : Manifest) (env : Env) (name : Name) :
    Option CovariantContainerInfo :=
  if !manifest.supportsLean429NestedContainers then
    none
  else
    match lean429CovariantContainerInfo? name, env.find? name with
    | some info, some { kind := .inductiveType .., .. } => some info
    | some info, some { kind := .indexedInductiveType .., .. } => some info
    | _, _ => none

partial def containsBVarAt (target : Nat) : Expr → Bool
  | .bvar index => index == target
  | .sort _ => false
  | .const _ _ => false
  | .lit _ => false
  | .app fn arg => containsBVarAt target fn || containsBVarAt target arg
  | .lam _ type body => containsBVarAt target type || containsBVarAt (target + 1) body
  | .forallE _ type body => containsBVarAt target type || containsBVarAt (target + 1) body
  | .letE _ type value body =>
      containsBVarAt target type || containsBVarAt target value || containsBVarAt (target + 1) body
  | .proj _ _ projectionTarget => containsBVarAt target projectionTarget

def checkFieldTypeUnderAllFields (fieldCount fieldIndex : Nat) (type : Expr) : Expr :=
  type.liftFrom (fieldCount - fieldIndex) 0

def listAllIdx (p : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | index, value :: rest => p index value && listAllIdx p (index + 1) rest

def listGetD [Inhabited α] : List α → Nat → α
  | [], _ => default
  | value :: _, 0 => value
  | _ :: rest, index + 1 => listGetD rest index

def listTakeD [Inhabited α] (values : List α) (count : Nat) : List α :=
  (List.range count).map fun index => listGetD values index

def boolFlagsEqual (left right : List Bool) : Bool :=
  left.length == right.length &&
    (left.zip right).all fun pair => pair.1 == pair.2

def computeCovariantFlags (paramCount : Nat) (check : List Bool → Nat → Bool) : List Bool :=
  let rec loop : Nat → List Bool → List Bool
    | 0, flags => flags
    | fuel + 1, flags =>
        let next :=
          (List.range paramCount).map fun index =>
            listGetD flags index && check flags index
        if boolFlagsEqual flags next then
          flags
        else
          loop fuel next
  loop (paramCount + 1) (List.replicate paramCount true)

mutual

partial def bvarStrictlyPositive (manifest : Manifest) (env : Env) (selfName : Name)
    (selfPositive : List Bool) (target : Nat) (expr : Expr) : Bool :=
  match expr with
  | .bvar _ => true
  | .forallE _ domain body =>
      !containsBVarAt target domain &&
        bvarStrictlyPositive manifest env selfName selfPositive (target + 1) body
  | _ =>
      let (head, args) := expr.getAppFnArgs
      match head with
      | .const name _ =>
          if name == selfName then
            args.length == selfPositive.length &&
              listAllIdx (fun index arg =>
                if listGetD selfPositive index then
                  bvarStrictlyPositive manifest env selfName selfPositive target arg
                else
                  !containsBVarAt target arg)
                0
                args
          else
            match availableCovariantContainer? manifest env name with
            | some info =>
                args.length == info.positiveArgs.length &&
                  listAllIdx (fun index arg =>
                    if listGetD info.positiveArgs index then
                      bvarStrictlyPositive manifest env selfName selfPositive target arg
                    else
                      !containsBVarAt target arg)
                    0
                    args
            | none => !containsBVarAt target expr
      | _ => !containsBVarAt target expr

partial def simpleCovariantContainer? (manifest : Manifest) (env : Env)
    (spec : SimpleInductiveSpec) : Option CovariantContainerInfo :=
  if spec.params.isEmpty then
    none
  else
    let flags :=
      computeCovariantFlags spec.params.length fun selfFlags paramIndex =>
        spec.constructors.all fun ctor =>
          let fieldCount := ctor.fields.length
          let target := fieldCount + spec.params.length - 1 - paramIndex
          listAllIdx (fun fieldIndex field =>
            let type := checkFieldTypeUnderAllFields fieldCount fieldIndex field.type
            bvarStrictlyPositive manifest env spec.name selfFlags target type)
            0
            ctor.fields
    if flags.any id then some { positiveArgs := flags } else none

partial def indexedCovariantContainer? (manifest : Manifest) (env : Env)
    (spec : IndexedInductiveSpec) : Option CovariantContainerInfo :=
  if spec.params.isEmpty then
    none
  else
    let flags :=
      computeCovariantFlags spec.params.length fun selfParamFlags paramIndex =>
        let selfFlags := selfParamFlags ++ List.replicate spec.indices.length false
        spec.constructors.all fun ctor =>
          let fieldCount := ctor.fields.length
          let target := fieldCount + spec.params.length - 1 - paramIndex
          ctor.targetIndices.all (fun index => !containsBVarAt target index) &&
            listAllIdx (fun fieldIndex field =>
              let type := checkFieldTypeUnderAllFields fieldCount fieldIndex field.type
              bvarStrictlyPositive manifest env spec.name selfFlags target type)
              0
              ctor.fields
    if flags.any id then
      some { positiveArgs := flags ++ List.replicate spec.indices.length false }
    else
      none

partial def availableCovariantContainer? (manifest : Manifest) (env : Env) (name : Name) :
    Option CovariantContainerInfo :=
  match availableFixedCovariantContainer? manifest env name with
  | some info => some info
  | none =>
      if !manifest.supportsLean429NestedContainers then
        none
      else
        match env.find? name with
        | some { kind := .inductiveType spec, .. } =>
            simpleCovariantContainer? manifest env spec
        | some { kind := .indexedInductiveType spec, .. } =>
            indexedCovariantContainer? manifest env spec
        | _ => none

end

partial def simpleStrictlyPositive (manifest : Manifest) (env : Env) (target : Name)
    (expr : Expr) : Bool :=
  if getAppHeadName? expr == some target then
    true
  else
    let (head, args) := expr.getAppFnArgs
    match head with
    | .const name _ =>
        match availableCovariantContainer? manifest env name with
        | some info =>
            let rec argsStrictlyPositive : Nat → List Expr → Bool
              | _, [] => true
              | index, arg :: rest =>
                  let ok :=
                    if listGetD info.positiveArgs index then
                      simpleStrictlyPositive manifest env target arg
                    else
                      !containsConst target arg
                  ok && argsStrictlyPositive (index + 1) rest
            args.length == info.positiveArgs.length && argsStrictlyPositive 0 args
        | none =>
            match expr with
            | .forallE _ domain body =>
                !containsConst target domain && simpleStrictlyPositive manifest env target body
            | _ => !containsConst target expr
    | _ =>
        match expr with
        | .forallE _ domain body =>
            !containsConst target domain && simpleStrictlyPositive manifest env target body
        | _ => !containsConst target expr

partial def mutualStrictlyPositive (manifest : Manifest) (env : Env) (targets : List Name)
    (expr : Expr) : Bool :=
  match getAppHeadName? expr with
  | some name =>
      if targets.contains name then
        true
      else
        checkHead
  | none => checkHead
where
  checkHead : Bool :=
    let (head, args) := expr.getAppFnArgs
    match head with
    | .const name _ =>
        match availableCovariantContainer? manifest env name with
        | some info =>
            let rec argsStrictlyPositive : Nat → List Expr → Bool
              | _, [] => true
              | index, arg :: rest =>
                  let ok :=
                    if listGetD info.positiveArgs index then
                      mutualStrictlyPositive manifest env targets arg
                    else
                      !containsAnyConst targets arg
                  ok && argsStrictlyPositive (index + 1) rest
            args.length == info.positiveArgs.length && argsStrictlyPositive 0 args
        | none =>
            match expr with
            | .forallE _ domain body =>
                !containsAnyConst targets domain &&
                  mutualStrictlyPositive manifest env targets body
            | _ => !containsAnyConst targets expr
    | _ =>
        match expr with
        | .forallE _ domain body =>
            !containsAnyConst targets domain && mutualStrictlyPositive manifest env targets body
        | _ => !containsAnyConst targets expr

end MPC
