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
      if manifest.literals != .nat then
        fail "natural literals are disabled by the manifest"
      else
        requireNatLiteralSupport env
        pure (.const "Nat" [])
  | .lit (.str _) =>
      fail "string literals are outside the MPC PoC"
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
  | .letE name type value body => do
      let _ ← inferSort manifest env levelParams ctx type
      check manifest env levelParams ctx value type
      let bodyType ← infer manifest env levelParams (ctx.extend name type) body
      pure (Expr.instantiate1 bodyType value)
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
      if manifest.literals != .nat then
        fail "natural literals are disabled by the manifest"
      else
        structuralDefEq manifest env levelParams ctx (← natLiteralConstructorSpine env value) right
  | _, .lit (.nat value) =>
      if manifest.literals != .nat then
        fail "natural literals are disabled by the manifest"
      else
        structuralDefEq manifest env levelParams ctx left (← natLiteralConstructorSpine env value)
  | .app leftFn leftArg, .app rightFn rightArg =>
      structuralDefEq manifest env levelParams ctx leftFn rightFn
      structuralDefEq manifest env levelParams ctx leftArg rightArg
  | .lam _ leftType leftBody, .lam _ rightType rightBody =>
      structuralDefEq manifest env levelParams ctx leftType rightType
      structuralDefEq manifest env levelParams (ctx.extend "_" leftType) leftBody rightBody
  | .forallE _ leftType leftBody, .forallE _ rightType rightBody =>
      structuralDefEq manifest env levelParams ctx leftType rightType
      structuralDefEq manifest env levelParams (ctx.extend "_" leftType) leftBody rightBody
  | .letE _ _ leftValue leftBody, _ =>
      structuralDefEq manifest env levelParams ctx (Expr.instantiate1 leftBody leftValue) right
  | _, .letE _ _ rightValue rightBody =>
      structuralDefEq manifest env levelParams ctx left (Expr.instantiate1 rightBody rightValue)
  | .proj leftStruct leftIndex leftTarget, .proj rightStruct rightIndex rightTarget =>
      if leftStruct == rightStruct && leftIndex == rightIndex then
        structuralDefEq manifest env levelParams ctx leftTarget rightTarget
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
    defEq manifest env levelParams ctx leftType rightType
    isPropExpr manifest env levelParams ctx leftType

partial def defEq (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (ctx : Context) (left right : Expr) : Result Unit := do
  match structuralDefEq manifest env levelParams ctx left right with
  | .ok () => pure ()
  | .error _ => proofIrrelevanceDefEq manifest env levelParams ctx left right

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

def getAppHeadName? (expr : Expr) : Option Name :=
  match expr.getAppFnArgs.1 with
  | .const name _ => some name
  | _ => none

partial def simpleStrictlyPositive (target : Name) (expr : Expr) : Bool :=
  if getAppHeadName? expr == some target then
    true
  else
    match expr with
    | .forallE _ domain body =>
        !containsConst target domain && simpleStrictlyPositive target body
    | _ => !containsConst target expr

end MPC
