import MPC.Declaration
import MPC.Normalize
import MPC.Packages.Literal
import MPC.Packages.Projection

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
        MPC.Packages.Literal.requireNatSupport env
        pure (.const "Nat" [])
  | .lit (.str _) => do
      if !manifest.supportsStringLiterals then
        fail "string literals are disabled by the manifest"
      else
        MPC.Packages.Literal.requireStringSupport env
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
        MPC.Packages.Projection.fieldType env structureName fieldIndex target targetType

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
        structuralDefEq manifest env levelParams ctx
          (← MPC.Packages.Literal.natConstructorSpine env value) right
  | _, .lit (.nat value) =>
      if !manifest.supportsNatLiterals then
        fail "natural literals are disabled by the manifest"
      else
        structuralDefEq manifest env levelParams ctx left
          (← MPC.Packages.Literal.natConstructorSpine env value)
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

end MPC
