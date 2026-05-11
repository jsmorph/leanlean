import MPC.Packages.Inductive.Reduction
import MPC.Packages.PrimitiveNat
import MPC.Packages.Projection

namespace MPC

def sameConst (leftName : Name) (leftLevels : List Level)
    (rightName : Name) (rightLevels : List Level) : Bool :=
  leftName == rightName &&
    leftLevels.length == rightLevels.length &&
    (leftLevels.zip rightLevels).all fun pair => pair.1.defEq pair.2

mutual

partial def whnfAlphaEq (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (left right : Expr) : Result Bool := do
  let left ← whnf manifest env levelParams left
  let right ← whnf manifest env levelParams right
  match left, right with
  | .bvar left, .bvar right => pure (left == right)
  | .sort left, .sort right => pure (left.defEq right)
  | .const leftName leftLevels, .const rightName rightLevels =>
      pure
        (leftName == rightName &&
          leftLevels.length == rightLevels.length &&
          (leftLevels.zip rightLevels).all fun pair => pair.1.defEq pair.2)
  | .lit left, .lit right => pure (left == right)
  | .app leftFn leftArg, .app rightFn rightArg => do
      if ← whnfAlphaEq manifest env levelParams leftFn rightFn then
        whnfAlphaEq manifest env levelParams leftArg rightArg
      else
        pure false
  | .lam _ leftType leftBody, .lam _ rightType rightBody => do
      if ← whnfAlphaEq manifest env levelParams leftType rightType then
        whnfAlphaEq manifest env levelParams leftBody rightBody
      else
        pure false
  | .forallE _ leftType leftBody, .forallE _ rightType rightBody => do
      if ← whnfAlphaEq manifest env levelParams leftType rightType then
        whnfAlphaEq manifest env levelParams leftBody rightBody
      else
        pure false
  | .letE _ _ leftValue leftBody, _ =>
      whnfAlphaEq manifest env levelParams (Expr.instantiate1 leftBody leftValue) right
  | _, .letE _ _ rightValue rightBody =>
      whnfAlphaEq manifest env levelParams left (Expr.instantiate1 rightBody rightValue)
  | .proj leftStruct leftIndex leftTarget, .proj rightStruct rightIndex rightTarget =>
      if leftStruct == rightStruct && leftIndex == rightIndex then
        whnfAlphaEq manifest env levelParams leftTarget rightTarget
      else
        pure false
  | _, _ => pure false

partial def reduceQuotLift? (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (_levels : List Level) (args : List Expr) : Result (Option Expr) := do
  if !manifest.supportsQuotients then
    pure none
  else
    let required := 6
    if args.length < required then
      pure none
    else
      let some fnArg := listGet? args 3
        | pure none
      let some quotientArg := listGet? args 5
        | pure none
      let trailing := args.drop required
      let quotientWhnf ← whnf manifest env levelParams quotientArg
      let (quotientHead, quotientArgs) := quotientWhnf.getAppFnArgs
      match quotientHead with
      | Expr.const mkName _ =>
          match env.find? mkName with
          | some { kind := .quotientMk, .. } =>
              let some valueArg := listGet? quotientArgs 2
                | pure none
              pure (some (Expr.mkApps (.app fnArg valueArg) trailing))
          | _ => pure none
      | _ => pure none

partial def reduceEqRec? (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (args : List Expr) : Result (Option Expr) := do
  if !manifest.supportsEquality then
    pure none
  else
    let required := 6
    if args.length < required then
      pure none
    else
      let some typeArg := listGet? args 0
        | pure none
      let some aArg := listGet? args 1
        | pure none
      let some minorArg := listGet? args 3
        | pure none
      let some bArg := listGet? args 4
        | pure none
      let some proofArg := listGet? args 5
        | pure none
      let trailing := args.drop required
      let proofWhnf ← whnf manifest env levelParams proofArg
      let (proofHead, proofArgs) := proofWhnf.getAppFnArgs
      let reduceToMinorIfEndpointsMatch : Result (Option Expr) := do
        if ← whnfAlphaEq manifest env levelParams aArg bArg then
          pure (some (Expr.mkApps minorArg trailing))
        else
          pure none
      match proofHead with
      | Expr.const reflName _ =>
          match env.find? reflName with
          | some { kind := .equalityRefl, .. } =>
              let some reflTypeArg := listGet? proofArgs 0
                | pure none
              let some reflValueArg := listGet? proofArgs 1
                | pure none
              if reflTypeArg == typeArg && reflValueArg == aArg && bArg == aArg then
                pure (some (Expr.mkApps minorArg trailing))
              else
                reduceToMinorIfEndpointsMatch
          | _ => reduceToMinorIfEndpointsMatch
      | _ => reduceToMinorIfEndpointsMatch

partial def reduceConstantApp? (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (name : Name) (levels : List Level) (args : List Expr) : Result (Option Expr) := do
  match env.find? name with
  | some info =>
      match ←
          MPC.Packages.PrimitiveNat.reduce? whnf manifest env levelParams name info levels args with
      | some reduced => pure (some reduced)
      | none =>
          match ←
              MPC.Packages.Projection.reduceConstant? whnf manifest env levelParams name levels args with
          | some reduced => pure (some reduced)
          | none =>
              match info.kind with
              | .recursor info =>
                  reduceSimpleRecursor? whnf manifest env levelParams name info levels args
              | .mutualRecursor info =>
                  reduceMutualRecursor? whnf manifest env levelParams name info levels args
              | .indexedRecursor info =>
                  reduceIndexedRecursor? whnf manifest env levelParams name info levels args
              | .nestedRecursor info =>
                  reduceNestedRecursor? whnf manifest env levelParams name info levels args
              | .quotientLift =>
                  reduceQuotLift? manifest env levelParams levels args
              | .equalityRec =>
                  reduceEqRec? manifest env levelParams args
              | _ => pure none
  | none => pure none

partial def whnf (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (expr : Expr) : Result Expr := do
  match expr with
  | .letE _ _ value body =>
      whnf manifest env levelParams (Expr.instantiate1 body value)
  | .proj structureName fieldIndex target => do
      if !manifest.supportsProjections then
        pure (.proj structureName fieldIndex target)
      else
        let targetWhnf ← whnf manifest env levelParams target
        match ←
            MPC.Packages.Projection.reduceTarget? manifest env structureName fieldIndex targetWhnf with
        | some reduced => whnf manifest env levelParams reduced
        | none => pure (.proj structureName fieldIndex targetWhnf)
  | .app fn arg =>
      let appExpr := Expr.app fn arg
      let (head, args) := Expr.getAppFnArgs appExpr
      let originalConst? :=
        match head with
        | .const name levels => some (name, levels)
        | _ => none
      match ←
          match originalConst? with
          | some (name, levels) => reduceConstantApp? manifest env levelParams name levels args
          | none => pure none with
      | some reduced => whnf manifest env levelParams reduced
      | none =>
          let head ← whnf manifest env levelParams head
          match head with
          | Expr.const name levels =>
              let unchanged :=
                match originalConst? with
                | some (originalName, originalLevels) =>
                    sameConst name levels originalName originalLevels
                | none => false
              if unchanged then
                pure (Expr.mkApps head args)
              else
                match ← reduceConstantApp? manifest env levelParams name levels args with
                | some reduced => whnf manifest env levelParams reduced
                | none => pure (Expr.mkApps head args)
          | .lam _ _ body =>
              match args with
              | first :: rest =>
                  whnf manifest env levelParams (Expr.mkApps (Expr.instantiate1 body first) rest)
              | [] => pure head
          | .app _ _ =>
              whnf manifest env levelParams (Expr.mkApps head args)
          | _ => pure (Expr.mkApps head args)
  | .const name levels =>
      match env.find? name with
      | some info =>
          match info.kind, info.instantiateValue? levels with
          | .definition, some value =>
              whnf manifest env levelParams value
          | _, _ => pure (.const name levels)
      | none => pure (.const name levels)
  | _ => pure expr

end

partial def normalize (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (expr : Expr) : Result Expr := do
  let expr ← whnf manifest env levelParams expr
  match expr with
  | .app fn arg => pure (.app (← normalize manifest env levelParams fn) (← normalize manifest env levelParams arg))
  | .lam name type body =>
      pure (.lam name (← normalize manifest env levelParams type) (← normalize manifest env levelParams body))
  | .forallE name type body =>
      pure (.forallE name (← normalize manifest env levelParams type) (← normalize manifest env levelParams body))
  | .letE name type value body =>
      pure
        (.letE name
          (← normalize manifest env levelParams type)
          (← normalize manifest env levelParams value)
          (← normalize manifest env levelParams body))
  | .proj structureName fieldIndex target =>
      pure (.proj structureName fieldIndex (← normalize manifest env levelParams target))
  | _ => pure expr

end MPC
