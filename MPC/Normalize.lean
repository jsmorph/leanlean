import MPC.Packages.Inductive.Reduction
import MPC.Packages.PrimitiveNat
import MPC.Packages.Projection

namespace MPC

mutual

partial def reduceQuotLift? (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (_levels : List Level) (args : List Expr) : Result (Option Expr) := do
  if !manifest.supportsQuotients then
    pure none
  else
    let required := 6
    if args.length < required then
      pure none
    else
      let some typeArg := listGet? args 0
        | pure none
      let some relationArg := listGet? args 1
        | pure none
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
              let some mkTypeArg := listGet? quotientArgs 0
                | pure none
              let some mkRelationArg := listGet? quotientArgs 1
                | pure none
              let some valueArg := listGet? quotientArgs 2
                | pure none
              if mkTypeArg.alphaEq typeArg && mkRelationArg.alphaEq relationArg then
                pure (some (Expr.mkApps (.app fnArg valueArg) trailing))
              else
                pure none
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
        let aWhnf ← whnf manifest env levelParams aArg
        let bWhnf ← whnf manifest env levelParams bArg
        if aWhnf.alphaEq bWhnf then
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

partial def whnf (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (expr : Expr) : Result Expr := do
  match expr with
  | .letE _ _ value body =>
      whnf manifest env levelParams (Expr.instantiate1 body value)
  | .proj structureName fieldIndex target => do
      match ←
          MPC.Packages.Projection.reduce? whnf manifest env levelParams structureName
            fieldIndex target with
      | some reduced => whnf manifest env levelParams reduced
      | none => pure (.proj structureName fieldIndex target)
  | .app fn arg =>
      let appExpr := Expr.app fn arg
      let (head, args) := Expr.getAppFnArgs appExpr
      let primitiveReduction? ←
        match head with
        | .const name levels =>
            match env.find? name with
            | some info =>
                MPC.Packages.PrimitiveNat.reduce? whnf manifest env levelParams name info levels args
            | none => pure none
        | _ => pure none
      match primitiveReduction? with
      | some reduced => whnf manifest env levelParams reduced
      | none =>
          let head ← whnf manifest env levelParams head
          match head with
          | Expr.const name levels =>
              match env.find? name with
              | some { kind := .recursor info, .. } =>
                  match ← reduceSimpleRecursor? whnf manifest env levelParams name info levels args with
                  | some reduced => whnf manifest env levelParams reduced
                  | none => pure (Expr.mkApps head args)
              | some { kind := .mutualRecursor info, .. } =>
                  match ← reduceMutualRecursor? whnf manifest env levelParams name info levels args with
                  | some reduced => whnf manifest env levelParams reduced
                  | none => pure (Expr.mkApps head args)
              | some { kind := .indexedRecursor info, .. } =>
                  match ← reduceIndexedRecursor? whnf manifest env levelParams name info levels args with
                  | some reduced => whnf manifest env levelParams reduced
                  | none => pure (Expr.mkApps head args)
              | some { kind := .nestedRecursor info, .. } =>
                  match ← reduceNestedRecursor? whnf manifest env levelParams name info levels args with
                  | some reduced => whnf manifest env levelParams reduced
                  | none => pure (Expr.mkApps head args)
              | some { kind := .quotientLift, .. } =>
                  match ← reduceQuotLift? manifest env levelParams levels args with
                  | some reduced => whnf manifest env levelParams reduced
                  | none => pure (Expr.mkApps head args)
              | some { kind := .equalityRec, .. } =>
                  match ← reduceEqRec? manifest env levelParams args with
                  | some reduced => whnf manifest env levelParams reduced
                  | none => pure (Expr.mkApps head args)
              | some { kind := .equalityNdRec, .. } =>
                  match ← reduceEqRec? manifest env levelParams args with
                  | some reduced => whnf manifest env levelParams reduced
                  | none => pure (Expr.mkApps head args)
              | _ => pure (Expr.mkApps head args)
          | .lam _ _ body =>
              match args with
              | first :: rest =>
                  whnf manifest env levelParams (Expr.mkApps (Expr.instantiate1 body first) rest)
              | [] => pure head
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
