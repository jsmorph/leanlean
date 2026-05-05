import MPC.Env

namespace MPC.Packages.Projection

open MPC

-- Avoid exported sparse matchers for structure and constructor-shape checks.
set_option backward.match.sparseCases false in
def fieldType (env : Env) (structureName : Name) (fieldIndex : Nat)
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
                  let levelSubst := levelParams.zip levels
                  pure
                    ((field.type.instantiateLevels levelSubst).instantiateSourceArgs
                      (targetArgs ++ previousFields))
              | _ => fail s!"projection target {structureName} is not a one-constructor structure"
        | some _ => fail s!"projection target {structureName} is not an inductive type"
        | none => fail s!"unknown projection structure: {structureName}"
  | _ => fail s!"projection target type is not a structure application: {repr targetType}"

-- Avoid an exported sparse matcher for the constructor-kind test.
set_option backward.match.sparseCases false in
partial def reduce? (whnfFn : Manifest → Env → LevelContext → Expr → Result Expr)
    (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (structureName : Name) (fieldIndex : Nat) (target : Expr) : Result (Option Expr) := do
  if !manifest.supportsProjections then
    pure none
  else
    let targetWhnf ← whnfFn manifest env levelParams target
    let (head, args) := targetWhnf.getAppFnArgs
    match head with
    | Expr.const ctorName _ =>
        match env.find? ctorName with
        | some { kind := .constructor inductiveName _ fieldCount, .. } =>
            if inductiveName != structureName || fieldIndex >= fieldCount then
              pure none
            else
              match env.find? structureName with
              | some { kind := .inductiveType spec, .. } =>
                  match spec.constructors with
                  | [_] =>
                      pure (listGet? (args.drop spec.params.length) fieldIndex)
                  | _ => pure none
              | _ => pure none
        | _ => pure none
    | _ => pure none

end MPC.Packages.Projection
