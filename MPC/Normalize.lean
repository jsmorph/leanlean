import MPC.Env

namespace MPC

partial def whnf (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (expr : Expr) : Result Expr := do
  match expr with
  | .letE _ _ value body =>
      whnf manifest env levelParams (body.instantiate1 value)
  | .app fn arg =>
      let fn ← whnf manifest env levelParams fn
      match fn with
      | .lam _ _ body =>
          whnf manifest env levelParams (body.instantiate1 arg)
      | _ => pure (.app fn arg)
  | .const name levels =>
      match env.find? name with
      | some info =>
          match info.kind, info.instantiateValue? levels with
          | .definition, some value =>
              whnf manifest env levelParams value
          | _, _ => pure (.const name levels)
      | none => pure (.const name levels)
  | _ => pure expr

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
  | _ => pure expr

end MPC
