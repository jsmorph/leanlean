import MPC.Level

namespace MPC

inductive Literal where
  | nat : Nat → Literal
  | str : String → Literal
  deriving BEq, Repr, Inhabited

inductive Expr where
  | bvar : Nat → Expr
  | sort : Level → Expr
  | const : Name → List Level → Expr
  | lit : Literal → Expr
  | app : Expr → Expr → Expr
  | lam : Name → Expr → Expr → Expr
  | forallE : Name → Expr → Expr → Expr
  | letE : Name → Expr → Expr → Expr → Expr
  deriving BEq, Repr, Inhabited

def Expr.mkApps (fn : Expr) : List Expr → Expr
  | [] => fn
  | arg :: args => Expr.mkApps (.app fn arg) args

partial def Expr.liftFrom (amount cutoff : Nat) : Expr → Expr
  | .bvar index =>
      if cutoff <= index then .bvar (index + amount) else .bvar index
  | .sort level => .sort level
  | .const name levels => .const name levels
  | .lit literal => .lit literal
  | .app fn arg => .app (fn.liftFrom amount cutoff) (arg.liftFrom amount cutoff)
  | .lam name type body =>
      .lam name (type.liftFrom amount cutoff) (body.liftFrom amount (cutoff + 1))
  | .forallE name type body =>
      .forallE name (type.liftFrom amount cutoff) (body.liftFrom amount (cutoff + 1))
  | .letE name type value body =>
      .letE name
        (type.liftFrom amount cutoff)
        (value.liftFrom amount cutoff)
        (body.liftFrom amount (cutoff + 1))

def Expr.lift (amount : Nat) (expr : Expr) : Expr :=
  expr.liftFrom amount 0

partial def Expr.instantiateAt (depth : Nat) (value : Expr) : Expr → Expr
  | .bvar index =>
      if index == depth then
        value.liftFrom depth 0
      else if depth < index then
        .bvar (index - 1)
      else
        .bvar index
  | .sort level => .sort level
  | .const name levels => .const name levels
  | .lit literal => .lit literal
  | .app fn arg => .app (fn.instantiateAt depth value) (arg.instantiateAt depth value)
  | .lam name type body =>
      .lam name (type.instantiateAt depth value) (body.instantiateAt (depth + 1) value)
  | .forallE name type body =>
      .forallE name (type.instantiateAt depth value) (body.instantiateAt (depth + 1) value)
  | .letE name type letValue body =>
      .letE name
        (type.instantiateAt depth value)
        (letValue.instantiateAt depth value)
        (body.instantiateAt (depth + 1) value)

def Expr.instantiate1 (body value : Expr) : Expr :=
  body.instantiateAt 0 value

partial def Expr.instantiateLevels (subst : List (Name × Level)) : Expr → Expr
  | .bvar index => .bvar index
  | .sort level => .sort (level.instantiate subst)
  | .const name levels => .const name (levels.map (·.instantiate subst))
  | .lit literal => .lit literal
  | .app fn arg => .app (fn.instantiateLevels subst) (arg.instantiateLevels subst)
  | .lam name type body =>
      .lam name (type.instantiateLevels subst) (body.instantiateLevels subst)
  | .forallE name type body =>
      .forallE name (type.instantiateLevels subst) (body.instantiateLevels subst)
  | .letE name type value body =>
      .letE name
        (type.instantiateLevels subst)
        (value.instantiateLevels subst)
        (body.instantiateLevels subst)

end MPC
