import MPC.Level

namespace MPC

inductive Literal where
  | nat : Nat → Literal
  | str : String → Literal
  deriving BEq, Repr, Inhabited, Hashable

inductive Expr where
  | bvar : Nat → Expr
  | sort : Level → Expr
  | const : Name → List Level → Expr
  | lit : Literal → Expr
  | app : Expr → Expr → Expr
  | lam : Name → Expr → Expr → Expr
  | forallE : Name → Expr → Expr → Expr
  | letE : Name → Expr → Expr → Expr → Expr
  | proj : Name → Nat → Expr → Expr
  deriving BEq, Repr, Inhabited, Hashable

def Expr.mkApps (fn : Expr) : List Expr → Expr
  | [] => fn
  | arg :: args => Expr.mkApps (.app fn arg) args

def Expr.constLevels? : Expr → Option (Name × List Level)
  | .const name levels => some (name, levels)
  | _ => none

partial def Expr.getAppFnArgsAux : Expr → List Expr → Expr × List Expr
  | .app fn arg, args => Expr.getAppFnArgsAux fn (arg :: args)
  | expr, args => (expr, args)

def Expr.getAppFnArgs (expr : Expr) : Expr × List Expr :=
  Expr.getAppFnArgsAux expr []

partial def Expr.liftFrom (amount cutoff : Nat) (expr : Expr) : Expr :=
  if amount == 0 then
    expr
  else
    match expr with
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
    | .proj structureName fieldIndex target =>
        .proj structureName fieldIndex (target.liftFrom amount cutoff)

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
  | .app fn arg =>
      .app (Expr.instantiateAt depth value fn) (Expr.instantiateAt depth value arg)
  | .lam name type body =>
      .lam name
        (Expr.instantiateAt depth value type)
        (Expr.instantiateAt (depth + 1) value body)
  | .forallE name type body =>
      .forallE name
        (Expr.instantiateAt depth value type)
        (Expr.instantiateAt (depth + 1) value body)
  | .letE name type letValue body =>
      .letE name
        (Expr.instantiateAt depth value type)
        (Expr.instantiateAt depth value letValue)
        (Expr.instantiateAt (depth + 1) value body)
  | .proj structureName fieldIndex target =>
      .proj structureName fieldIndex (Expr.instantiateAt depth value target)

def Expr.instantiate1 (body value : Expr) : Expr :=
  Expr.instantiateAt 0 value body

partial def Expr.instantiateManyFrom (cutoff : Nat) (values : List Expr) : Expr → Expr
  | .bvar index =>
      if index < cutoff then
        .bvar index
      else
        let rel := index - cutoff
        if rel < values.length then
          match values[values.length - 1 - rel]? with
          | some value => value.liftFrom cutoff 0
          | none => .bvar index
        else
          .bvar (index - values.length)
  | .sort level => .sort level
  | .const name levels => .const name levels
  | .lit literal => .lit literal
  | .app fn arg =>
      .app (Expr.instantiateManyFrom cutoff values fn) (Expr.instantiateManyFrom cutoff values arg)
  | .lam name type body =>
      .lam name
        (Expr.instantiateManyFrom cutoff values type)
        (Expr.instantiateManyFrom (cutoff + 1) values body)
  | .forallE name type body =>
      .forallE name
        (Expr.instantiateManyFrom cutoff values type)
        (Expr.instantiateManyFrom (cutoff + 1) values body)
  | .letE name type value body =>
      .letE name
        (Expr.instantiateManyFrom cutoff values type)
        (Expr.instantiateManyFrom cutoff values value)
        (Expr.instantiateManyFrom (cutoff + 1) values body)
  | .proj structureName fieldIndex target =>
      .proj structureName fieldIndex (Expr.instantiateManyFrom cutoff values target)

def Expr.instantiateMany (expr : Expr) (values : List Expr) : Expr :=
  Expr.instantiateManyFrom 0 values expr

def Expr.instantiateSourceArgs (expr : Expr) (args : List Expr) : Expr :=
  expr.instantiateMany args

partial def Expr.instantiateLevels (subst : List (Name × Level)) : Expr → Expr
  | expr =>
      if subst.isEmpty then
        expr
      else
        match expr with
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
        | .proj structureName fieldIndex target =>
            .proj structureName fieldIndex (target.instantiateLevels subst)

partial def Expr.alphaEq : Expr → Expr → Bool
  | .bvar left, .bvar right => left == right
  | .sort left, .sort right => left.defEq right
  | .const leftName leftLevels, .const rightName rightLevels =>
      leftName == rightName &&
        leftLevels.length == rightLevels.length &&
        (leftLevels.zip rightLevels).all fun pair => pair.1.defEq pair.2
  | .lit left, .lit right => left == right
  | .app leftFn leftArg, .app rightFn rightArg =>
      leftFn.alphaEq rightFn && leftArg.alphaEq rightArg
  | .lam _ leftType leftBody, .lam _ rightType rightBody =>
      leftType.alphaEq rightType && leftBody.alphaEq rightBody
  | .forallE _ leftType leftBody, .forallE _ rightType rightBody =>
      leftType.alphaEq rightType && leftBody.alphaEq rightBody
  | .letE _ leftType leftValue leftBody, .letE _ rightType rightValue rightBody =>
      leftType.alphaEq rightType && leftValue.alphaEq rightValue && leftBody.alphaEq rightBody
  | .proj leftStruct leftIndex leftTarget, .proj rightStruct rightIndex rightTarget =>
      leftStruct == rightStruct && leftIndex == rightIndex && leftTarget.alphaEq rightTarget
  | _, _ => false

end MPC
