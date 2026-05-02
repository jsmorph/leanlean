namespace LeanLean

abbrev Name := String

inductive Level where
  | zero : Level
  | succ : Level → Level
  | max : Level → Level → Level
  deriving DecidableEq, Repr, Inhabited

namespace Level

def ofNat : Nat → Level
  | 0 => .zero
  | n + 1 => .succ (ofNat n)

instance instOfNatLevel (n : Nat) : OfNat Level n where
  ofNat := ofNat n

def eval : Level → Nat
  | .zero => 0
  | .succ level => eval level + 1
  | .max left right => Nat.max (eval left) (eval right)

def normalize (level : Level) : Level :=
  ofNat (eval level)

def defEq (left right : Level) : Bool :=
  eval left = eval right

def le (left right : Level) : Bool :=
  eval left <= eval right

end Level

inductive Expr where
  | bvar : Nat → Expr
  | sort : Level → Expr
  | const : Name → Expr
  | app : Expr → Expr → Expr
  | lam : String → Expr → Expr → Expr
  | forallE : String → Expr → Expr → Expr
  | letE : String → Expr → Expr → Expr → Expr
  deriving DecidableEq, Repr, Inhabited

namespace Expr

def mkApps (fn : Expr) : List Expr → Expr
  | [] => fn
  | arg :: args => mkApps (.app fn arg) args

def collectAppRev (expr : Expr) (args : List Expr) : Expr × List Expr :=
  match expr with
  | .app fn arg => collectAppRev fn (arg :: args)
  | _ => (expr, args)
termination_by expr

def getAppFn (expr : Expr) : Expr :=
  (collectAppRev expr []).1

def getAppArgs (expr : Expr) : List Expr :=
  (collectAppRev expr []).2

def bvarArgs (count inner : Nat) : List Expr :=
  (List.range count).map fun index => .bvar (inner + count - 1 - index)

def closedAt (depth : Nat) : Expr → Bool
  | .bvar index => index < depth
  | .sort _ => true
  | .const _ => true
  | .app fn arg => closedAt depth fn && closedAt depth arg
  | .lam _ ty body => closedAt depth ty && closedAt (depth + 1) body
  | .forallE _ ty body => closedAt depth ty && closedAt (depth + 1) body
  | .letE _ ty val body =>
      closedAt depth ty && closedAt depth val && closedAt (depth + 1) body

def closed (expr : Expr) : Bool :=
  closedAt 0 expr

def alphaEq : Expr → Expr → Bool
  | .bvar left, .bvar right => left = right
  | .sort left, .sort right => Level.defEq left right
  | .const left, .const right => left = right
  | .app leftFn leftArg, .app rightFn rightArg =>
      alphaEq leftFn rightFn && alphaEq leftArg rightArg
  | .lam _ leftTy leftBody, .lam _ rightTy rightBody =>
      alphaEq leftTy rightTy && alphaEq leftBody rightBody
  | .forallE _ leftTy leftBody, .forallE _ rightTy rightBody =>
      alphaEq leftTy rightTy && alphaEq leftBody rightBody
  | .letE _ leftTy leftVal leftBody, .letE _ rightTy rightVal rightBody =>
      alphaEq leftTy rightTy &&
      alphaEq leftVal rightVal &&
      alphaEq leftBody rightBody
  | _, _ => false

def occursConst (target : Name) : Expr → Bool
  | .bvar _ => false
  | .sort _ => false
  | .const name => name = target
  | .app fn arg => occursConst target fn || occursConst target arg
  | .lam _ ty body => occursConst target ty || occursConst target body
  | .forallE _ ty body => occursConst target ty || occursConst target body
  | .letE _ ty val body =>
      occursConst target ty || occursConst target val || occursConst target body

def liftFrom (cutoff delta : Nat) : Expr → Expr
  | .bvar index =>
      if index < cutoff then
        .bvar index
      else
        .bvar (index + delta)
  | .sort level => .sort level
  | .const name => .const name
  | .app fn arg => .app (liftFrom cutoff delta fn) (liftFrom cutoff delta arg)
  | .lam name ty body =>
      .lam name (liftFrom cutoff delta ty) (liftFrom (cutoff + 1) delta body)
  | .forallE name ty body =>
      .forallE name (liftFrom cutoff delta ty) (liftFrom (cutoff + 1) delta body)
  | .letE name ty val body =>
      .letE
        name
        (liftFrom cutoff delta ty)
        (liftFrom cutoff delta val)
        (liftFrom (cutoff + 1) delta body)

def lift (delta : Nat) (expr : Expr) : Expr :=
  liftFrom 0 delta expr

def lowerFrom (cutoff delta : Nat) : Expr → Option Expr
  | .bvar index =>
      if index < cutoff then
        some (.bvar index)
      else if delta <= index then
        some (.bvar (index - delta))
      else
        none
  | .sort level => some (.sort level)
  | .const name => some (.const name)
  | .app fn arg => do
      let fn' ← lowerFrom cutoff delta fn
      let arg' ← lowerFrom cutoff delta arg
      pure (.app fn' arg')
  | .lam name ty body => do
      let ty' ← lowerFrom cutoff delta ty
      let body' ← lowerFrom (cutoff + 1) delta body
      pure (.lam name ty' body')
  | .forallE name ty body => do
      let ty' ← lowerFrom cutoff delta ty
      let body' ← lowerFrom (cutoff + 1) delta body
      pure (.forallE name ty' body')
  | .letE name ty val body => do
      let ty' ← lowerFrom cutoff delta ty
      let val' ← lowerFrom cutoff delta val
      let body' ← lowerFrom (cutoff + 1) delta body
      pure (.letE name ty' val' body')

def lower (delta : Nat) (expr : Expr) : Option Expr :=
  lowerFrom 0 delta expr

def instantiateFrom (cutoff : Nat) (value : Expr) : Expr → Expr
  | .bvar index =>
      if index < cutoff then
        .bvar index
      else if index = cutoff then
        .lift cutoff value
      else
        .bvar (index - 1)
  | .sort level => .sort level
  | .const name => .const name
  | .app fn arg =>
      .app (instantiateFrom cutoff value fn) (instantiateFrom cutoff value arg)
  | .lam name ty body =>
      .lam
        name
        (instantiateFrom cutoff value ty)
        (instantiateFrom (cutoff + 1) value body)
  | .forallE name ty body =>
      .forallE
        name
        (instantiateFrom cutoff value ty)
        (instantiateFrom (cutoff + 1) value body)
  | .letE name ty val body =>
      .letE
        name
        (instantiateFrom cutoff value ty)
        (instantiateFrom cutoff value val)
        (instantiateFrom (cutoff + 1) value body)

def instantiate1 (value body : Expr) : Expr :=
  instantiateFrom 0 value body

def instantiateMany (values : List Expr) (body : Expr) : Expr :=
  values.reverse.foldl (fun acc value => instantiate1 value acc) body

end Expr

end LeanLean
