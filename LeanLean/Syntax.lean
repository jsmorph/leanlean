namespace LeanLean

abbrev Name := String

inductive Level where
  | zero : Level
  | param : Name → Level
  | succ : Level → Level
  | max : Level → Level → Level
  | imax : Level → Level → Level
  deriving DecidableEq, Repr, Inhabited

namespace Level

structure Summand where
  name? : Option Name
  offset : Nat
  deriving DecidableEq, Repr, Inhabited

def ofNat : Nat → Level
  | 0 => .zero
  | n + 1 => .succ (ofNat n)

instance instOfNatLevel (n : Nat) : OfNat Level n where
  ofNat := ofNat n

def closed : Level → Bool
  | .zero => true
  | .param _ => false
  | .succ level => closed level
  | .max left right => closed left && closed right
  | .imax left right => closed left && closed right

def closedIn (params : List Name) : Level → Bool
  | .zero => true
  | .param name => params.contains name
  | .succ level => closedIn params level
  | .max left right => closedIn params left && closedIn params right
  | .imax left right => closedIn params left && closedIn params right

def bumpSummands : List Summand → List Summand :=
  List.map fun summand => { summand with offset := summand.offset + 1 }

def mergeSummand (summand : Summand) : List Summand → List Summand
  | [] => [summand]
  | entry :: rest =>
      if entry.name? = summand.name? then
        { entry with offset := Nat.max entry.offset summand.offset } :: rest
      else
        entry :: mergeSummand summand rest

def mergeSummands (left right : List Summand) : List Summand :=
  right.foldl (fun acc summand => mergeSummand summand acc) left

def normalizeSummands? : Level → Option (List Summand)
  | .zero => some [{ name? := none, offset := 0 }]
  | .param name => some [{ name? := some name, offset := 0 }]
  | .succ level => bumpSummands <$> normalizeSummands? level
  | .max left right => do
      let left ← normalizeSummands? left
      let right ← normalizeSummands? right
      pure (mergeSummands left right)
  | .imax _ _ => none
termination_by level => level

def normalizeSummands (level : Level) : List Summand :=
  match normalizeSummands? level with
  | some summands => summands
  | none => panic! s!"cannot flatten unresolved imax level {repr level}"

def toLevel : Summand → Level
  | { name? := none, offset } => ofNat offset
  | { name? := some name, offset } =>
      Nat.rec (.param name) (fun _ acc => .succ acc) offset

def fromSummands : List Summand → Level
  | [] => .zero
  | summand :: rest =>
      rest.foldl (fun acc entry => .max acc (toLevel entry)) (toLevel summand)

def reduceIMax : Level → Level
  | .zero => .zero
  | .param name => .param name
  | .succ level => .succ (reduceIMax level)
  | .max left right => .max (reduceIMax left) (reduceIMax right)
  | .imax left right =>
      let left := reduceIMax left
      let right := reduceIMax right
      match right with
      | .zero => .zero
      | .succ _ => .max left right
      | _ =>
          match normalizeSummands? right with
          | some summands =>
              if summands.any fun summand => 0 < summand.offset then
                .max left right
              else
                .imax left right
          | none => .imax left right
termination_by level => level

partial def normalize : Level → Level
  | level =>
      let reduced := reduceIMax level
      match normalizeSummands? reduced with
      | some summands => fromSummands summands
      | none =>
          match reduced with
          | .succ level => .succ (normalize level)
          | .max left right => .max (normalize left) (normalize right)
          | .imax left right => .imax (normalize left) (normalize right)
          | other => other

def closedEval? (level : Level) : Option Nat :=
  match normalizeSummands? (normalize level) with
  | some summands =>
      if summands.all fun summand => summand.name?.isNone then
        some (summands.foldl (fun acc summand => Nat.max acc summand.offset) 0)
      else
        none
  | none => none

def definitelyPositive (level : Level) : Bool :=
  match normalizeSummands? (normalize level) with
  | some summands => summands.any fun summand => 0 < summand.offset
  | none => false

def eval (level : Level) : Nat :=
  match closedEval? level with
  | some value => value
  | none => panic! s!"attempted to evaluate open universe level {repr level}"

partial def defEq (left right : Level) : Bool :=
  let left := normalize left
  let right := normalize right
  match normalizeSummands? left, normalizeSummands? right with
  | some leftN, some rightN =>
      leftN.length = rightN.length &&
        leftN.all fun summand => rightN.any fun other => other = summand
  | _, _ =>
      match left, right with
      | .zero, .zero => true
      | .param left, .param right => left = right
      | .succ left, .succ right => defEq left right
      | .max leftA leftB, .max rightA rightB =>
          (defEq leftA rightA && defEq leftB rightB) ||
            (defEq leftA rightB && defEq leftB rightA)
      | .imax leftA leftB, .imax rightA rightB =>
          defEq leftA rightA && defEq leftB rightB
      | _, _ => false

def summandLe (left right : Summand) : Bool :=
  match left.name?, right.name? with
  | none, none => left.offset <= right.offset
  | none, some _ => left.offset = 0 || left.offset <= right.offset
  | some leftName, some rightName => leftName = rightName && left.offset <= right.offset
  | some _, none => false

def le (left right : Level) : Bool :=
  let left := normalize left
  let right := normalize right
  match normalizeSummands? left, normalizeSummands? right with
  | some leftN, some rightN =>
      leftN.all fun leftSummand =>
        rightN.any fun rightSummand => summandLe leftSummand rightSummand
  | _, _ => defEq left right

def instantiate (params : List Name) (values : List Level) : Level → Level
  | .zero => .zero
  | .param name =>
      match List.zip params values |>.find? (fun pair => pair.1 = name) with
      | some (_, value) => value
      | none => .param name
  | .succ level => .succ (instantiate params values level)
  | .max left right => .max (instantiate params values left) (instantiate params values right)
  | .imax left right => .imax (instantiate params values left) (instantiate params values right)
termination_by level => level

end Level

inductive Expr where
  | bvar : Nat → Expr
  | sort : Level → Expr
  | const : Name → List Level → Expr
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
  | .sort level => level.closed
  | .const _ levels => levels.all Level.closed
  | .app fn arg => closedAt depth fn && closedAt depth arg
  | .lam _ ty body => closedAt depth ty && closedAt (depth + 1) body
  | .forallE _ ty body => closedAt depth ty && closedAt (depth + 1) body
  | .letE _ ty val body =>
      closedAt depth ty && closedAt depth val && closedAt (depth + 1) body

def closed (expr : Expr) : Bool :=
  closedAt 0 expr

def closedAtIn (params : List Name) (depth : Nat) : Expr → Bool
  | .bvar index => index < depth
  | .sort level => level.closedIn params
  | .const _ levels => levels.all (Level.closedIn params)
  | .app fn arg => closedAtIn params depth fn && closedAtIn params depth arg
  | .lam _ ty body => closedAtIn params depth ty && closedAtIn params (depth + 1) body
  | .forallE _ ty body => closedAtIn params depth ty && closedAtIn params (depth + 1) body
  | .letE _ ty val body =>
      closedAtIn params depth ty && closedAtIn params depth val && closedAtIn params (depth + 1) body

def closedIn (params : List Name) (expr : Expr) : Bool :=
  closedAtIn params 0 expr

def alphaEq : Expr → Expr → Bool
  | .bvar left, .bvar right => left = right
  | .sort left, .sort right => Level.defEq left right
  | .const leftName leftLevels, .const rightName rightLevels =>
      leftName = rightName &&
      leftLevels.length = rightLevels.length &&
      (List.zip leftLevels rightLevels).all fun pair => Level.defEq pair.1 pair.2
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
  | .const name _ => name = target
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
  | .const name levels => .const name levels
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
  | .const name levels => some (.const name levels)
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
  | .const name levels => .const name levels
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

def listGet? : List α → Nat → Option α
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: rest, index + 1 => listGet? rest index

def instantiateManyFrom (cutoff : Nat) (values : List Expr) : Expr → Expr
  | .bvar index =>
      if index < cutoff then
        .bvar index
      else
        let rel := index - cutoff
        if rel < values.length then
          match listGet? values (values.length - 1 - rel) with
          | some value => .lift cutoff value
          | none => panic! "invalid simultaneous instantiation index"
        else
          .bvar (index - values.length)
  | .sort level => .sort level
  | .const name levels => .const name levels
  | .app fn arg =>
      .app (instantiateManyFrom cutoff values fn) (instantiateManyFrom cutoff values arg)
  | .lam name ty body =>
      .lam
        name
        (instantiateManyFrom cutoff values ty)
        (instantiateManyFrom (cutoff + 1) values body)
  | .forallE name ty body =>
      .forallE
        name
        (instantiateManyFrom cutoff values ty)
        (instantiateManyFrom (cutoff + 1) values body)
  | .letE name ty val body =>
      .letE
        name
        (instantiateManyFrom cutoff values ty)
        (instantiateManyFrom cutoff values val)
        (instantiateManyFrom (cutoff + 1) values body)
termination_by expr => expr

def instantiateMany (values : List Expr) (body : Expr) : Expr :=
  instantiateManyFrom 0 values body

def instantiateLevels (params : List Name) (values : List Level) : Expr → Expr
  | .bvar index => .bvar index
  | .sort level => .sort (Level.instantiate params values level)
  | .const name levels =>
      .const name (levels.map (Level.instantiate params values))
  | .app fn arg =>
      .app (instantiateLevels params values fn) (instantiateLevels params values arg)
  | .lam name ty body =>
      .lam
        name
        (instantiateLevels params values ty)
        (instantiateLevels params values body)
  | .forallE name ty body =>
      .forallE
        name
        (instantiateLevels params values ty)
        (instantiateLevels params values body)
  | .letE name ty val body =>
      .letE
        name
        (instantiateLevels params values ty)
        (instantiateLevels params values val)
        (instantiateLevels params values body)
termination_by expr => expr

end Expr

end LeanLean
