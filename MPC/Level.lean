import MPC.Name

namespace MPC

inductive Level where
  | zero
  | param : Name → Level
  | succ : Level → Level
  | max : Level → Level → Level
  | imax : Level → Level → Level
  deriving BEq, Repr, Inhabited

namespace Level

structure Summand where
  name? : Option Name
  offset : Nat
  deriving BEq, Repr, Inhabited

def ofNat : Nat → Level
  | 0 => .zero
  | n + 1 => .succ (ofNat n)

def bumpSummands : List Summand → List Summand :=
  List.map fun summand => { summand with offset := summand.offset + 1 }

def mergeSummand (summand : Summand) : List Summand → List Summand
  | [] => [summand]
  | entry :: rest =>
      if entry.name? == summand.name? then
        { entry with offset := Nat.max entry.offset summand.offset } :: rest
      else
        entry :: mergeSummand summand rest

def mergeSummands (left right : List Summand) : List Summand :=
  right.foldl (fun acc summand => mergeSummand summand acc) left

def summandToLevel : Summand → Level
  | { name? := none, offset } => ofNat offset
  | { name? := some name, offset } =>
      Nat.rec (.param name) (fun _ acc => .succ acc) offset

def fromSummands : List Summand → Level
  | [] => .zero
  | summand :: rest =>
      rest.foldl (fun acc entry => .max acc (summandToLevel entry)) (summandToLevel summand)

def summandLe (left right : Summand) : Bool :=
  match left.name?, right.name? with
  | none, none => left.offset <= right.offset
  | none, some _ => left.offset == 0 || left.offset <= right.offset
  | some leftName, some rightName => leftName == rightName && left.offset <= right.offset
  | some _, none => false

end Level

abbrev LevelContext := List Name

def LevelContext.contains (ctx : LevelContext) (name : Name) : Bool :=
  ctx.any (fun other => other == name)

def LevelContext.lookup? (subst : List (Name × Level)) (name : Name) : Option Level :=
  match subst with
  | [] => none
  | (other, value) :: rest =>
      if other == name then some value else lookup? rest name

partial def Level.closedIn (ctx : LevelContext) : Level → Bool
  | .zero => true
  | .param name => ctx.contains name
  | .succ level => level.closedIn ctx
  | .max left right => left.closedIn ctx && right.closedIn ctx
  | .imax left right => left.closedIn ctx && right.closedIn ctx

partial def Level.instantiate (subst : List (Name × Level)) : Level → Level
  | level =>
      if subst.isEmpty then
        level
      else
        match level with
        | .zero => .zero
        | .param name =>
            match LevelContext.lookup? subst name with
            | some value => value
            | none => .param name
        | .succ level => .succ (level.instantiate subst)
        | .max left right => .max (left.instantiate subst) (right.instantiate subst)
        | .imax left right => .imax (left.instantiate subst) (right.instantiate subst)

def Level.normalizeSummands? : Level → Option (List Level.Summand)
  | .zero => some [{ name? := none, offset := 0 }]
  | .param name => some [{ name? := some name, offset := 0 }]
  | .succ level => Level.bumpSummands <$> normalizeSummands? level
  | .max left right => do
      let left ← normalizeSummands? left
      let right ← normalizeSummands? right
      pure (Level.mergeSummands left right)
  | .imax _ _ => none
termination_by level => level

def Level.reduceIMax : Level → Level
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

partial def Level.normalize : Level → Level
  | level =>
      let reduced := reduceIMax level
      match normalizeSummands? reduced with
      | some summands => Level.fromSummands summands
      | none =>
          match reduced with
          | .succ level => .succ (normalize level)
          | .max left right => .max (normalize left) (normalize right)
          | .imax left right => .imax (normalize left) (normalize right)
          | other => other

partial def Level.atMostOne : Level → Bool
  | level =>
      match normalize level with
      | .zero => true
      | .succ .zero => true
      | .max left right => atMostOne left && atMostOne right
      | .imax left right => atMostOne left && atMostOne right
      | _ => false

mutual

partial def Level.defEq (left right : Level) : Bool :=
  let left := normalize left
  let right := normalize right
  match normalizeSummands? left, normalizeSummands? right with
  | some leftN, some rightN =>
      leftN.all (fun leftSummand => rightN.any (Level.summandLe leftSummand)) &&
        rightN.all fun rightSummand => leftN.any fun leftSummand => Level.summandLe rightSummand leftSummand
  | _, _ =>
      match left, right with
      | .zero, .zero => true
      | .param left, .param right => left == right
      | .succ left, .succ right => defEq left right
      | .max leftA leftB, .max rightA rightB =>
          (defEq leftA rightA && defEq leftB rightB) ||
            (defEq leftA rightB && defEq leftB rightA)
      | .imax leftA leftB, .imax rightA rightB =>
          (defEq leftA rightA && defEq leftB rightB) ||
            (((le leftA leftB) || atMostOne leftA) &&
              ((le rightA rightB) || atMostOne rightA) &&
              defEq leftB rightB)
      | .imax left right, other =>
          ((le left right) || atMostOne left) && defEq right other
      | other, .imax left right =>
          ((le left right) || atMostOne left) && defEq other right
      | _, _ => false

partial def Level.le (left right : Level) : Bool :=
  let left := normalize left
  let right := normalize right
  match normalizeSummands? left, normalizeSummands? right with
  | some leftN, some rightN =>
      leftN.all fun leftSummand =>
        rightN.any fun rightSummand => Level.summandLe leftSummand rightSummand
  | _, _ =>
      match left, right with
      | .imax leftA leftB, _ =>
          if (le leftA leftB) || atMostOne leftA then
            le leftB right
          else if le leftA right && le leftB right then
            true
          else
            defEq left right
      | _, .imax rightA rightB =>
          if (le rightA rightB) || atMostOne rightA then
            le left rightB
          else
            defEq left right
      | _, _ => defEq left right

end

end MPC
