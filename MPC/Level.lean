import MPC.Name

namespace MPC

inductive Level where
  | zero
  | param : Name → Level
  | succ : Level → Level
  | max : Level → Level → Level
  | imax : Level → Level → Level
  deriving BEq, Repr, Inhabited

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
  | .zero => .zero
  | .param name =>
      match LevelContext.lookup? subst name with
      | some value => value
      | none => .param name
  | .succ level => .succ (level.instantiate subst)
  | .max left right => .max (left.instantiate subst) (right.instantiate subst)
  | .imax left right => .imax (left.instantiate subst) (right.instantiate subst)

partial def Level.normalize : Level → Level
  | .succ level => .succ level.normalize
  | .max left right =>
      match left.normalize, right.normalize with
      | .zero, level => level
      | level, .zero => level
      | left, right =>
          if left == right then left else .max left right
  | .imax left right =>
      match left.normalize, right.normalize with
      | _, .zero => .zero
      | .zero, .succ right => .succ right
      | left, right =>
          if left == right then left else .imax left right
  | level => level

def Level.defEq (left right : Level) : Bool :=
  left.normalize == right.normalize

end MPC
