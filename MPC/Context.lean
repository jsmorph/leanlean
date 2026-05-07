import MPC.Expr

namespace MPC

structure Binder where
  name : Name
  type : Expr
  deriving BEq, Repr, Hashable

abbrev Context := List Binder

def Context.get? : Context → Nat → Option Binder
  | [], _ => none
  | binder :: _, 0 => some binder
  | _ :: rest, index + 1 => get? rest index

def Context.lookup? (ctx : Context) (index : Nat) : Option Binder :=
  match Context.get? ctx index with
  | some binder => some { binder with type := binder.type.lift (index + 1) }
  | none => none

def Context.extend (ctx : Context) (name : Name) (type : Expr) : Context :=
  { name, type } :: ctx

def bindForall (binders : List Binder) (body : Expr) : Expr :=
  binders.foldr (fun binder body => .forallE binder.name binder.type body) body

end MPC
