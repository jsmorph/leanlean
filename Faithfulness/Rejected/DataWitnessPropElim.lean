namespace LeanLeanFaithfulness.Rejected

inductive DataWitnessProp (α : Type) : Prop
| mk : α → DataWitnessProp α

example (p : DataWitnessProp Nat) : Nat :=
  DataWitnessProp.rec (motive := fun _ => Nat) (fun x => x) p

end LeanLeanFaithfulness.Rejected
