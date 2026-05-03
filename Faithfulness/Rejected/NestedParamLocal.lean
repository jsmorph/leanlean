namespace LeanLeanFaithfulness.Rejected

inductive WrapAt (n : Nat) (α : Type) : Type
| mk : α → WrapAt n α

inductive Dep : Type
| mk : ((n : Nat) → WrapAt n Dep) → Dep

end LeanLeanFaithfulness.Rejected
