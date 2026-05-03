namespace LeanLeanFaithfulness.Rejected

inductive ShiftedStruct (α : Type) : Nat → Type
| mk (n : Nat) : α → ShiftedStruct α (Nat.succ n)

example (x : ShiftedStruct Bool 1) :
    ShiftedStruct.mk x.1 x.2 = x := rfl

end LeanLeanFaithfulness.Rejected
