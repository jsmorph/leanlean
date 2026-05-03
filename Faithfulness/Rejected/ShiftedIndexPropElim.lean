namespace LeanLeanFaithfulness.Rejected

inductive ShiftedIndexProp : Nat → Prop
| mk (n : Nat) : ShiftedIndexProp (Nat.succ n)

example :
    ShiftedIndexProp.rec (motive := fun _ => Nat) 0 (ShiftedIndexProp.mk 0) = 0 := rfl

end LeanLeanFaithfulness.Rejected
