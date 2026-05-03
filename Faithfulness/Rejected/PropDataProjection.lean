namespace LeanLeanFaithfulness.Rejected

inductive ExistsNat : Prop
| mk : Nat → ExistsNat

example (x : ExistsNat) :
    x.1 = x.1 := rfl

end LeanLeanFaithfulness.Rejected
