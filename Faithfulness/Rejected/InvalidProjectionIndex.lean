namespace LeanLeanFaithfulness.Rejected

structure Pair where
  fst : Nat
  snd : Bool

example (x : Pair) :
    x.3 = x.3 := rfl

end LeanLeanFaithfulness.Rejected
