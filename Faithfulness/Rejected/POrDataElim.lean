namespace LeanLeanFaithfulness.Rejected

inductive POr (a b : Prop) : Prop
| inl : a → POr a b
| inr : b → POr a b

example {a b : Prop} (h : POr a b) : Bool :=
  POr.rec (motive := fun _ => Bool) (fun _ => true) (fun _ => false) h

end LeanLeanFaithfulness.Rejected
