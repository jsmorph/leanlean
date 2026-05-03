set_option linter.unusedVariables false

namespace LeanLeanFaithfulness.Rejected

def relEq (a b : Bool) : Prop :=
  a = b

def relTrue (a b : Bool) : Prop :=
  True

def q : Quot relTrue :=
  Quot.mk relTrue true

example :
    Quot.lift (r := relEq) (fun x => x) (by intro a b h; exact h) q = true := rfl

end LeanLeanFaithfulness.Rejected
