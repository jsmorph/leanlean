namespace LeanLeanFaithfulness.ModuleA

inductive Boundary : Type
| mk : Nat → Boundary

def value : Boundary :=
  Boundary.mk 2

end LeanLeanFaithfulness.ModuleA
