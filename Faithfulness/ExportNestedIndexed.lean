namespace LeanLeanFaithfulness.ExportNestedIndexed

inductive IVec (α : Type) : Nat → Type
  | nil : IVec α 0
  | cons : (n : Nat) → α → IVec α n → IVec α (Nat.succ n)

inductive PairBox (α β : Type) : Type
  | mk : α → β → PairBox α β

inductive IBox (α β : Type) : Nat → Type
  | mk : β → IBox α β 0

inductive NestedIndexedClosed : Type
  | mk : IVec NestedIndexedClosed 0 → NestedIndexedClosed

inductive NestedIndexedParamClosed (α : Type) : Type
  | mk : IVec (NestedIndexedParamClosed α) 0 → NestedIndexedParamClosed α

inductive NestedIndexedParamLocal (α : Type) : Type
  | mk : ((fuel : Nat) → IVec (NestedIndexedParamLocal α) fuel) →
      NestedIndexedParamLocal α

inductive NestedPairBox (α : Type) : Type
  | mk : PairBox α (NestedPairBox α) → NestedPairBox α

inductive NestedIndexedPairBox (α : Type) : Type
  | mk : IBox α (NestedIndexedPairBox α) 0 → NestedIndexedPairBox α

def closedValue : NestedIndexedClosed :=
  NestedIndexedClosed.mk (IVec.nil (α := NestedIndexedClosed))

def paramValue : NestedIndexedParamClosed Nat :=
  NestedIndexedParamClosed.mk (IVec.nil (α := NestedIndexedParamClosed Nat))

end LeanLeanFaithfulness.ExportNestedIndexed
