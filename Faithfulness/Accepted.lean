set_option linter.unusedVariables false

namespace LeanLeanFaithfulness.Accepted

universe u

def transparentId {α : Sort u} (x : α) : α := x

example : transparentId true = true := rfl

example : transparentId (α := Type) Bool = Bool := rfl

opaque opaqueTrue : Bool := true

example : (opaqueTrue : Bool) = opaqueTrue := rfl

inductive LocalNat : Type
| zero : LocalNat
| succ : LocalNat → LocalNat

def two : LocalNat :=
  LocalNat.succ (LocalNat.succ LocalNat.zero)

example :
    LocalNat.rec LocalNat.zero (fun _ ih => LocalNat.succ ih) two = two := rfl

inductive PolyBox (α : Sort u) : Type u
| mk : α → PolyBox α

example :
    PolyBox.rec (motive := fun _ => Bool) (fun b => b) (PolyBox.mk true) = true := rfl

example :
    PolyBox.rec (motive := fun _ => Type) (fun α => α) (PolyBox.mk Bool) = Bool := rfl

inductive PTrue : Prop
| intro : PTrue

example :
    PTrue.rec (motive := fun _ => Bool) true PTrue.intro = true := rfl

inductive POr (a b : Prop) : Prop
| inl : a → POr a b
| inr : b → POr a b

example {a b : Prop} (h : POr a b) : POr a b :=
  POr.rec (motive := fun _ => POr a b) (fun ha => POr.inl ha) (fun hb => POr.inr hb) h

inductive IndexSingleton : Nat → Prop
| mk (n : Nat) : IndexSingleton n

example :
    IndexSingleton.rec (motive := fun _ => Nat) 0 (IndexSingleton.mk 0) = 0 := rfl

example :
    (@Eq.rec Bool true (fun _ _ => Bool) false true rfl) = false := rfl

def rel (a b : Bool) : Prop :=
  a = b

def q : Quot rel :=
  Quot.mk rel true

example :
    Quot.lift (fun x => x) (by intro a b h; exact h) q = true := rfl

mutual
  inductive MutEven : Type
  | zero : MutEven
  | succOdd : MutOdd → MutEven

  inductive MutOdd : Type
  | succEven : MutEven → MutOdd
end

example : MutEven :=
  MutEven.succOdd (MutOdd.succEven MutEven.zero)

mutual
  inductive MutNestA : Type
  | mk : List MutNestB → MutNestA

  inductive MutNestB : Type
  | mk : MutNestA → MutNestB
end

example : MutNestA :=
  MutNestA.mk [MutNestB.mk (MutNestA.mk [])]

structure Pair where
  fst : Nat
  snd : Bool

example :
    Pair.fst { fst := 0, snd := true } = 0 := rfl

example (x : Pair) :
    Pair.mk x.fst x.snd = x := rfl

structure SigmaBox where
  α : Type
  value : α

example :
    SigmaBox.α { α := Bool, value := true } = Bool := rfl

example :
    SigmaBox.value { α := Bool, value := true } = true := rfl

example (x : SigmaBox) :
    SigmaBox.mk x.α x.value = x := rfl

inductive ProofBox (p : Prop) : Prop
| mk : p → ProofBox p

example {p : Prop} (h : p) :
    (ProofBox.mk h).1 = h := rfl

inductive RecStruct : Type
| mk : RecStruct → RecStruct

example (x : RecStruct) :
    x.1 = x.1 := rfl

end LeanLeanFaithfulness.Accepted
