set_option linter.unusedVariables false

namespace LeanLeanFaithfulness.Accepted

universe u

def transparentId {α : Sort u} (x : α) : α := x

example : transparentId true = true := rfl

example : transparentId (α := Type) Bool = Bool := rfl

abbrev abbrevTrue : Bool :=
  true

example : abbrevTrue = true := rfl

opaque opaqueTrue : Bool := true

example : (opaqueTrue : Bool) = opaqueTrue := rfl

inductive LocalNat : Type
| zero : LocalNat
| succ : LocalNat → LocalNat

def two : LocalNat :=
  LocalNat.succ (LocalNat.succ LocalNat.zero)

example :
    LocalNat.rec LocalNat.zero (fun _ ih => LocalNat.succ ih) two = two := rfl

def literalNat : Nat :=
  3

example :
    Nat.rec true (fun _ _ => false) literalNat = false := rfl

theorem natSubClosed :
    Nat.sub 8 3 = 5 := rfl

theorem natSubTruncated :
    Nat.sub 3 8 = 0 := rfl

def literalString : String :=
  "lean"

example :
    literalString = "lean" := rfl

def natDouble : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.succ (Nat.succ (natDouble n))

example :
    natDouble 2 = 4 := rfl

def listLength : List Nat → Nat
  | [] => 0
  | _ :: xs => Nat.succ (listLength xs)

example :
    listLength [0, 1, 2] = 3 := rfl

mutual
  def evenFlag : Nat → Bool
    | 0 => true
    | n + 1 => oddFlag n

  def oddFlag : Nat → Bool
    | 0 => false
    | n + 1 => evenFlag n
end

example :
    evenFlag 2 = true := rfl

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

example :
    PUnit.rec (motive := fun _ => Bool) true PUnit.unit = true := rfl

example (x : PEmpty) : Bool :=
  PEmpty.elim x

def liftedBool : ULift Bool :=
  ⟨true⟩

example :
    liftedBool.down = true := rfl

def liftedTrue : PLift True :=
  ⟨True.intro⟩

example :
    liftedTrue.down = True.intro := rfl

def sigmaPair : Sigma (fun _ : Bool => Nat) :=
  ⟨true, 1⟩

example :
    sigmaPair.1 = true := rfl

example :
    sigmaPair.2 = 1 := rfl

def subtypeTrue : { b : Bool // b = true } :=
  ⟨true, rfl⟩

example :
    subtypeTrue.val = true := rfl

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

structure Parent where
  a : Nat

structure Child extends Parent where
  b : Bool

example (x : Child) :
    Child.mk x.toParent x.b = x := rfl

example (x : Child) :
    Parent.mk x.toParent.a = x.toParent := rfl

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

theorem trueTheorem : True :=
  True.intro

example :
    trueTheorem = True.intro := rfl

inductive RecStruct : Type
| mk : RecStruct → RecStruct

example (x : RecStruct) :
    x.1 = x.1 := rfl

inductive Vec1 (α : Type) : Nat → Type
| mk (n : Nat) : α → Vec1 α n

example :
    (Vec1.mk 0 true).1 = true := rfl

example (x : Vec1 Bool 0) :
    Vec1.mk 0 x.1 = x := rfl

inductive ShiftedStruct (α : Type) : Nat → Type
| mk (n : Nat) : α → ShiftedStruct α (Nat.succ n)

example :
    (ShiftedStruct.mk 0 true).1 = 0 := rfl

example :
    (ShiftedStruct.mk 0 true).2 = true := rfl

end LeanLeanFaithfulness.Accepted
