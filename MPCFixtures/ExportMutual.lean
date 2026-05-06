namespace MPCFixtures.ExportMutual

mutual
inductive MEven : Type
  | zero : MEven
  | succOdd : MOdd → MEven

inductive MOdd : Type
  | succEven : MEven → MOdd
end

def oddOne : MOdd :=
  MOdd.succEven MEven.zero

def evenTwo : MEven :=
  MEven.succOdd oddOne

noncomputable def squashEven (e : MEven) : MEven :=
  MEven.rec
    (motive_1 := fun _ => MEven)
    (motive_2 := fun _ => MEven)
    MEven.zero
    (fun _ ih => ih)
    (fun _ ih => ih)
    e

noncomputable def squashedEvenTwo : MEven :=
  squashEven evenTwo

end MPCFixtures.ExportMutual
