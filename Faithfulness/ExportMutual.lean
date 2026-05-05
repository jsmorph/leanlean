namespace LeanLeanFaithfulness.ExportMutual

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

end LeanLeanFaithfulness.ExportMutual
