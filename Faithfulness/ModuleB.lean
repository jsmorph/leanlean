import Faithfulness.ModuleA

namespace LeanLeanFaithfulness.ModuleB

def importedValue : ModuleA.Boundary :=
  ModuleA.value

example :
    ModuleA.Boundary.rec (motive := fun _ => Nat) (fun n => n) importedValue = 2 := rfl

end LeanLeanFaithfulness.ModuleB
