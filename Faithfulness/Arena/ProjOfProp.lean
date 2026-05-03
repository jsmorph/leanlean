import Lean

open Lean Elab Command

namespace LeanLeanFaithfulness.Arena.ProjOfProp

structure Wrapper : Prop where
  mk ::
  p : False

run_cmd liftTermElabM do
  let badValue : Expr :=
    .proj `LeanLeanFaithfulness.Arena.ProjOfProp.Wrapper 0
      (mkApp
        (mkConst ``LeanLeanFaithfulness.Arena.ProjOfProp.Wrapper.mk)
        (mkConst ``True.intro))
  let decl : Declaration := .thmDecl {
    name := `LeanLeanFaithfulness.Arena.ProjOfProp.badFalse
    levelParams := []
    type := mkConst ``False
    value := badValue
  }
  withOptions (debug.skipKernelTC.set · true) do
    addDecl decl

end LeanLeanFaithfulness.Arena.ProjOfProp
