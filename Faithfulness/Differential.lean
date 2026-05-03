import Faithfulness.Accepted
import LeanLean.Import

open Lean Elab Command Term Meta

namespace LeanLeanFaithfulness.Differential

def liftResult (label : String) : LeanLean.Result α → CommandElabM α
  | .ok value => pure value
  | .error err => Lean.throwError m!"{label}: {err}"

def elabClosedTerm (stx : Syntax) : CommandElabM Expr :=
  liftTermElabM do
    let term ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars term

def reduceClosedTerm (term : Expr) : CommandElabM (Expr × Expr) :=
  liftTermElabM do
    let type ← instantiateMVars (← inferType term)
    let value ← instantiateMVars (← reduce term)
    pure (type, value)

def termRoots (term type value : Expr) : List Name :=
  LeanLean.Import.appendLeanNames
    (LeanLean.Import.appendLeanNames
      (LeanLean.Import.leanExprConstants term)
      (LeanLean.Import.leanExprConstants type))
    (LeanLean.Import.leanExprConstants value)

def compareTerm (label : String) (stx : Syntax) : CommandElabM Unit := do
  let term ← elabClosedTerm stx
  let (type, value) ← reduceClosedTerm term
  let leanEnv ← Lean.getEnv
  let localEnv ←
    liftResult label <| LeanLean.Import.replayEnvironmentClosure [] leanEnv (termRoots term type value)
  let localTerm ← liftResult label <| LeanLean.Import.translateExpr term
  let localType ← liftResult label <| LeanLean.Import.translateExpr type
  let localValue ← liftResult label <| LeanLean.Import.translateExpr value
  let inferred ← liftResult label <| LeanLean.infer localEnv [] localTerm
  liftResult label <| LeanLean.checkDefEq localEnv inferred localType
  let normalized ← liftResult label <| LeanLean.normalize localEnv localTerm
  liftResult label <| LeanLean.checkDefEq localEnv normalized localValue

run_cmd
  compareTerm
    "transparent definition type and value"
    (← `(LeanLeanFaithfulness.Accepted.transparentId true))
  compareTerm
    "abbreviation value"
    (← `(LeanLeanFaithfulness.Accepted.abbrevTrue))
  compareTerm
    "primitive Nat recursor value"
    (← `(
      LeanLeanFaithfulness.Accepted.LocalNat.rec
        (motive := fun _ => LeanLeanFaithfulness.Accepted.LocalNat)
        LeanLeanFaithfulness.Accepted.LocalNat.zero
        (fun _ ih => LeanLeanFaithfulness.Accepted.LocalNat.succ ih)
        LeanLeanFaithfulness.Accepted.two))
  compareTerm
    "large Prop recursor value"
    (← `(
      LeanLeanFaithfulness.Accepted.PTrue.rec
        (motive := fun _ => Bool)
        true
        LeanLeanFaithfulness.Accepted.PTrue.intro))
  compareTerm
    "equality recursor value"
    (← `(
      @Eq.rec Bool true (fun _ _ => Bool) false true rfl))
  compareTerm
    "sort-polymorphic unit recursor value"
    (← `(
      @PUnit.rec.{1, 0} (fun _ => Bool) true PUnit.unit))
  compareTerm
    "dependent projection value"
    (← `(
      LeanLeanFaithfulness.Accepted.SigmaBox.value
        { α := Bool, value := true }))
  compareTerm
    "core Decidable recursor value"
    (← `(
      @Decidable.rec True
        (fun _ => Bool)
        (fun _ => false)
        (fun _ => true)
        (Decidable.isTrue True.intro)))

end LeanLeanFaithfulness.Differential

def main : IO Unit :=
  pure ()
