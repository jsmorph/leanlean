import Faithfulness.Accepted
import LeanLean.Import

namespace LeanLeanFaithfulness.ImportSmoke

run_cmd
  let env ← Lean.getEnv
  let roots :=
    [
      `LeanLeanFaithfulness.Accepted.transparentId,
      `LeanLeanFaithfulness.Accepted.abbrevTrue,
      `LeanLeanFaithfulness.Accepted.opaqueTrue,
      `LeanLeanFaithfulness.Accepted.LocalNat,
      `LeanLeanFaithfulness.Accepted.two,
      `LeanLeanFaithfulness.Accepted.PolyBox,
      `LeanLeanFaithfulness.Accepted.PTrue,
      `LeanLeanFaithfulness.Accepted.POr,
      `LeanLeanFaithfulness.Accepted.MutEven,
      `LeanLeanFaithfulness.Accepted.MutNestA,
      `LeanLeanFaithfulness.Accepted.MutNestB,
      `LeanLeanFaithfulness.Accepted.ProofBox,
      `LeanLeanFaithfulness.Accepted.rel,
      `LeanLeanFaithfulness.Accepted.q,
      `LeanLeanFaithfulness.Accepted.SigmaBox,
      `LeanLeanFaithfulness.Accepted.trueTheorem,
      ``Eq,
      ``Quot,
      ``Nat,
      ``Bool,
      ``List,
      `LeanLeanFaithfulness.Accepted.IndexSingleton,
      `LeanLeanFaithfulness.Accepted.Vec1,
      `LeanLeanFaithfulness.Accepted.Pair,
      `LeanLeanFaithfulness.Accepted.Parent,
      `LeanLeanFaithfulness.Accepted.Child
    ]
  let localEnv ←
    match LeanLean.Import.replayEnvironmentClosure [] env roots with
    | .ok localEnv => pure localEnv
    | .error err => Lean.throwError err
  let childName := LeanLean.Import.translateName `LeanLeanFaithfulness.Accepted.Child
  let childB := LeanLean.Import.translateName `LeanLeanFaithfulness.Accepted.Child.b
  let childParent := LeanLean.Import.translateName `LeanLeanFaithfulness.Accepted.Child.toParent
  unless localEnv.contains childB && localEnv.contains childParent do
    Lean.throwError "structure metadata import did not collect child projection declarations"
  match localEnv.findStructure? childName with
  | some _ => pure ()
  | none => Lean.throwError "structure metadata import did not register Child"
  let childFields ←
    match localEnv.structureFieldsFlattened childName false with
    | .ok fields => pure fields
    | .error err => Lean.throwError err
  unless childFields = ["a", "b"] do
    Lean.throwError "structure metadata import produced wrong inherited fields for Child"
  let pairFst := LeanLean.Import.translateName `LeanLeanFaithfulness.Accepted.Pair.fst
  let pairSnd := LeanLean.Import.translateName `LeanLeanFaithfulness.Accepted.Pair.snd
  unless localEnv.contains pairFst && localEnv.contains pairSnd do
    Lean.throwError "structure metadata import did not collect Pair projection declarations"
  let sigmaType := LeanLean.Import.translateName `LeanLeanFaithfulness.Accepted.SigmaBox.α
  let sigmaValue := LeanLean.Import.translateName `LeanLeanFaithfulness.Accepted.SigmaBox.value
  unless localEnv.contains sigmaType && localEnv.contains sigmaValue do
    Lean.throwError "structure metadata import did not collect SigmaBox projection declarations"

end LeanLeanFaithfulness.ImportSmoke

def main : IO Unit :=
  pure ()
