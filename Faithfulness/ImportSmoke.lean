import Faithfulness.Accepted
import LeanLean.Import

namespace LeanLeanFaithfulness.ImportSmoke

def expectReplayErrorPrefix
    (env : Lean.Environment)
    (root : Lean.Name)
    (expectedPrefix : String) : Lean.Elab.Command.CommandElabM Unit := do
  match LeanLean.Import.replayEnvironmentClosure [] env [root] with
  | .ok _ => Lean.throwError m!"environment import unexpectedly succeeded: {root}"
  | .error err =>
      unless expectedPrefix.isPrefixOf err do
        Lean.throwError
          m!"environment import for {root} failed with the wrong error\nexpected prefix: {expectedPrefix}\nactual: {err}"

run_cmd
  let env ← Lean.getEnv
  let acceptedRoots :=
    [
      `LeanLeanFaithfulness.Accepted.transparentId,
      `LeanLeanFaithfulness.Accepted.abbrevTrue,
      `LeanLeanFaithfulness.Accepted.opaqueTrue,
      `LeanLeanFaithfulness.Accepted.LocalNat,
      `LeanLeanFaithfulness.Accepted.two,
      `LeanLeanFaithfulness.Accepted.literalNat,
      `LeanLeanFaithfulness.Accepted.PolyBox,
      `LeanLeanFaithfulness.Accepted.PTrue,
      `LeanLeanFaithfulness.Accepted.POr,
      `LeanLeanFaithfulness.Accepted.MutEven,
      `LeanLeanFaithfulness.Accepted.MutNestA,
      `LeanLeanFaithfulness.Accepted.MutNestB,
      `LeanLeanFaithfulness.Accepted.ProofBox,
      `LeanLeanFaithfulness.Accepted.rel,
      `LeanLeanFaithfulness.Accepted.q,
      `LeanLeanFaithfulness.Accepted.liftedBool,
      `LeanLeanFaithfulness.Accepted.liftedTrue,
      `LeanLeanFaithfulness.Accepted.sigmaPair,
      `LeanLeanFaithfulness.Accepted.subtypeTrue,
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
  let broadCoreRoots :=
    [
      ``True,
      ``False,
      ``And,
      ``Or,
      ``Exists,
      ``Subtype,
      ``Sigma,
      ``Prod,
      ``PEmpty,
      ``PUnit,
      ``Unit,
      ``Empty,
      ``Option,
      ``ULift,
      ``PLift,
      ``PSigma,
      ``Decidable
    ]
  let roots := acceptedRoots ++ broadCoreRoots
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
  for recursiveRoot in
      #[
        `LeanLeanFaithfulness.Accepted.natDouble,
        `LeanLeanFaithfulness.Accepted.listLength,
        `LeanLeanFaithfulness.Accepted.evenFlag,
        `LeanLeanFaithfulness.Accepted.oddFlag
      ] do
    expectReplayErrorPrefix
      env
      recursiveRoot
      "recursive definition artifacts are outside the local environment importer:"
  for recursiveCoreRoot in #[``Nat.add, ``List.map] do
    expectReplayErrorPrefix
      env
      recursiveCoreRoot
      "recursive definition artifacts are outside the local environment importer:"

end LeanLeanFaithfulness.ImportSmoke

def main : IO Unit :=
  pure ()
