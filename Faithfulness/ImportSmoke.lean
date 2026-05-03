import Faithfulness.Fragments
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
  let localEnv ←
    match LeanLean.Import.replayEnvironmentClosure [] env Fragments.replayRoots with
    | .ok localEnv => pure localEnv
    | .error err => Lean.throwError err
  let boundaryName := LeanLean.Import.translateName `LeanLeanFaithfulness.ModuleA.Boundary
  let importedValue := LeanLean.Import.translateName `LeanLeanFaithfulness.ModuleB.importedValue
  unless localEnv.contains boundaryName && localEnv.contains importedValue do
    Lean.throwError "module-boundary import did not collect imported declarations"
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
