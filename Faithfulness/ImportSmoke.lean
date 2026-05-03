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
      `LeanLeanFaithfulness.Accepted.ProofBox,
      `LeanLeanFaithfulness.Accepted.rel,
      `LeanLeanFaithfulness.Accepted.q,
      `LeanLeanFaithfulness.Accepted.SigmaBox,
      `LeanLeanFaithfulness.Accepted.SigmaBox.α,
      `LeanLeanFaithfulness.Accepted.SigmaBox.value,
      `LeanLeanFaithfulness.Accepted.trueTheorem,
      ``Eq,
      ``Quot,
      ``Nat,
      ``Bool,
      ``List,
      `LeanLeanFaithfulness.Accepted.IndexSingleton,
      `LeanLeanFaithfulness.Accepted.Vec1,
      `LeanLeanFaithfulness.Accepted.Pair,
      `LeanLeanFaithfulness.Accepted.Pair.fst,
      `LeanLeanFaithfulness.Accepted.Pair.snd,
      `LeanLeanFaithfulness.Accepted.Parent,
      `LeanLeanFaithfulness.Accepted.Parent.a,
      `LeanLeanFaithfulness.Accepted.Child,
      `LeanLeanFaithfulness.Accepted.Child.toParent,
      `LeanLeanFaithfulness.Accepted.Child.b
    ]
  match LeanLean.Import.replayEnvironmentClosure [] env roots with
  | .ok _ => pure ()
  | .error err => Lean.throwError err

end LeanLeanFaithfulness.ImportSmoke

def main : IO Unit :=
  pure ()
