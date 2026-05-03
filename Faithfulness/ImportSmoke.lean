import Faithfulness.Accepted
import LeanLean.Import

namespace LeanLeanFaithfulness.ImportSmoke

run_cmd
  let env ← Lean.getEnv
  let roots :=
    [
      `LeanLeanFaithfulness.Accepted.transparentId,
      `LeanLeanFaithfulness.Accepted.LocalNat,
      `LeanLeanFaithfulness.Accepted.PolyBox,
      `LeanLeanFaithfulness.Accepted.PTrue,
      `LeanLeanFaithfulness.Accepted.MutEven,
      `LeanLeanFaithfulness.Accepted.ProofBox
    ]
  match LeanLean.Import.replayEnvironmentClosure [] env roots with
  | .ok _ => pure ()
  | .error err => Lean.throwError err

end LeanLeanFaithfulness.ImportSmoke

def main : IO Unit :=
  pure ()
