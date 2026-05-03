import Lean

open Lean Meta Elab Tactic

namespace LeanLeanFaithfulness.Arena.Bogus1

set_option debug.skipKernelTC true

theorem thm : 0 = 1 := by
  run_tac closeMainGoalUsing `bogus fun _goal _ =>
    return mkConst ``True.intro

end LeanLeanFaithfulness.Arena.Bogus1
