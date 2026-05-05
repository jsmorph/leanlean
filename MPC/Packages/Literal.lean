import MPC.Env

namespace MPC.Packages.Literal

open MPC

def requireNatSupport (env : Env) : Result Unit := do
  if env.contains "Nat" && env.contains "Nat.zero" && env.contains "Nat.succ" then
    pure ()
  else
    fail "natural literals require Nat, Nat.zero, and Nat.succ in the environment"

def requireStringSupport (env : Env) : Result Unit := do
  if env.contains "String" then
    pure ()
  else
    fail "string literals require String in the environment"

def natConstructorSpine (env : Env) : Nat → Result Expr
  | 0 => do
      requireNatSupport env
      pure (.const "Nat.zero" [])
  | n + 1 => do
      requireNatSupport env
      pure (.app (.const "Nat.succ" []) (← natConstructorSpine env n))

end MPC.Packages.Literal
