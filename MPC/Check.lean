import MPC.Declaration

namespace MPC

def infer (_manifest : Manifest) (_env : Env) (_levelParams : LevelContext)
    (_ctx : Context) (_expr : Expr) : Result Expr :=
  fail "infer is not implemented"

def check (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (ctx : Context) (expr expectedType : Expr) : Result Unit := do
  let inferred ← infer manifest env levelParams ctx expr
  if inferred == expectedType then
    pure ()
  else
    fail s!"type mismatch: inferred {repr inferred}, expected {repr expectedType}"

end MPC
