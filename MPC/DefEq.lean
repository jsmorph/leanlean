import MPC.Normalize

namespace MPC

def defEq (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (_ctx : Context) (left right : Expr) : Result Unit := do
  let left ← normalize manifest env levelParams left
  let right ← normalize manifest env levelParams right
  if left == right then
    pure ()
  else
    fail s!"not definitionally equal: {repr left} and {repr right}"

end MPC
