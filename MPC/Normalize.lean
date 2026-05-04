import MPC.Check

namespace MPC

def whnf (_manifest : Manifest) (_env : Env) (_levelParams : LevelContext)
    (expr : Expr) : Result Expr :=
  pure expr

def normalize (_manifest : Manifest) (_env : Env) (_levelParams : LevelContext)
    (expr : Expr) : Result Expr :=
  pure expr

end MPC
