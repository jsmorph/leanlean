import MPC.Env

namespace MPC

inductive Declaration where
  | axiom : Name → LevelContext → Expr → Declaration
  | definition : Name → LevelContext → Expr → Expr → Declaration
  | opaque : Name → LevelContext → Expr → Expr → Declaration
  | theorem : Name → LevelContext → Expr → Expr → Declaration
  deriving BEq, Repr, Inhabited

end MPC
