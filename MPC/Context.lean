import MPC.Expr

namespace MPC

structure Binder where
  name : Name
  type : Expr
  deriving BEq, Repr

abbrev Context := List Binder

end MPC
