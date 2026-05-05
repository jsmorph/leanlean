import MPC.Env

namespace MPC

inductive Declaration where
  | axiom : Name → LevelContext → Expr → Declaration
  | definition : Name → LevelContext → Expr → Expr → Declaration
  | opaque : Name → LevelContext → Expr → Expr → Declaration
  | theorem : Name → LevelContext → Expr → Expr → Declaration
  | inductive : SimpleInductiveSpec → Declaration
  | inductiveBlock : InductiveBlockSpec → Declaration
  | indexedInductive : IndexedInductiveSpec → Declaration
  | equalityPrimitives
  | quotientPrimitives
  deriving BEq, Repr, Inhabited

end MPC
