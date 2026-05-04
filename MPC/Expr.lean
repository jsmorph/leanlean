import MPC.Level

namespace MPC

inductive Literal where
  | nat : Nat → Literal
  | str : String → Literal
  deriving BEq, Repr

inductive Expr where
  | bvar : Nat → Expr
  | sort : Level → Expr
  | const : Name → List Level → Expr
  | lit : Literal → Expr
  | app : Expr → Expr → Expr
  | lam : Name → Expr → Expr → Expr
  | forallE : Name → Expr → Expr → Expr
  | letE : Name → Expr → Expr → Expr → Expr
  deriving BEq, Repr

def Expr.mkApps (fn : Expr) : List Expr → Expr
  | [] => fn
  | arg :: args => Expr.mkApps (.app fn arg) args

end MPC
