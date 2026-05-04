import MPC.Basic

namespace MPC

inductive PropMode where
  | disabled
  | enabled
  deriving BEq, Repr, Inhabited

inductive LiteralMode where
  | none
  | nat
  deriving BEq, Repr, Inhabited

inductive InductiveMode where
  | none
  | simple
  deriving BEq, Repr, Inhabited

structure Manifest where
  prop : PropMode := .disabled
  literals : LiteralMode := .none
  inductives : InductiveMode := .none
  deriving BEq, Repr, Inhabited

def Manifest.validate (_manifest : Manifest) : Result Unit :=
  pure ()

end MPC
