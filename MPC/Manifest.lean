import MPC.Basic

namespace MPC

inductive PropMode where
  | disabled
  | enabled
  deriving BEq, Repr

inductive LiteralMode where
  | none
  | nat
  deriving BEq, Repr

inductive InductiveMode where
  | none
  | simple
  deriving BEq, Repr

structure Manifest where
  prop : PropMode := .disabled
  literals : LiteralMode := .none
  inductives : InductiveMode := .none
  deriving BEq, Repr

def Manifest.validate (_manifest : Manifest) : Result Unit :=
  pure ()

end MPC
