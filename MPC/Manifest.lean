import MPC.Basic

namespace MPC

inductive DeclarationMode where
  | disabled
  | checked
  deriving BEq, Repr, Inhabited

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
  | indexed
  deriving BEq, Repr, Inhabited

structure Manifest where
  declarations : DeclarationMode := .disabled
  prop : PropMode := .disabled
  literals : LiteralMode := .none
  inductives : InductiveMode := .none
  deriving BEq, Repr, Inhabited

def Manifest.validate (manifest : Manifest) : Result Unit := do
  if manifest.declarations == .checked then
    pure ()
  else
    fail "declaration admission is disabled by the manifest"

def Manifest.supportsSimpleInductives (manifest : Manifest) : Bool :=
  manifest.inductives == .simple || manifest.inductives == .indexed

def Manifest.supportsIndexedInductives (manifest : Manifest) : Bool :=
  manifest.inductives == .indexed

end MPC
