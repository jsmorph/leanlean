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

inductive InductivePropMode where
  | disabled
  | propOnly
  deriving BEq, Repr, Inhabited

inductive QuotientMode where
  | disabled
  | primitive
  deriving BEq, Repr, Inhabited

inductive EqualityMode where
  | disabled
  | primitive
  deriving BEq, Repr, Inhabited

inductive ProjectionMode where
  | disabled
  | core
  deriving BEq, Repr, Inhabited

inductive PrimitiveReductionMode where
  | disabled
  | nat429
  deriving BEq, Repr, Inhabited

inductive FunctionEtaMode where
  | disabled
  | enabled
  deriving BEq, Repr, Inhabited

structure Manifest where
  declarations : DeclarationMode := .disabled
  prop : PropMode := .disabled
  literals : LiteralMode := .none
  inductives : InductiveMode := .none
  inductiveProp : InductivePropMode := .disabled
  equality : EqualityMode := .disabled
  quotients : QuotientMode := .disabled
  projections : ProjectionMode := .disabled
  primitiveReductions : PrimitiveReductionMode := .disabled
  functionEta : FunctionEtaMode := .disabled
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

def Manifest.supportsPropInductives (manifest : Manifest) : Bool :=
  manifest.inductiveProp == .propOnly

def Manifest.supportsQuotients (manifest : Manifest) : Bool :=
  manifest.quotients == .primitive

def Manifest.supportsEquality (manifest : Manifest) : Bool :=
  manifest.equality == .primitive

def Manifest.supportsProjections (manifest : Manifest) : Bool :=
  manifest.projections == .core

def Manifest.supportsNatPrimitiveReductions (manifest : Manifest) : Bool :=
  manifest.primitiveReductions == .nat429

def Manifest.supportsFunctionEta (manifest : Manifest) : Bool :=
  manifest.functionEta == .enabled

end MPC
