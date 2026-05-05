import MPC.Context
import MPC.Manifest

namespace MPC

structure SimpleConstructorSpec where
  name : Name
  fields : List Binder := []
  deriving BEq, Repr, Inhabited

structure SimpleInductiveSpec where
  name : Name
  levelParams : LevelContext := []
  params : List Binder := []
  resultLevel : Level
  constructors : List SimpleConstructorSpec
  deriving BEq, Repr, Inhabited

structure IndexedConstructorSpec where
  name : Name
  fields : List Binder := []
  targetIndices : List Expr
  deriving BEq, Repr, Inhabited

structure IndexedInductiveSpec where
  name : Name
  levelParams : LevelContext := []
  params : List Binder := []
  indices : List Binder
  resultLevel : Level
  constructors : List IndexedConstructorSpec
  deriving BEq, Repr, Inhabited

structure SimpleRecursiveFieldInfo where
  fieldIndex : Nat
  deriving BEq, Repr, Inhabited

structure SimpleRecursorConstructorInfo where
  name : Name
  fieldCount : Nat
  recursiveFields : List SimpleRecursiveFieldInfo
  deriving BEq, Repr, Inhabited

structure SimpleRecursorInfo where
  inductiveName : Name
  constructors : List SimpleRecursorConstructorInfo
  deriving BEq, Repr, Inhabited

structure IndexedRecursiveFieldInfo where
  fieldIndex : Nat
  binders : List Binder := []
  indices : List Expr
  deriving BEq, Repr, Inhabited

structure IndexedRecursorConstructorInfo where
  name : Name
  fieldCount : Nat
  recursiveFields : List IndexedRecursiveFieldInfo
  deriving BEq, Repr, Inhabited

structure IndexedRecursorInfo where
  inductiveName : Name
  constructors : List IndexedRecursorConstructorInfo
  deriving BEq, Repr, Inhabited

structure NestedRecursiveFieldInfo where
  fieldIndex : Nat
  binders : List Binder := []
  targetIndex : Nat
  deriving BEq, Repr, Inhabited

structure NestedRecursorConstructorInfo where
  name : Name
  fields : List Binder := []
  recursiveFields : List NestedRecursiveFieldInfo := []
  deriving BEq, Repr, Inhabited

structure NestedRecursorTargetInfo where
  recursorName : Name
  locals : List Binder := []
  headName : Name
  levels : List Level
  target : Expr
  paramCount : Nat
  constructors : List NestedRecursorConstructorInfo := []
  deriving BEq, Repr, Inhabited

structure NestedRecursorInfo where
  rootName : Name
  targetIndex : Nat
  targets : List NestedRecursorTargetInfo
  deriving BEq, Repr, Inhabited

inductive ConstantKind where
  | axiom
  | definition
  | opaque
  | theorem
  | inductiveType : SimpleInductiveSpec → ConstantKind
  | indexedInductiveType : IndexedInductiveSpec → ConstantKind
  | constructor : Name → Nat → Nat → ConstantKind
  | recursor : SimpleRecursorInfo → ConstantKind
  | indexedRecursor : IndexedRecursorInfo → ConstantKind
  | nestedRecursor : NestedRecursorInfo → ConstantKind
  | equalityType
  | equalityRefl
  | equalityRec
  | equalityNdRec
  | quotientType
  | quotientMk
  | quotientLift
  | quotientInd
  | quotientSound
  deriving BEq, Repr, Inhabited

structure ConstantInfo where
  name : Name
  levelParams : LevelContext
  type : Expr
  value? : Option Expr := none
  kind : ConstantKind
  deriving BEq, Repr, Inhabited

abbrev Env := List ConstantInfo

def emptyEnv : Env :=
  []

def Env.find? (env : Env) (name : Name) : Option ConstantInfo :=
  List.find? (fun info => info.name == name) env

def Env.contains (env : Env) (name : Name) : Bool :=
  (env.find? name).isSome

def Env.add (env : Env) (info : ConstantInfo) : Result Env :=
  if env.contains info.name then
    fail s!"constant already exists: {info.name}"
  else
    pure (info :: env)

def ConstantInfo.levelSubst? (info : ConstantInfo) (levels : List Level) :
    Option (List (Name × Level)) :=
  if info.levelParams.length == levels.length then
    some (info.levelParams.zip levels)
  else
    none

def ConstantInfo.instantiateType? (info : ConstantInfo) (levels : List Level) :
    Option Expr := do
  let subst ← info.levelSubst? levels
  pure (info.type.instantiateLevels subst)

def ConstantInfo.instantiateValue? (info : ConstantInfo) (levels : List Level) :
    Option Expr := do
  let value ← info.value?
  let subst ← info.levelSubst? levels
  pure (value.instantiateLevels subst)

end MPC
