import MPC.Context
import MPC.Manifest
import Std.Data.HashMap

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

structure InductiveBlockSpec where
  levelParams : LevelContext := []
  specs : List SimpleInductiveSpec
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

structure MutualRecursiveFieldInfo where
  fieldIndex : Nat
  targetIndex : Nat
  deriving BEq, Repr, Inhabited

structure MutualRecursorConstructorInfo where
  inductiveIndex : Nat
  name : Name
  fieldCount : Nat
  recursiveFields : List MutualRecursiveFieldInfo
  deriving BEq, Repr, Inhabited

structure MutualRecursorInfo where
  targetIndex : Nat
  inductiveNames : List Name
  constructors : List MutualRecursorConstructorInfo
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
  targetArgs : List Expr := []
  deriving BEq, Repr, Inhabited

structure NestedRecursorConstructorInfo where
  name : Name
  fields : List Binder := []
  targetArgs : List Expr := []
  recursiveFields : List NestedRecursiveFieldInfo := []
  deriving BEq, Repr, Inhabited

structure NestedRecursorTargetInfo where
  recursorName : Name
  locals : List Binder := []
  headName : Name
  levels : List Level
  target : Expr
  paramCount : Nat
  params : List Expr := []
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
  | mutualRecursor : MutualRecursorInfo → ConstantKind
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

structure ConstructorFieldInfo where
  paramCount : Nat
  proofFields : List Bool := []
  deriving BEq, Repr, Inhabited

structure Env where
  entries : List ConstantInfo := []
  index : Std.HashMap Name ConstantInfo := {}
  constructorFieldInfo : Std.HashMap Name ConstructorFieldInfo := {}

def emptyEnv : Env :=
  {}

def listGet? : List α → Nat → Option α
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: rest, index + 1 => listGet? rest index

def Env.find? (env : Env) (name : Name) : Option ConstantInfo :=
  env.index.get? name

def Env.findConstructorFieldInfo? (env : Env) (name : Name) :
    Option ConstructorFieldInfo :=
  env.constructorFieldInfo.get? name

def Env.contains (env : Env) (name : Name) : Bool :=
  env.index.contains name

def Env.length (env : Env) : Nat :=
  env.entries.length

partial def typeResultSortWithArity? : Expr → Option (Nat × Level)
  | .forallE _ _ body => do
      let (arity, level) ← typeResultSortWithArity? body
      pure (arity + 1, level)
  | .sort level => some (0, level)
  | _ => none

partial def forallResult : Expr → Expr
  | .forallE _ _ body => forallResult body
  | expr => expr

def ConstantInfo.propResultArity? (info : ConstantInfo) : Option Nat := do
  let (arity, level) ← typeResultSortWithArity? info.type
  if level.defEqZero then
    some arity
  else
    none

def Env.knownPropType (env : Env) (type : Expr) : Bool :=
  let result := forallResult type
  let (head, args) := result.getAppFnArgs
  match head with
  | .const name _ =>
      match env.find? name with
      | some info =>
          match info.propResultArity? with
          | some arity => args.length == arity
          | none => false
      | none => false
  | _ => false

def Env.constructorFieldInfoFromFields? (env : Env) (paramCount : Nat)
    (fields : List Binder) : Option ConstructorFieldInfo :=
  let proofFields := fields.map fun field => env.knownPropType field.type
  if proofFields.any (fun flag => flag) then
    some { paramCount, proofFields }
  else
    none

def Env.constructorFieldInfoFor? (env : Env) (info : ConstantInfo) :
    Option ConstructorFieldInfo :=
  match info.kind with
  | .constructor inductiveName ctorIndex _ =>
      match env.find? inductiveName with
      | some { kind := .inductiveType spec, .. } =>
          match listGet? spec.constructors ctorIndex with
          | some ctor => env.constructorFieldInfoFromFields? spec.params.length ctor.fields
          | none => none
      | some { kind := .indexedInductiveType spec, .. } =>
          match listGet? spec.constructors ctorIndex with
          | some ctor => env.constructorFieldInfoFromFields? spec.params.length ctor.fields
          | none => none
      | _ => none
  | _ => none

def Env.add (env : Env) (info : ConstantInfo) : Result Env :=
  if env.contains info.name then
    fail s!"constant already exists: {info.name}"
  else
    let constructorFieldInfo :=
      match env.constructorFieldInfoFor? info with
      | some fieldInfo => env.constructorFieldInfo.insert info.name fieldInfo
      | none => env.constructorFieldInfo
    pure
      {
        entries := info :: env.entries
        index := env.index.insert info.name info
        constructorFieldInfo
      }

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
