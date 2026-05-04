import MPC.Context
import MPC.Manifest

namespace MPC

inductive ConstantKind where
  | axiom
  | definition
  | opaque
  | theorem
  | constructor : Name → Nat → ConstantKind
  | recursor : Name → ConstantKind
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
