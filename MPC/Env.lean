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
  deriving BEq, Repr

structure ConstantInfo where
  name : Name
  levelParams : LevelContext
  type : Expr
  value? : Option Expr := none
  kind : ConstantKind
  deriving BEq, Repr

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

end MPC
