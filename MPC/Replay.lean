import MPC.Packages.Inductive.Admission
import MPC.Packages.Equality
import MPC.Packages.Quotient

namespace MPC

structure DeclarationOps (m : Type → Type) where
  validate : m Unit
  inferSort : Env → LevelContext → Context → Expr → m Level
  check : Env → LevelContext → Context → Expr → Expr → m Unit
  isPropExpr : Env → LevelContext → Context → Expr → m Unit
  addConstant : Env → ConstantInfo → m Env
  addGenerated : Env → Declaration → m Env

def addDeclWith [Monad m] (ops : DeclarationOps m) (env : Env) : Declaration → m Env
  | declaration => do
      ops.validate
      match declaration with
      | .axiom name levelParams type => do
          let _ ← ops.inferSort env levelParams [] type
          ops.addConstant env { name, levelParams, type, kind := .axiom }
      | .definition name levelParams type value => do
          let _ ← ops.inferSort env levelParams [] type
          ops.check env levelParams [] value type
          ops.addConstant env { name, levelParams, type, value? := some value, kind := .definition }
      | .opaque name levelParams type value => do
          let _ ← ops.inferSort env levelParams [] type
          ops.check env levelParams [] value type
          ops.addConstant env { name, levelParams, type, value? := some value, kind := .opaque }
      | .theorem name levelParams type value => do
          ops.isPropExpr env levelParams [] type
          ops.check env levelParams [] value type
          ops.addConstant env { name, levelParams, type, value? := some value, kind := .theorem }
      | declaration =>
          ops.addGenerated env declaration

def addGeneratedDecl (manifest : Manifest) (env : Env) : Declaration → Result Env
  | .inductive spec =>
      addSimpleInductive manifest env spec
  | .inductiveBlock block =>
      addInductiveBlock manifest env block
  | .indexedInductive spec =>
      addIndexedInductive manifest env spec
  | .equalityPrimitives =>
      MPC.Packages.Equality.addEqualityPrimitives manifest env
  | .quotientPrimitives =>
      MPC.Packages.Quotient.addQuotientPrimitives manifest env
  | _ =>
      fail "declaration is not handled by generated declaration admission"

def declarationOps (manifest : Manifest) : DeclarationOps Result where
  validate := Manifest.validate manifest
  inferSort := fun env levelParams ctx expr =>
    inferSort manifest env levelParams ctx expr
  check := fun env levelParams ctx expr expectedType =>
    check manifest env levelParams ctx expr expectedType
  isPropExpr := fun env levelParams ctx expr =>
    isPropExpr manifest env levelParams ctx expr
  addConstant := Env.add
  addGenerated := addGeneratedDecl manifest

def addDecl (manifest : Manifest) (env : Env) (declaration : Declaration) : Result Env :=
  addDeclWith (declarationOps manifest) env declaration

def replay (manifest : Manifest) : Env → List Declaration → Result Env
  | env, [] => pure env
  | env, decl :: rest => do
      let env ← addDecl manifest env decl
      replay manifest env rest

end MPC
