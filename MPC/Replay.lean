import MPC.Check

namespace MPC

def addDecl (manifest : Manifest) (env : Env) : Declaration → Result Env
  | .axiom name levelParams type => do
      let _ ← inferSort manifest env levelParams [] type
      Env.add env { name, levelParams, type, kind := .axiom }
  | .definition name levelParams type value => do
      let _ ← inferSort manifest env levelParams [] type
      check manifest env levelParams [] value type
      Env.add env { name, levelParams, type, value? := some value, kind := .definition }
  | .opaque name levelParams type value => do
      let _ ← inferSort manifest env levelParams [] type
      check manifest env levelParams [] value type
      Env.add env { name, levelParams, type, value? := some value, kind := .opaque }
  | .theorem name levelParams type value => do
      isPropExpr manifest env levelParams [] type
      check manifest env levelParams [] value type
      Env.add env { name, levelParams, type, value? := some value, kind := .theorem }

def replay (manifest : Manifest) : Env → List Declaration → Result Env
  | env, [] => pure env
  | env, decl :: rest => do
      let env ← addDecl manifest env decl
      replay manifest env rest

end MPC
