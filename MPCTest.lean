import MPC

open MPC

def expectOk {α : Type} : Result α → IO α
  | .ok value => pure value
  | .error error => throw <| IO.userError error.message

def expectOkLabel {α : Type} (label : String) : Result α → IO α
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"{label}: {error.message}"

def expectError {α : Type} (label : String) : Result α → IO Unit
  | .ok _ => throw <| IO.userError s!"expected failure: {label}"
  | .error _ => pure ()

def expectExprEq (label : String) (left right : Expr) : IO Unit :=
  if left == right then
    pure ()
  else
    throw <| IO.userError s!"{label}: expected {repr right}, got {repr left}"

def type0 : Expr :=
  .sort (.succ .zero)

def propType : Expr :=
  .sort .zero

def natType : Expr :=
  .const "Nat" []

def pi (name : Name) (domain body : Expr) : Expr :=
  .forallE name domain body

def appN (fn : Expr) (args : List Expr) : Expr :=
  Expr.mkApps fn args

def baseDeclarations : List Declaration :=
  [
    .axiom "Nat" [] type0,
    .axiom "Nat.zero" [] natType,
    .axiom "Nat.succ" [] (pi "n" natType natType),
    .axiom "P" [] propType,
    .axiom "p" [] (.const "P" []),
    .axiom "q" [] (.const "P" [])
  ]

def boolSpec : SimpleInductiveSpec :=
  {
    name := "MPCBool"
    resultLevel := .succ .zero
    constructors :=
      [
        { name := "MPCBool.false" },
        { name := "MPCBool.true" }
      ]
  }

def badRecursiveSpec : SimpleInductiveSpec :=
  {
    name := "Bad"
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "Bad.mk"
          fields :=
            [
              {
                name := "f"
                type := pi "x" (.const "Bad" []) natType
              }
            ]
        }
      ]
  }

def checkBasePackages : IO Unit := do
  let env ← expectOk (replay MPC.Configs.Poc emptyEnv baseDeclarations)
  let literalType ← expectOk (infer MPC.Configs.Poc env [] [] (.lit (.nat 3)))
  expectExprEq "natural literal type" literalType natType
  let _env ← expectOk (addDecl MPC.Configs.Poc env (.theorem "pt" [] (.const "P" []) (.const "p" [])))
  expectError "theorem without Prop"
    (addDecl { MPC.Configs.Poc with prop := .disabled } env
      (.theorem "badTheorem" [] (.const "P" []) (.const "p" [])))

def checkSimpleInductives : IO Unit := do
  let env ← expectOkLabel "bool replay" (replay MPC.Configs.Poc emptyEnv (baseDeclarations ++ [.inductive boolSpec]))
  if !(env.contains "MPCBool.rec") then
    throw <| IO.userError "simple inductive did not generate recursor"
  let motive := .lam "x" (.const "MPCBool" []) (.const "P" [])
  let recursor :=
    appN
      (.const "MPCBool.rec" [.zero])
      [
        motive,
        .const "p" [],
        .const "q" [],
        .const "MPCBool.false" []
      ]
  let reduced ← expectOk (normalize MPC.Configs.Poc env [] recursor)
  expectExprEq "simple recursor iota" reduced (.const "p" [])
  expectError "negative recursive occurrence"
    (replay MPC.Configs.Poc emptyEnv (baseDeclarations ++ [.inductive badRecursiveSpec]))

def main : IO Unit := do
  checkBasePackages
  checkSimpleInductives
