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

def expectEnvContains (label : String) (env : Env) (name : Name) : IO Unit :=
  if env.contains name then
    pure ()
  else
    throw <| IO.userError s!"{label}: missing {name}"

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

def propInductiveSpec : SimpleInductiveSpec :=
  {
    name := "PropOnly"
    resultLevel := .zero
    constructors :=
      [
        { name := "PropOnly.intro" }
      ]
  }

def boxSpec : SimpleInductiveSpec :=
  {
    name := "Box"
    resultLevel := .succ .zero
    params :=
      [
        { name := "A", type := type0 }
      ]
    constructors :=
      [
        {
          name := "Box.mk"
          fields :=
            [
              { name := "value", type := .bvar 0 }
            ]
        }
      ]
  }

def checkBasePackages : IO Unit := do
  expectOkLabel "manifest validation" (Manifest.validate MPC.Configs.Poc)
  let env ← expectOk (replay MPC.Configs.Poc emptyEnv baseDeclarations)
  let literalType ← expectOk (infer MPC.Configs.Poc env [] [] (.lit (.nat 3)))
  expectExprEq "natural literal type" literalType natType
  let twoCtor := .app (.const "Nat.succ" []) (.app (.const "Nat.succ" []) (.const "Nat.zero" []))
  expectOkLabel "natural literal constructor equality"
    (defEq MPC.Configs.Poc env [] [] (.lit (.nat 2)) twoCtor)
  let _env ← expectOk (addDecl MPC.Configs.Poc env (.theorem "pt" [] (.const "P" []) (.const "p" [])))
  expectError "theorem without Prop"
    (addDecl { MPC.Configs.Poc with prop := .disabled } env
      (.theorem "badTheorem" [] (.const "P" []) (.const "p" [])))
  expectError "declaration admission disabled"
    (addDecl { MPC.Configs.Poc with declarations := .disabled } env
      (.axiom "NoDecls" [] type0))
  let malformedNatEnv ← expectOk (replay MPC.Configs.Poc emptyEnv [.axiom "Nat" [] type0])
  expectError "malformed natural literal environment"
    (infer MPC.Configs.Poc malformedNatEnv [] [] (.lit (.nat 0)))

def checkSimpleInductives : IO Unit := do
  let env ← expectOkLabel "bool replay" (replay MPC.Configs.Poc emptyEnv (baseDeclarations ++ [.inductive boolSpec]))
  expectEnvContains "simple inductive" env "MPCBool.rec"
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
  expectError "proposition-valued simple inductive"
    (replay MPC.Configs.Poc emptyEnv (baseDeclarations ++ [.inductive propInductiveSpec]))
  let boxEnv ← expectOkLabel "box replay" (replay MPC.Configs.Poc emptyEnv (baseDeclarations ++ [.inductive boxSpec]))
  expectEnvContains "parameterized simple inductive" boxEnv "Box.rec"
  let boxMotive :=
    .lam "x" (.app (.const "Box" []) natType) (.const "P" [])
  let boxMinor := .lam "value" natType (.const "p" [])
  let boxTarget := appN (.const "Box.mk" []) [natType, .const "Nat.zero" []]
  let boxRecursor :=
    appN
      (.const "Box.rec" [.zero])
      [
        natType,
        boxMotive,
        boxMinor,
        boxTarget
      ]
  let boxReduced ← expectOk (normalize MPC.Configs.Poc boxEnv [] boxRecursor)
  expectExprEq "parameterized simple recursor iota" boxReduced (.const "p" [])

def scriptInput : String :=
  "axiom Nat Type0\n" ++
  "axiom Nat.zero Nat\n" ++
  "axiom Nat.succ forall:n:Nat:Nat\n" ++
  "axiom P Prop\n" ++
  "axiom p P\n" ++
  "def three Nat nat:3\n" ++
  "theorem pt P p\n" ++
  "inductive-bool SB SB.false SB.true\n"

def ndjsonInput : String :=
  "{\"decl\":\"axiom\",\"name\":\"Nat\",\"type\":{\"sort\":1}}\n" ++
  "{\"decl\":\"axiom\",\"name\":\"Nat.zero\",\"type\":{\"const\":\"Nat\"}}\n" ++
  "{\"decl\":\"axiom\",\"name\":\"Nat.succ\",\"type\":{\"forall\":{\"name\":\"n\",\"domain\":{\"const\":\"Nat\"},\"body\":{\"const\":\"Nat\"}}}}\n" ++
  "{\"decl\":\"axiom\",\"name\":\"P\",\"type\":{\"sort\":0}}\n" ++
  "{\"decl\":\"axiom\",\"name\":\"p\",\"type\":{\"const\":\"P\"}}\n" ++
  "{\"decl\":\"axiom\",\"name\":\"q\",\"type\":{\"const\":\"P\"}}\n" ++
  "{\"decl\":\"def\",\"name\":\"three\",\"type\":{\"const\":\"Nat\"},\"value\":{\"nat\":3}}\n" ++
  "{\"decl\":\"inductive\",\"name\":\"JBool\",\"level\":1,\"constructors\":[{\"name\":\"JBool.false\"},{\"name\":\"JBool.true\"}]}\n" ++
  "{\"generated\":\"constructor\",\"name\":\"JBool.false\"}\n" ++
  "{\"generated\":\"constructor\",\"name\":\"JBool.true\"}\n" ++
  "{\"generated\":\"recursor\",\"name\":\"JBool.rec\"}\n"

def badNdjsonAuditInput : String :=
  "{\"decl\":\"axiom\",\"name\":\"Nat\",\"type\":{\"sort\":1}}\n" ++
  "{\"generated\":\"recursor\",\"name\":\"Missing.rec\"}\n"

def checkAdapters : IO Unit := do
  let scriptEnv ← expectOkLabel "script adapter"
    (MPC.Adapters.Script.checkString MPC.Configs.Poc scriptInput)
  expectEnvContains "script adapter" scriptEnv "three"
  expectEnvContains "script adapter" scriptEnv "pt"
  expectEnvContains "script adapter" scriptEnv "SB.rec"
  let jsonEnv ← expectOkLabel "NDJSON adapter"
    (MPC.Adapters.NDJSON.checkString MPC.Configs.Poc ndjsonInput)
  expectEnvContains "NDJSON adapter" jsonEnv "three"
  expectEnvContains "NDJSON adapter" jsonEnv "JBool.false"
  expectEnvContains "NDJSON adapter" jsonEnv "JBool.true"
  expectEnvContains "NDJSON adapter" jsonEnv "JBool.rec"
  expectError "malformed script"
    (MPC.Adapters.Script.checkString MPC.Configs.Poc "axiom Nat\n")
  expectError "NDJSON missing generated declaration"
    (MPC.Adapters.NDJSON.checkString MPC.Configs.Poc badNdjsonAuditInput)

def main : IO Unit := do
  checkBasePackages
  checkSimpleInductives
  checkAdapters
