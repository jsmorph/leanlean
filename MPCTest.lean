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

def natZero : Expr :=
  .const "Nat.zero" []

def natSucc (value : Expr) : Expr :=
  .app (.const "Nat.succ" []) value

def vecType (index : Expr) : Expr :=
  appN (.const "Vec" []) [natType, index]

def vecSpec : IndexedInductiveSpec :=
  {
    name := "Vec"
    resultLevel := .succ .zero
    params :=
      [
        { name := "A", type := type0 }
      ]
    indices :=
      [
        { name := "n", type := natType }
      ]
    constructors :=
      [
        {
          name := "Vec.nil"
          targetIndices := [natZero]
        },
        {
          name := "Vec.cons"
          fields :=
            [
              { name := "n", type := natType },
              { name := "head", type := .bvar 1 },
              { name := "tail", type := appN (.const "Vec" []) [.bvar 2, .bvar 1] }
            ]
          targetIndices := [natSucc (.bvar 2)]
        }
      ]
  }

def alphaType : Expr :=
  .const "Alpha" []

def betaType : Expr :=
  .const "Beta" []

def relType : Expr :=
  pi "x" alphaType (pi "y" alphaType propType)

def fnType : Expr :=
  pi "x" alphaType betaType

def eqBeta (left right : Expr) : Expr :=
  appN (.const "Eq" [.succ .zero]) [betaType, left, right]

def hType : Expr :=
  pi "x" alphaType
    (pi "y" alphaType
      (pi "rel" (appN (.const "r" []) [.bvar 1, .bvar 0])
        (eqBeta (.app (.const "f" []) (.bvar 2)) (.app (.const "f" []) (.bvar 1)))))

def predType : Expr :=
  pi "x" alphaType type0

def predA : Expr :=
  .app (.const "Pred" []) (.const "a" [])

def equalityDeclarations : List Declaration :=
  [
    .axiom "Alpha" [] type0,
    .axiom "Beta" [] type0,
    .axiom "Pred" [] predType,
    .axiom "a" [] alphaType,
    .axiom "predProof" [] predA,
    .axiom "b" [] betaType
  ]

def quotientDeclarations : List Declaration :=
  [
    .axiom "Alpha" [] type0,
    .axiom "Beta" [] type0,
    .axiom "r" [] relType,
    .axiom "f" [] fnType,
    .axiom "h" [] hType,
    .axiom "a" [] alphaType
  ]

def quotMkA : Expr :=
  appN (.const "Quot.mk" [.succ .zero]) [alphaType, .const "r" [], .const "a" []]

def quotLiftA : Expr :=
  appN
    (.const "Quot.lift" [.succ .zero, .succ .zero])
    [
      alphaType,
      .const "r" [],
      betaType,
      .const "f" [],
      .const "h" [],
      quotMkA
    ]

def eqReflA : Expr :=
  appN (.const "Eq.refl" [.succ .zero]) [alphaType, .const "a" []]

def eqRecMotive : Expr :=
  .lam "x" alphaType
    (.lam "h" (appN (.const "Eq" [.succ .zero]) [alphaType, .const "a" [], .bvar 0])
      (.app (.const "Pred" []) (.bvar 1)))

def eqRecTransport : Expr :=
  appN
    (.const "Eq.rec" [.succ .zero, .succ .zero])
    [
      alphaType,
      .const "a" [],
      eqRecMotive,
      .const "predProof" [],
      .const "a" [],
      eqReflA
    ]

def eqNdRecMotive : Expr :=
  .lam "x" alphaType betaType

def eqNdRecTransport : Expr :=
  appN
    (.const "Eq.ndrec" [.succ .zero, .succ .zero])
    [
      alphaType,
      .const "a" [],
      eqNdRecMotive,
      .const "b" [],
      .const "a" [],
      eqReflA
    ]

def dPairSpec : SimpleInductiveSpec :=
  {
    name := "DPair"
    resultLevel := .succ .zero
    params :=
      [
        { name := "A", type := type0 },
        { name := "B", type := pi "x" (.bvar 0) type0 }
      ]
    constructors :=
      [
        {
          name := "DPair.mk"
          fields :=
            [
              { name := "fst", type := .bvar 1 },
              { name := "snd", type := .app (.bvar 1) (.bvar 0) }
            ]
        }
      ]
  }

def dPairTarget : Expr :=
  appN
    (.const "DPair.mk" [])
    [
      alphaType,
      .const "Pred" [],
      .const "a" [],
      .const "predProof" []
    ]

def dPairFst : Expr :=
  .proj "DPair" 0 dPairTarget

def dPairSnd : Expr :=
  .proj "DPair" 1 dPairTarget

def badIndexedTargetSpec : IndexedInductiveSpec :=
  { vecSpec with
    name := "BadVec"
    constructors :=
      [
        {
          name := "BadVec.nil"
          targetIndices := []
        }
      ]
  }

def propIndexedSpec : IndexedInductiveSpec :=
  { vecSpec with
    name := "PropVec"
    resultLevel := .zero
    constructors :=
      [
        {
          name := "PropVec.nil"
          targetIndices := [natZero]
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

def checkIndexedInductives : IO Unit := do
  expectError "indexed inductive disabled"
    (replay MPC.Configs.Poc emptyEnv (baseDeclarations ++ [.indexedInductive vecSpec]))
  let env ← expectOkLabel "Vec replay"
    (replay MPC.Configs.IndexedPoc emptyEnv (baseDeclarations ++ [.indexedInductive vecSpec]))
  expectEnvContains "indexed inductive" env "Vec.rec"
  let motive :=
    .lam "n" natType
      (.lam "target" (vecType (.bvar 0)) (.const "P" []))
  let nilMinor := .const "p" []
  let consMinor :=
    .lam "n" natType
      (.lam "head" natType
        (.lam "tail" (vecType (.bvar 1))
          (.lam "ih" (.const "P" []) (.bvar 0))))
  let nilTarget := appN (.const "Vec.nil" []) [natType]
  let consTarget :=
    appN
      (.const "Vec.cons" [])
      [
        natType,
        natZero,
        natZero,
        nilTarget
      ]
  let recursor :=
    appN
      (.const "Vec.rec" [.zero])
      [
        natType,
        motive,
        nilMinor,
        consMinor,
        natSucc natZero,
        consTarget
      ]
  let reduced ← expectOk (normalize MPC.Configs.IndexedPoc env [] recursor)
  expectExprEq "indexed recursor nested iota" reduced (.const "p" [])
  expectError "indexed constructor target arity"
    (replay MPC.Configs.IndexedPoc emptyEnv (baseDeclarations ++ [.indexedInductive badIndexedTargetSpec]))
  expectError "proposition-valued indexed inductive"
    (replay MPC.Configs.IndexedPoc emptyEnv (baseDeclarations ++ [.indexedInductive propIndexedSpec]))

def checkEquality : IO Unit := do
  expectError "equality primitives disabled"
    (replay MPC.Configs.Poc emptyEnv [.equalityPrimitives])
  expectError "duplicate equality primitives"
    (replay MPC.Configs.EqualityPoc emptyEnv [.equalityPrimitives, .equalityPrimitives])
  let env ← expectOkLabel "equality replay"
    (replay MPC.Configs.EqualityPoc emptyEnv
      (baseDeclarations ++ [.equalityPrimitives] ++ equalityDeclarations))
  expectEnvContains "equality primitives" env "Eq.rec"
  let inferred ← expectOkLabel "Eq.rec inference"
    (infer MPC.Configs.EqualityPoc env [] [] eqRecTransport)
  let inferred ← expectOkLabel "Eq.rec inferred type normalization"
    (normalize MPC.Configs.EqualityPoc env [] inferred)
  expectExprEq "Eq.rec type" inferred predA
  let reduced ← expectOkLabel "Eq.rec reduction"
    (normalize MPC.Configs.EqualityPoc env [] eqRecTransport)
  expectExprEq "Eq.rec value" reduced (.const "predProof" [])
  let ndInferred ← expectOkLabel "Eq.ndrec inference"
    (infer MPC.Configs.EqualityPoc env [] [] eqNdRecTransport)
  let ndInferred ← expectOkLabel "Eq.ndrec inferred type normalization"
    (normalize MPC.Configs.EqualityPoc env [] ndInferred)
  expectExprEq "Eq.ndrec type" ndInferred betaType
  let ndReduced ← expectOkLabel "Eq.ndrec reduction"
    (normalize MPC.Configs.EqualityPoc env [] eqNdRecTransport)
  expectExprEq "Eq.ndrec value" ndReduced (.const "b" [])

def checkProjections : IO Unit := do
  let declarations := baseDeclarations ++ equalityDeclarations ++ [.inductive dPairSpec]
  let baseEnv ← expectOkLabel "projection baseline replay"
    (replay MPC.Configs.Poc emptyEnv declarations)
  expectError "projection disabled"
    (infer MPC.Configs.Poc baseEnv [] [] dPairFst)
  let env ← expectOkLabel "projection replay"
    (replay MPC.Configs.ProjectionPoc emptyEnv declarations)
  expectEnvContains "projection structure" env "DPair"
  let fstType ← expectOkLabel "first projection inference"
    (infer MPC.Configs.ProjectionPoc env [] [] dPairFst)
  expectExprEq "first projection type" fstType alphaType
  let fstReduced ← expectOkLabel "first projection reduction"
    (normalize MPC.Configs.ProjectionPoc env [] dPairFst)
  expectExprEq "first projection value" fstReduced (.const "a" [])
  let sndType ← expectOkLabel "second projection inference"
    (infer MPC.Configs.ProjectionPoc env [] [] dPairSnd)
  expectExprEq "second projection raw type" sndType (.app (.const "Pred" []) dPairFst)
  let sndTypeReduced ← expectOkLabel "second projection type normalization"
    (normalize MPC.Configs.ProjectionPoc env [] sndType)
  expectExprEq "second projection normalized type" sndTypeReduced predA
  expectOkLabel "second projection conversion"
    (check MPC.Configs.ProjectionPoc env [] [] dPairSnd predA)
  let sndReduced ← expectOkLabel "second projection reduction"
    (normalize MPC.Configs.ProjectionPoc env [] dPairSnd)
  expectExprEq "second projection value" sndReduced (.const "predProof" [])
  expectError "projection field out of range"
    (infer MPC.Configs.ProjectionPoc env [] [] (.proj "DPair" 2 dPairTarget))

def checkQuotients : IO Unit := do
  expectError "quotient primitives disabled"
    (replay MPC.Configs.Poc emptyEnv [.quotientPrimitives])
  expectError "quotient primitives without equality"
    (replay MPC.Configs.QuotPoc emptyEnv [.quotientPrimitives])
  expectError "duplicate quotient primitives"
    (replay MPC.Configs.QuotPoc emptyEnv
      [.equalityPrimitives, .quotientPrimitives, .quotientPrimitives])
  let env ← expectOkLabel "quotient replay"
    (replay MPC.Configs.QuotPoc emptyEnv
      (baseDeclarations ++ [.equalityPrimitives, .quotientPrimitives] ++ quotientDeclarations))
  expectEnvContains "quotient primitives" env "Quot.lift"
  let inferred ← expectOkLabel "quotient lift inference"
    (infer MPC.Configs.QuotPoc env [] [] quotLiftA)
  expectExprEq "quotient lift type" inferred betaType
  let reduced ← expectOkLabel "quotient lift reduction"
    (normalize MPC.Configs.QuotPoc env [] quotLiftA)
  expectExprEq "quotient lift value" reduced (.app (.const "f" []) (.const "a" []))

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
  checkIndexedInductives
  checkEquality
  checkProjections
  checkQuotients
  checkAdapters
