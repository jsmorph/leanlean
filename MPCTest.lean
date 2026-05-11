import MPC
import MPC.Adapters.Layer

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

def expect (label : String) (condition : Bool) : IO Unit :=
  if condition then
    pure ()
  else
    throw <| IO.userError label

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

def shadowEnv (env : Env) (info : ConstantInfo) : Env :=
  {
    entries := info :: env.entries
    index := env.index.insert info.name info
    constructorFieldInfo := env.constructorFieldInfo
  }

def type0 : Expr :=
  .sort (.succ .zero)

def propType : Expr :=
  .sort .zero

def natType : Expr :=
  .const "Nat" []

def stringType : Expr :=
  .const "String" []

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

def primitiveBoolSpec : SimpleInductiveSpec :=
  {
    name := "Bool"
    resultLevel := .succ .zero
    constructors :=
      [
        { name := "Bool.false" },
        { name := "Bool.true" }
      ]
  }

def natInductiveSpec : SimpleInductiveSpec :=
  {
    name := "Nat"
    resultLevel := .succ .zero
    constructors :=
      [
        { name := "Nat.zero" },
        {
          name := "Nat.succ"
          fields := [{ name := "n", type := natType }]
        }
      ]
  }

def mutEvenSpec : SimpleInductiveSpec :=
  {
    name := "MutEven"
    resultLevel := .succ .zero
    constructors :=
      [
        { name := "MutEven.zero" },
        {
          name := "MutEven.succOdd"
          fields := [{ name := "pred", type := .const "MutOdd" [] }]
        }
      ]
  }

def mutOddSpec : SimpleInductiveSpec :=
  {
    name := "MutOdd"
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "MutOdd.succEven"
          fields := [{ name := "pred", type := .const "MutEven" [] }]
        }
      ]
  }

def mutEvenOddBlock : InductiveBlockSpec :=
  { levelParams := [], specs := [mutEvenSpec, mutOddSpec] }

def badMutASpec : SimpleInductiveSpec :=
  {
    name := "BadMutA"
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "BadMutA.mk"
          fields := [
            { name := "f", type := .forallE "x" (.const "BadMutB" []) natType }
          ]
        }
      ]
  }

def badMutBSpec : SimpleInductiveSpec :=
  {
    name := "BadMutB"
    resultLevel := .succ .zero
    constructors :=
      [
        { name := "BadMutB.mk", fields := [{ name := "x", type := .const "BadMutA" [] }] }
      ]
  }

def badMutualBlock : InductiveBlockSpec :=
  { levelParams := [], specs := [badMutASpec, badMutBSpec] }

def listSpec : SimpleInductiveSpec :=
  {
    name := "List"
    params := [{ name := "α", type := type0 }]
    resultLevel := .succ .zero
    constructors :=
      [
        { name := "List.nil" },
        {
          name := "List.cons"
          fields :=
            [
              { name := "head", type := .bvar 0 },
              {
                name := "tail"
                type := .app (.const "List" []) (.bvar 1)
              }
            ]
        }
      ]
  }

def arraySpec : SimpleInductiveSpec :=
  {
    name := "Array"
    params := [{ name := "α", type := type0 }]
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "Array.mk"
          fields :=
            [
              {
                name := "toList"
                type := .app (.const "List" []) (.bvar 0)
              }
            ]
        }
      ]
  }

def nestedArraySpec : SimpleInductiveSpec :=
  {
    name := "NestedArray"
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "NestedArray.mk"
          fields :=
            [
              {
                name := "args"
                type := .app (.const "Array" []) (.const "NestedArray" [])
              }
            ]
        }
      ]
  }

def nestedArrayType : Expr :=
  .const "NestedArray" []

def listNestedArrayType : Expr :=
  .app (.const "List" []) nestedArrayType

def arrayNestedArrayType : Expr :=
  .app (.const "Array" []) nestedArrayType

def listNestedArrayNil : Expr :=
  .app (.const "List.nil" []) nestedArrayType

def arrayNestedArrayMk (values : Expr) : Expr :=
  appN (.const "Array.mk" []) [nestedArrayType, values]

def nestedArrayMk (args : Expr) : Expr :=
  .app (.const "NestedArray.mk" []) args

def nestedArrayEmpty : Expr :=
  nestedArrayMk (arrayNestedArrayMk listNestedArrayNil)

def listNestedArrayCons (head tail : Expr) : Expr :=
  appN (.const "List.cons" []) [nestedArrayType, head, tail]

def nestedArrayRootMotive : Expr :=
  .lam "target" nestedArrayType (.const "P" [])

def nestedArrayArrayMotive : Expr :=
  .lam "target" arrayNestedArrayType (.const "P" [])

def nestedArrayListMotive : Expr :=
  .lam "target" listNestedArrayType (.const "P" [])

def nestedArrayRootMinor : Expr :=
  .lam "args" arrayNestedArrayType
    (.lam "ih" (.const "P" []) (.const "p" []))

def nestedArrayArrayMinor : Expr :=
  .lam "toList" listNestedArrayType
    (.lam "ih" (.const "P" []) (.const "p" []))

def nestedArrayListConsMinor : Expr :=
  .lam "head" nestedArrayType
    (.lam "tail" listNestedArrayType
      (.lam "headIH" (.const "P" [])
        (.lam "tailIH" (.const "P" []) (.bvar 0))))

def nestedArrayRecursorOnCons : Expr :=
  appN
    (.const "NestedArray.rec_2" [.zero])
    [
      nestedArrayRootMotive,
      nestedArrayArrayMotive,
      nestedArrayListMotive,
      nestedArrayRootMinor,
      nestedArrayArrayMinor,
      .const "p" [],
      nestedArrayListConsMinor,
      listNestedArrayCons nestedArrayEmpty listNestedArrayNil
    ]

def nestedFnSpec : SimpleInductiveSpec :=
  {
    name := "NestedFn"
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "NestedFn.mk"
          fields :=
            [
              {
                name := "children"
                type :=
                  pi "n" natType
                    (.app (.const "List" []) (.const "NestedFn" []))
              }
            ]
        }
      ]
  }

def nestedFnType : Expr :=
  .const "NestedFn" []

def listNestedFnType : Expr :=
  .app (.const "List" []) nestedFnType

def listNestedFnNil : Expr :=
  .app (.const "List.nil" []) nestedFnType

def nestedFnChildrenValue : Expr :=
  .lam "n" natType listNestedFnNil

def nestedFnTarget : Expr :=
  .app (.const "NestedFn.mk" []) nestedFnChildrenValue

def nestedFnRootMotive : Expr :=
  .lam "target" nestedFnType (.const "P" [])

def nestedFnListMotive : Expr :=
  .lam "target" listNestedFnType (.const "P" [])

def nestedFnRootMinor : Expr :=
  .lam "children" (pi "n" natType listNestedFnType)
    (.lam "ih" (pi "n" natType (.const "P" []))
      (.app (.bvar 0) (.const "Nat.zero" [])))

def nestedFnListConsMinor : Expr :=
  .lam "head" nestedFnType
    (.lam "tail" listNestedFnType
      (.lam "headIH" (.const "P" [])
        (.lam "tailIH" (.const "P" []) (.bvar 0))))

def nestedFnRecursorOnTarget : Expr :=
  appN
    (.const "NestedFn.rec" [.zero])
    [
      nestedFnRootMotive,
      nestedFnListMotive,
      nestedFnRootMinor,
      .const "p" [],
      nestedFnListConsMinor,
      nestedFnTarget
    ]

def nestedIndexedClosedSpec : SimpleInductiveSpec :=
  {
    name := "NestedIndexedClosed"
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "NestedIndexedClosed.mk"
          fields :=
            [
              {
                name := "children"
                type :=
                  appN
                    (.const "Vec" [])
                    [
                      .const "NestedIndexedClosed" [],
                      .const "Nat.zero" []
                    ]
              }
            ]
        }
      ]
  }

def nestedIndexedLocalSpec : SimpleInductiveSpec :=
  {
    name := "NestedIndexedLocal"
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "NestedIndexedLocal.mk"
          fields :=
            [
              {
                name := "children"
                type :=
                  pi "fuel" natType
                    (appN
                      (.const "Vec" [])
                      [
                        .const "NestedIndexedLocal" [],
                        .bvar 0
                      ])
              }
            ]
        }
      ]
  }

def nestedIndexedClosedType : Expr :=
  .const "NestedIndexedClosed" []

def vecNestedIndexedClosedZero : Expr :=
  appN
    (.const "Vec" [])
    [
      nestedIndexedClosedType,
      .const "Nat.zero" []
    ]

def vecNestedIndexedClosedNil : Expr :=
  .app (.const "Vec.nil" []) nestedIndexedClosedType

def nestedIndexedClosedTarget : Expr :=
  .app (.const "NestedIndexedClosed.mk" []) vecNestedIndexedClosedNil

def nestedIndexedClosedRootMotive : Expr :=
  .lam "target" nestedIndexedClosedType (.const "P" [])

def nestedIndexedClosedVecMotive : Expr :=
  .lam "n" natType
    (.lam "target"
      (appN (.const "Vec" []) [nestedIndexedClosedType, .bvar 0])
      (.const "P" []))

def nestedIndexedClosedRootMinor : Expr :=
  .lam "children" vecNestedIndexedClosedZero
    (.lam "ih" (.const "P" []) (.bvar 0))

def nestedIndexedClosedVecConsMinor : Expr :=
  .lam "n" natType
    (.lam "head" nestedIndexedClosedType
      (.lam "tail" (appN (.const "Vec" []) [nestedIndexedClosedType, .bvar 1])
        (.lam "headIH" (.const "P" [])
          (.lam "tailIH" (.const "P" []) (.bvar 0)))))

def nestedIndexedClosedRecursorOnNil : Expr :=
  appN
    (.const "NestedIndexedClosed.rec" [.zero])
    [
      nestedIndexedClosedRootMotive,
      nestedIndexedClosedVecMotive,
      nestedIndexedClosedRootMinor,
      .const "p" [],
      nestedIndexedClosedVecConsMinor,
      nestedIndexedClosedTarget
    ]

def nestedIndexedParamClosedSpec : SimpleInductiveSpec :=
  {
    name := "NestedIndexedParamClosed"
    params := [{ name := "A", type := type0 }]
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "NestedIndexedParamClosed.mk"
          fields :=
            [
              {
                name := "children"
                type :=
                  appN
                    (.const "Vec" [])
                    [
                      .app (.const "NestedIndexedParamClosed" []) (.bvar 0),
                      .const "Nat.zero" []
                    ]
              }
            ]
        }
      ]
  }

def nestedIndexedParamLocalSpec : SimpleInductiveSpec :=
  {
    name := "NestedIndexedParamLocal"
    params := [{ name := "A", type := type0 }]
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "NestedIndexedParamLocal.mk"
          fields :=
            [
              {
                name := "children"
                type :=
                  pi "fuel" natType
                    (appN
                      (.const "Vec" [])
                      [
                        .app (.const "NestedIndexedParamLocal" []) (.bvar 1),
                        .bvar 0
                      ])
              }
            ]
        }
      ]
  }

def nestedIndexedParamClosedNatType : Expr :=
  .app (.const "NestedIndexedParamClosed" []) natType

def vecNestedIndexedParamClosedZero : Expr :=
  appN
    (.const "Vec" [])
    [
      nestedIndexedParamClosedNatType,
      .const "Nat.zero" []
    ]

def vecNestedIndexedParamClosedNil : Expr :=
  .app (.const "Vec.nil" []) nestedIndexedParamClosedNatType

def nestedIndexedParamClosedTarget : Expr :=
  appN
    (.const "NestedIndexedParamClosed.mk" [])
    [
      natType,
      vecNestedIndexedParamClosedNil
    ]

def nestedIndexedParamClosedRootMotive : Expr :=
  .lam "target" nestedIndexedParamClosedNatType (.const "P" [])

def nestedIndexedParamClosedVecMotive : Expr :=
  .lam "n" natType
    (.lam "target"
      (appN (.const "Vec" []) [nestedIndexedParamClosedNatType, .bvar 0])
      (.const "P" []))

def nestedIndexedParamClosedRootMinor : Expr :=
  .lam "children" vecNestedIndexedParamClosedZero
    (.lam "ih" (.const "P" []) (.bvar 0))

def nestedIndexedParamClosedVecConsMinor : Expr :=
  .lam "n" natType
    (.lam "head" nestedIndexedParamClosedNatType
      (.lam "tail" (appN (.const "Vec" []) [nestedIndexedParamClosedNatType, .bvar 1])
        (.lam "headIH" (.const "P" [])
          (.lam "tailIH" (.const "P" []) (.bvar 0)))))

def nestedIndexedParamClosedRecursorOnNil : Expr :=
  appN
    (.const "NestedIndexedParamClosed.rec" [.zero])
    [
      natType,
      nestedIndexedParamClosedRootMotive,
      nestedIndexedParamClosedVecMotive,
      nestedIndexedParamClosedRootMinor,
      .const "p" [],
      nestedIndexedParamClosedVecConsMinor,
      nestedIndexedParamClosedTarget
    ]

def badNestedArraySpec : SimpleInductiveSpec :=
  {
    name := "BadNestedArray"
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "BadNestedArray.mk"
          fields :=
            [
              {
                name := "args"
                type :=
                  .app
                    (.const "Array" [])
                    (pi "f" (.const "BadNestedArray" []) natType)
              }
            ]
        }
      ]
  }

def contraBoxSpec : SimpleInductiveSpec :=
  {
    name := "ContraBox"
    params := [{ name := "A", type := type0 }]
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "ContraBox.mk"
          fields :=
            [
              {
                name := "fn"
                type := pi "x" (.bvar 0) natType
              }
            ]
        }
      ]
  }

def badNestedContraBoxSpec : SimpleInductiveSpec :=
  {
    name := "BadNestedContraBox"
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "BadNestedContraBox.mk"
          fields :=
            [
              {
                name := "box"
                type :=
                  .app (.const "ContraBox" []) (.const "BadNestedContraBox" [])
              }
            ]
        }
      ]
  }

def pairBoxSpec : SimpleInductiveSpec :=
  {
    name := "PairBox"
    params :=
      [
        { name := "A", type := type0 },
        { name := "B", type := type0 }
      ]
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "PairBox.mk"
          fields :=
            [
              { name := "fst", type := .bvar 1 },
              { name := "snd", type := .bvar 1 }
            ]
        }
      ]
  }

def nestedPairBoxSpec : SimpleInductiveSpec :=
  {
    name := "NestedPairBox"
    params := [{ name := "A", type := type0 }]
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "NestedPairBox.mk"
          fields :=
            [
              {
                name := "children"
                type :=
                  appN
                    (.const "PairBox" [])
                    [
                      .bvar 0,
                      .app (.const "NestedPairBox" []) (.bvar 0)
                    ]
              }
            ]
        }
      ]
  }

def indexedPairBoxSpec : IndexedInductiveSpec :=
  {
    name := "IndexedPairBox"
    params :=
      [
        { name := "A", type := type0 },
        { name := "B", type := type0 }
      ]
    indices := [{ name := "n", type := natType }]
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "IndexedPairBox.mk"
          fields := [{ name := "value", type := .bvar 0 }]
          targetIndices := [.const "Nat.zero" []]
        }
      ]
  }

def nestedIndexedPairBoxSpec : SimpleInductiveSpec :=
  {
    name := "NestedIndexedPairBox"
    params := [{ name := "A", type := type0 }]
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "NestedIndexedPairBox.mk"
          fields :=
            [
              {
                name := "children"
                type :=
                  appN
                    (.const "IndexedPairBox" [])
                    [
                      .bvar 0,
                      .app (.const "NestedIndexedPairBox" []) (.bvar 0),
                      .const "Nat.zero" []
                    ]
              }
            ]
        }
      ]
  }

def badPairBoxSpec : SimpleInductiveSpec :=
  {
    name := "BadPairBox"
    params :=
      [
        { name := "A", type := type0 },
        { name := "B", type := type0 }
      ]
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "BadPairBox.mk"
          fields :=
            [
              {
                name := "fn"
                type := pi "x" (.bvar 0) natType
              }
            ]
        }
      ]
  }

def badNestedPairBoxSpec : SimpleInductiveSpec :=
  {
    name := "BadNestedPairBox"
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "BadNestedPairBox.mk"
          fields :=
            [
              {
                name := "children"
                type :=
                  appN
                    (.const "BadPairBox" [])
                    [
                      natType,
                      .const "BadNestedPairBox" []
                    ]
              }
            ]
        }
      ]
  }

def recNatSpec : SimpleInductiveSpec :=
  {
    name := "RecNat"
    resultLevel := .succ .zero
    constructors :=
      [
        { name := "RecNat.zero" },
        {
          name := "RecNat.succ"
          fields := [{ name := "n", type := .const "RecNat" [] }]
        }
      ]
  }

def recNatType : Expr :=
  .const "RecNat" []

def recNatZero : Expr :=
  .const "RecNat.zero" []

def recNatSucc (value : Expr) : Expr :=
  .app (.const "RecNat.succ" []) value

def recNatMotiveType : Expr :=
  pi "target" recNatType propType

def recNatCasesOnType : Expr :=
  pi "motive" recNatMotiveType
    (pi "zeroCase" (.app (.bvar 0) recNatZero)
      (pi "succCase"
        (pi "n" recNatType (.app (.bvar 2) (recNatSucc (.bvar 0))))
        (pi "target" recNatType (.app (.bvar 3) (.bvar 0)))))

def recNatCasesOnValue : Expr :=
  .lam "motive" recNatMotiveType
    (.lam "zeroCase" (.app (.bvar 0) recNatZero)
      (.lam "succCase"
        (pi "n" recNatType (.app (.bvar 2) (recNatSucc (.bvar 0))))
        (.lam "target" recNatType
          (appN
            (.const "RecNat.rec" [.zero])
            [
              .bvar 3,
              .bvar 2,
              .lam "n" recNatType
                (.lam "ih" (.app (.bvar 4) (.bvar 0))
                  (.app (.bvar 3) (.bvar 1))),
              .bvar 0
            ]))))

def ofNatLevel : Level :=
  .param "u"

def ofNatAlphaSort : Expr :=
  .sort (.succ ofNatLevel)

def ofNatSpec : SimpleInductiveSpec :=
  {
    name := "OfNat"
    levelParams := ["u"]
    params :=
      [
        { name := "α", type := ofNatAlphaSort },
        { name := "n", type := natType }
      ]
    resultLevel := .succ ofNatLevel
    constructors :=
      [
        {
          name := "OfNat.mk"
          fields := [{ name := "ofNat", type := .bvar 1 }]
        }
      ]
  }

def ofNatApp (level : Level) (alpha index : Expr) : Expr :=
  appN (.const "OfNat" [level]) [alpha, index]

def ofNatAccessorType : Expr :=
  pi "α" ofNatAlphaSort
    (pi "n" natType
      (pi "self" (ofNatApp ofNatLevel (.bvar 1) (.bvar 0)) (.bvar 2)))

def ofNatAccessorValue : Expr :=
  .lam "α" ofNatAlphaSort
    (.lam "n" natType
      (.lam "self" (ofNatApp ofNatLevel (.bvar 1) (.bvar 0))
        (.proj "OfNat" 0 (.bvar 0))))

def instOfNatNatType : Expr :=
  pi "n" natType (ofNatApp .zero natType (.bvar 0))

def instOfNatNatValue : Expr :=
  .lam "n" natType
    (appN (.const "OfNat.mk" [.zero]) [natType, .bvar 0, .bvar 0])

def ofNatZeroExpr : Expr :=
  appN
    (.const "OfNat.ofNat" [.zero])
    [
      natType,
      .lit (.nat 0),
      .app (.const "instOfNatNat" []) (.lit (.nat 0))
    ]

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

def propChoiceSpec : SimpleInductiveSpec :=
  {
    name := "PropChoice"
    resultLevel := .zero
    constructors :=
      [
        { name := "PropChoice.left" },
        { name := "PropChoice.right" }
      ]
  }

def propOnlyRecursorType : Expr :=
  pi "motive"
    (pi "target" (.const "PropOnly" []) propType)
    (pi "PropOnly.intro.minor"
      (.app (.bvar 0) (.const "PropOnly.intro" []))
      (pi "target" (.const "PropOnly" []) (.app (.bvar 2) (.bvar 0))))

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

def boolType : Expr :=
  .const "Bool" []

def boolFalse : Expr :=
  .const "Bool.false" []

def boolTrue : Expr :=
  .const "Bool.true" []

def natBinaryNatType : Expr :=
  pi "a" natType (pi "b" natType natType)

def natBinaryBoolType : Expr :=
  pi "a" natType (pi "b" natType boolType)

def natBinaryNatZeroValue : Expr :=
  .lam "a" natType (.lam "b" natType natZero)

def natBinaryBoolFalseValue : Expr :=
  .lam "a" natType (.lam "b" natType boolFalse)

def primitiveNatDeclarations : List Declaration :=
  [
    .inductive primitiveBoolSpec,
    .axiom "m" [] natType,
    .definition "Nat.add" [] natBinaryNatType natBinaryNatZeroValue,
    .definition "Nat.mul" [] natBinaryNatType natBinaryNatZeroValue,
    .definition "Nat.pow" [] natBinaryNatType natBinaryNatZeroValue,
    .definition "Nat.sub" [] natBinaryNatType natBinaryNatZeroValue,
    .definition "Nat.beq" [] natBinaryBoolType natBinaryBoolFalseValue,
    .definition "Nat.ble" [] natBinaryBoolType natBinaryBoolFalseValue
  ]

def etaDeclarations : List Declaration :=
  [
    .axiom "f" [] (pi "x" natType natType)
  ]

def etaExpandedF : Expr :=
  .lam "x" natType (.app (.const "f" []) (.bvar 0))

def etaNatAddOne : Expr :=
  .lam "x" natType (appN (.const "Nat.add" []) [.bvar 0, .lit (.nat 1)])

def vecType (index : Expr) : Expr :=
  appN (.const "Vec" []) [natType, index]

def propVecType (index : Expr) : Expr :=
  appN (.const "PropVec" []) [natType, index]

def reachType (index : Expr) : Expr :=
  appN (.const "Reach" []) [.const "Alpha" [], .const "r" [], index]

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

def eqAlpha (left right : Expr) : Expr :=
  appN (.const "Eq" [.succ .zero]) [alphaType, left, right]

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
    .axiom "Fam" [] (pi "T" type0 type0),
    .definition "AlphaAlias" [] type0 alphaType,
    .axiom "Pred" [] predType,
    .axiom "a" [] alphaType,
    .axiom "predProof" [] predA,
    .axiom "b" [] betaType,
    .axiom "famValue" [] (appN (.const "Fam" []) [alphaType])
  ]

def equalityEndpointProofDeclarations : List Declaration :=
  [
    .axiom "famEq" []
      (appN (.const "Eq" [.succ (.succ .zero)])
        [
          type0,
          appN (.const "Fam" []) [alphaType],
          appN (.const "Fam" []) [.const "AlphaAlias" []]
        ])
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

def relLamLeft : Expr :=
  .lam "x" alphaType (.lam "y" alphaType (.const "P" []))

def relLamRight : Expr :=
  .lam "a" alphaType (.lam "b" alphaType (.const "P" []))

def hLamType : Expr :=
  pi "x" alphaType
    (pi "y" alphaType
      (pi "rel" (appN relLamRight [.bvar 1, .bvar 0])
        (eqBeta (.app (.const "f" []) (.bvar 2)) (.app (.const "f" []) (.bvar 1)))))

def quotientAlphaRelationDeclarations : List Declaration :=
  quotientDeclarations ++ [.axiom "hLam" [] hLamType]

def hAliasType : Expr :=
  pi "x" alphaType
    (pi "y" alphaType
      (pi "rel" (appN (.const "rAlias" []) [.bvar 1, .bvar 0])
        (eqBeta (.app (.const "f" []) (.bvar 2)) (.app (.const "f" []) (.bvar 1)))))

def quotientTransparentRelationDeclarations : List Declaration :=
  quotientDeclarations ++
    [
      .definition "rAlias" [] relType (.const "r" []),
      .axiom "hAlias" [] hAliasType
    ]

def quotTypeA : Expr :=
  appN (.const "Quot" [.succ .zero]) [alphaType, .const "r" []]

def quotLiftFnType : Expr :=
  pi "q" quotTypeA betaType

def quotLiftFnValue : Expr :=
  appN
    (.const "Quot.lift" [.succ .zero, .succ .zero])
    [
      alphaType,
      .const "r" [],
      betaType,
      .const "f" [],
      .const "h" []
    ]

def quotientLiftHeadDefinitionDeclarations : List Declaration :=
  quotientDeclarations ++
    [
      .definition "liftFn" [] quotLiftFnType quotLiftFnValue
    ]

def quotMkA : Expr :=
  appN (.const "Quot.mk" [.succ .zero]) [alphaType, .const "r" [], .const "a" []]

def quotMkRelLamA : Expr :=
  appN (.const "Quot.mk" [.succ .zero]) [alphaType, relLamLeft, .const "a" []]

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

def quotLiftAlphaRenamedRelation : Expr :=
  appN
    (.const "Quot.lift" [.succ .zero, .succ .zero])
    [
      alphaType,
      relLamRight,
      betaType,
      .const "f" [],
      .const "hLam" [],
      quotMkRelLamA
    ]

def quotLiftTransparentRelation : Expr :=
  appN
    (.const "Quot.lift" [.succ .zero, .succ .zero])
    [
      alphaType,
      .const "rAlias" [],
      betaType,
      .const "f" [],
      .const "hAlias" [],
      quotMkA
    ]

def quotLiftViaDefinition : Expr :=
  .app (.const "liftFn" []) quotMkA

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

def eqRecKTransport : Expr :=
  appN
    (.const "Eq.rec" [.succ .zero, .succ .zero])
    [
      alphaType,
      .const "a" [],
      eqRecMotive,
      .const "predProof" [],
      .const "a" [],
      .const "aEqA" []
    ]

def eqRecNestedEndpointMotive : Expr :=
  .lam "T" type0
    (.lam "h"
      (appN (.const "Eq" [.succ (.succ .zero)])
        [
          type0,
          appN (.const "Fam" []) [alphaType],
          .bvar 0
        ])
      (.bvar 1))

def eqRecNestedEndpointTransport : Expr :=
  appN
    (.const "Eq.rec" [.succ .zero, .succ (.succ .zero)])
    [
      type0,
      appN (.const "Fam" []) [alphaType],
      eqRecNestedEndpointMotive,
      .const "famValue" [],
      appN (.const "Fam" []) [.const "AlphaAlias" []],
      .const "famEq" []
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

def eqSymmType : Expr :=
  pi "a" alphaType
    (pi "b" alphaType
      (pi "h" (eqAlpha (.bvar 1) (.bvar 0))
        (eqAlpha (.bvar 1) (.bvar 2))))

def eqSymmMotive : Expr :=
  .lam "x" alphaType
    (.lam "hx" (eqAlpha (.bvar 3) (.bvar 0))
      (eqAlpha (.bvar 1) (.bvar 4)))

def eqSymmValue : Expr :=
  .lam "a" alphaType
    (.lam "b" alphaType
      (.lam "h" (eqAlpha (.bvar 1) (.bvar 0))
        (appN
          (.const "Eq.rec" [.zero, .succ .zero])
          [
            alphaType,
            .bvar 2,
            eqSymmMotive,
            appN (.const "Eq.refl" [.succ .zero]) [alphaType, .bvar 2],
            .bvar 1,
            .bvar 0
          ])))

def proofBoxSpec : SimpleInductiveSpec :=
  {
    name := "ProofBox"
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "ProofBox.mk"
          fields :=
            [
              { name := "value", type := alphaType },
              { name := "proof", type := .const "P" [] }
            ]
        }
      ]
  }

def proofBoxType : Expr :=
  .const "ProofBox" []

def proofBoxP : Expr :=
  appN (.const "ProofBox.mk" []) [.const "a" [], .const "p" []]

def proofBoxQ : Expr :=
  appN (.const "ProofBox.mk" []) [.const "a" [], .const "q" []]

def proofBoxEqType : Expr :=
  appN (.const "Eq" [.succ .zero]) [proofBoxType, proofBoxP, proofBoxQ]

def proofBoxEqRecMotive : Expr :=
  .lam "x" proofBoxType
    (.lam "h" (appN (.const "Eq" [.succ .zero]) [proofBoxType, proofBoxP, .bvar 0])
      betaType)

def proofBoxEqRecTransport : Expr :=
  appN
    (.const "Eq.rec" [.succ .zero, .succ .zero])
    [
      proofBoxType,
      proofBoxP,
      proofBoxEqRecMotive,
      .const "b" [],
      proofBoxQ,
      .const "proofBoxEq" []
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

def dPairType : Expr :=
  appN (.const "DPair" []) [alphaType, .const "Pred" []]

def dPairStuckTarget : Expr :=
  .const "dPairStuck" []

def dPairStuckFst : Expr :=
  .proj "DPair" 0 dPairStuckTarget

def dPairStuckSnd : Expr :=
  .proj "DPair" 1 dPairStuckTarget

def dPairEtaConstructor : Expr :=
  appN
    (.const "DPair.mk" [])
    [
      alphaType,
      .const "Pred" [],
      dPairStuckFst,
      dPairStuckSnd
    ]

def dPairEtaFstMotive : Expr :=
  .lam "target" dPairType alphaType

def dPairEtaFstMinor : Expr :=
  .lam "fst" alphaType
    (.lam "snd" (.app (.const "Pred" []) (.bvar 0)) (.bvar 1))

def dPairRecFstEta : Expr :=
  appN
    (.const "DPair.rec" [.succ .zero])
    [
      alphaType,
      .const "Pred" [],
      dPairEtaFstMotive,
      dPairEtaFstMinor,
      dPairStuckTarget
    ]

def dPairEtaSndMotive : Expr :=
  .lam "target" dPairType
    (.app (.const "Pred" []) (.proj "DPair" 0 (.bvar 0)))

def dPairEtaSndMinor : Expr :=
  .lam "fst" alphaType
    (.lam "snd" (.app (.const "Pred" []) (.bvar 0)) (.bvar 0))

def dPairRecSndEta : Expr :=
  appN
    (.const "DPair.rec" [.succ .zero])
    [
      alphaType,
      .const "Pred" [],
      dPairEtaSndMotive,
      dPairEtaSndMinor,
      dPairStuckTarget
    ]

def unitLikeSpec : SimpleInductiveSpec :=
  {
    name := "UnitLike"
    resultLevel := .succ .zero
    constructors :=
      [
        { name := "UnitLike.unit" }
      ]
  }

def phantomSpec : SimpleInductiveSpec :=
  {
    name := "Phantom"
    resultLevel := .succ .zero
    params :=
      [
        { name := "A", type := type0 }
      ]
    constructors :=
      [
        { name := "Phantom.mk" }
      ]
  }

def unitBoxSpec : SimpleInductiveSpec :=
  {
    name := "UnitBox"
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "UnitBox.mk"
          fields := [{ name := "as", type := .const "UnitLike" [] }]
        }
      ]
  }

def hAddLikeSpec : SimpleInductiveSpec :=
  {
    name := "HAddLike"
    levelParams := ["u", "v", "w"]
    params :=
      [
        { name := "α", type := .sort (.param "u") },
        { name := "β", type := .sort (.param "v") },
        { name := "γ", type := .sort (.param "w") }
      ]
    resultLevel :=
      .max
        (.max (.succ (.param "u")) (.succ (.param "v")))
        (.succ (.param "w"))
    constructors :=
      [
        {
          name := "HAddLike.mk"
          fields :=
            [
              {
                name := "hAdd"
                type := pi "x" (.bvar 2) (pi "y" (.bvar 2) (.bvar 2))
              }
            ]
        }
      ]
  }

def hAddLikeApp (alpha beta gamma : Expr) : Expr :=
  appN (.const "HAddLike" [.param "u", .param "v", .param "w"]) [alpha, beta, gamma]

def hAddLikeAccessorType : Expr :=
  pi "α" (.sort (.param "u"))
    (pi "β" (.sort (.param "v"))
      (pi "γ" (.sort (.param "w"))
        (pi "self" (hAddLikeApp (.bvar 2) (.bvar 1) (.bvar 0))
          (pi "x" (.bvar 3) (pi "y" (.bvar 3) (.bvar 3))))))

def hAddLikeAccessorValue : Expr :=
  .lam "α" (.sort (.param "u"))
    (.lam "β" (.sort (.param "v"))
      (.lam "γ" (.sort (.param "w"))
        (.lam "self" (hAddLikeApp (.bvar 2) (.bvar 1) (.bvar 0))
          (.proj "HAddLike" 0 (.bvar 0)))))

def universeFieldSpec : SimpleInductiveSpec :=
  {
    name := "UniverseField"
    levelParams := ["u"]
    params := [{ name := "α", type := .sort (.param "u") }]
    resultLevel := .succ (.param "u")
    constructors :=
      [
        {
          name := "UniverseField.mk"
          fields := [{ name := "field", type := .sort (.param "u") }]
        }
      ]
  }

def universeFieldTarget : Expr :=
  appN (.const "UniverseField.mk" [.zero]) [.const "P" [], .const "P" []]

def universeFieldProjection : Expr :=
  .proj "UniverseField" 0 universeFieldTarget

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

def sameSpec : IndexedInductiveSpec :=
  {
    name := "Same"
    levelParams := ["u"]
    params :=
      [
        { name := "A", type := .sort (.param "u") },
        { name := "a", type := .bvar 0 }
      ]
    indices :=
      [
        { name := "b", type := .bvar 1 }
      ]
    resultLevel := .zero
    constructors :=
      [
        {
          name := "Same.refl"
          targetIndices := [.bvar 0]
        }
      ]
  }

def reachSpec : IndexedInductiveSpec :=
  {
    name := "Reach"
    resultLevel := .zero
    params :=
      [
        { name := "A", type := type0 },
        { name := "R", type := pi "x" (.bvar 0) (pi "y" (.bvar 1) propType) }
      ]
    indices :=
      [
        { name := "x", type := .bvar 1 }
      ]
    constructors :=
      [
        {
          name := "Reach.intro"
          fields :=
            [
              { name := "x", type := .bvar 1 },
              {
                name := "step"
                type :=
                  pi "y" (.bvar 2)
                    (pi "h" (appN (.bvar 2) [.bvar 0, .bvar 1])
                      (appN (.const "Reach" []) [.bvar 4, .bvar 3, .bvar 1]))
              }
            ]
          targetIndices := [.bvar 1]
        }
      ]
  }

def reachStepTypeA : Expr :=
  pi "y" alphaType
    (pi "h" (appN (.const "r" []) [.bvar 0, .const "a" []])
      (reachType (.bvar 1)))

def reachStepTypeForBoundX : Expr :=
  pi "y" alphaType
    (pi "h" (appN (.const "r" []) [.bvar 0, .bvar 1])
      (reachType (.bvar 1)))

def reachIHTypeForBoundX : Expr :=
  pi "y" alphaType
    (pi "h" (appN (.const "r" []) [.bvar 0, .bvar 2])
      (.const "P" []))

def useReachIHType : Expr :=
  pi "x" alphaType
    (pi "ih" (pi "y" alphaType (pi "h" (appN (.const "r" []) [.bvar 0, .bvar 1]) (.const "P" [])))
      (.const "P" []))

def reachPreDeclarations : List Declaration :=
  [
    .axiom "Alpha" [] type0,
    .axiom "r" [] relType,
    .axiom "a" [] alphaType,
    .axiom "UseReachIH" [] useReachIHType
  ]

def reachPostDeclarations : List Declaration :=
  [
    .axiom "step" [] reachStepTypeA
  ]

def reachMotive : Expr :=
  .lam "x" alphaType
    (.lam "target" (reachType (.bvar 0)) (.const "P" []))

def reachMinor : Expr :=
  .lam "x" alphaType
    (.lam "step" reachStepTypeForBoundX
      (.lam "ih" reachIHTypeForBoundX
        (appN (.const "UseReachIH" []) [.bvar 2, .bvar 0])))

def reachTarget : Expr :=
  appN (.const "Reach.intro" []) [alphaType, .const "r" [], .const "a" [], .const "step" []]

def reachRecursorOnTarget : Expr :=
  appN
    (.const "Reach.rec" [])
    [
      alphaType,
      .const "r" [],
      reachMotive,
      reachMinor,
      .const "a" [],
      reachTarget
    ]

def reachExpectedIH : Expr :=
  .lam "y" alphaType
    (.lam "h" (appN (.const "r" []) [.bvar 0, .const "a" []])
      (appN
        (.const "Reach.rec" [])
        [
          alphaType,
          .const "r" [],
          reachMotive.lift 2,
          reachMinor.lift 2,
          .bvar 1,
          appN (.const "step" []) [.bvar 1, .bvar 0]
        ]))

def reachExpectedReduction : Expr :=
  appN (.const "UseReachIH" []) [.const "a" [], reachExpectedIH]

def reachLargeMotive : Expr :=
  .lam "x" alphaType
    (.lam "target" (reachType (.bvar 0)) natType)

def reachLargeIHTypeForBoundX : Expr :=
  pi "y" alphaType
    (pi "h" (appN (.const "r" []) [.bvar 0, .bvar 2])
      natType)

def reachLargeMinor : Expr :=
  .lam "x" alphaType
    (.lam "step" reachStepTypeForBoundX
      (.lam "ih" reachLargeIHTypeForBoundX
        natZero))

def reachLargeRecursorOnTarget : Expr :=
  appN
    (.const "Reach.rec" [.succ .zero])
    [
      alphaType,
      .const "r" [],
      reachLargeMotive,
      reachLargeMinor,
      .const "a" [],
      reachTarget
    ]

def checkBasePackages : IO Unit := do
  expectOkLabel "manifest validation" (Manifest.validate MPC.Configs.Poc)
  expectOkLabel "Lean 4.29 manifest validation" (Manifest.validate MPC.Configs.LeanCore429)
  let env ← expectOk (replay MPC.Configs.Poc emptyEnv baseDeclarations)
  let proofArgEnv ← expectOkLabel "proof-argument axiom"
    (addDecl MPC.Configs.Poc env
      (.axiom "UseProof" [] (pi "h" (.const "P" []) natType)))
  expectOkLabel "proof irrelevance below application"
    (defEq MPC.Configs.Poc proofArgEnv [] []
      (.app (.const "UseProof" []) (.const "p" []))
      (.app (.const "UseProof" []) (.const "q" [])))
  let literalType ← expectOk (infer MPC.Configs.Poc env [] [] (.lit (.nat 3)))
  expectExprEq "natural literal type" literalType natType
  expectError "string literal disabled in PoC"
    (infer MPC.Configs.Poc env [] [] (.lit (.str "")))
  let stringEnv ← expectOk
    (replay MPC.Configs.LeanCore429 emptyEnv (baseDeclarations ++ [.axiom "String" [] type0]))
  let stringLiteralType ← expectOk
    (infer MPC.Configs.LeanCore429 stringEnv [] [] (.lit (.str "")))
  expectExprEq "string literal type" stringLiteralType stringType
  let zetaExpr :=
    .letE "F" (pi "n" natType propType)
      (.lam "n" natType (.const "P" []))
      (.letE "h" (.app (.bvar 0) natZero) (.const "p" []) (.bvar 0))
  expectOkLabel "let body checks with zeta"
    (check MPC.Configs.Poc env [] [] zetaExpr (.const "P" []))
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
  expectError "nested container disabled"
    (replay MPC.Configs.Poc emptyEnv
      (baseDeclarations ++ [.inductive listSpec, .inductive arraySpec, .inductive nestedArraySpec]))
  expectError "nested container unavailable"
    (replay MPC.Configs.LeanCore429 emptyEnv (baseDeclarations ++ [.inductive nestedArraySpec]))
  let nestedEnv ← expectOkLabel "nested Array recursive field"
    (replay MPC.Configs.LeanCore429 emptyEnv
      (baseDeclarations ++ [.inductive listSpec, .inductive arraySpec, .inductive nestedArraySpec]))
  expectEnvContains "nested Array recursor" nestedEnv "NestedArray.rec"
  expectEnvContains "nested Array helper recursor" nestedEnv "NestedArray.rec_1"
  expectEnvContains "nested List helper recursor" nestedEnv "NestedArray.rec_2"
  match nestedEnv.find? "NestedArray.rec_2" with
  | some { kind := .nestedRecursor info, .. } =>
      expect "nested List helper target index" (info.targetIndex == 2)
      expect "nested recursor family target count" (info.targets.length == 3)
  | some _ => throw <| IO.userError "nested List helper recursor has wrong kind"
  | none => throw <| IO.userError "nested List helper recursor missing"
  let nestedReduced ← expectOkLabel "nested helper recursor reduction"
    (normalize MPC.Configs.LeanCore429 nestedEnv [] nestedArrayRecursorOnCons)
  expectExprEq "nested helper recursor iota" nestedReduced (.const "p" [])
  let nestedFnEnv ← expectOkLabel "nested function-field replay"
    (replay MPC.Configs.LeanCore429 emptyEnv
      (baseDeclarations ++ [.inductive listSpec, .inductive nestedFnSpec]))
  expectEnvContains "nested function-field root recursor" nestedFnEnv "NestedFn.rec"
  expectEnvContains "nested function-field helper recursor" nestedFnEnv "NestedFn.rec_1"
  let nestedFnReduced ← expectOkLabel "nested function-field recursor reduction"
    (normalize MPC.Configs.LeanCore429 nestedFnEnv [] nestedFnRecursorOnTarget)
  expectExprEq "nested function-field iota" nestedFnReduced (.const "p" [])
  let nestedIndexedClosedEnv ← expectOkLabel "closed indexed helper replay"
    (replay MPC.Configs.LeanCore429 emptyEnv
      (baseDeclarations ++ [.indexedInductive vecSpec, .inductive nestedIndexedClosedSpec]))
  expectEnvContains
    "closed indexed helper root recursor"
    nestedIndexedClosedEnv
    "NestedIndexedClosed.rec"
  expectEnvContains
    "closed indexed helper target recursor"
    nestedIndexedClosedEnv
    "NestedIndexedClosed.rec_1"
  let nestedIndexedClosedReduced ← expectOkLabel "closed indexed helper reduction"
    (normalize MPC.Configs.LeanCore429 nestedIndexedClosedEnv [] nestedIndexedClosedRecursorOnNil)
  expectExprEq "closed indexed helper iota" nestedIndexedClosedReduced (.const "p" [])
  let nestedIndexedLocalEnv ← expectOkLabel "local indexed helper replay"
    (replay MPC.Configs.LeanCore429 emptyEnv
      (baseDeclarations ++ [.indexedInductive vecSpec, .inductive nestedIndexedLocalSpec]))
  expectEnvContains
    "local indexed helper root recursor"
    nestedIndexedLocalEnv
    "NestedIndexedLocal.rec"
  expectEnvContains
    "local indexed helper target recursor"
    nestedIndexedLocalEnv
    "NestedIndexedLocal.rec_1"
  match nestedIndexedLocalEnv.find? "NestedIndexedLocal.rec_1" with
  | some { kind := .nestedRecursor info, .. } =>
      expect "local indexed helper target index" (info.targetIndex == 1)
      expect "local indexed helper family target count" (info.targets.length == 2)
      match listGet? info.targets 1 with
      | some target =>
          expect "local indexed helper target local count" (target.locals.length == 1)
      | none => throw <| IO.userError "local indexed helper target missing"
  | some _ => throw <| IO.userError "local indexed helper recursor has wrong kind"
  | none => throw <| IO.userError "local indexed helper recursor missing"
  let nestedIndexedParamClosedEnv ← expectOkLabel "parameterized closed indexed helper replay"
    (replay MPC.Configs.LeanCore429 emptyEnv
      (baseDeclarations ++ [.indexedInductive vecSpec, .inductive nestedIndexedParamClosedSpec]))
  expectEnvContains
    "parameterized closed indexed helper target recursor"
    nestedIndexedParamClosedEnv
    "NestedIndexedParamClosed.rec_1"
  let nestedIndexedParamClosedReduced ←
    expectOkLabel "parameterized closed indexed helper reduction"
      (normalize
        MPC.Configs.LeanCore429
        nestedIndexedParamClosedEnv
        []
        nestedIndexedParamClosedRecursorOnNil)
  expectExprEq
    "parameterized closed indexed helper iota"
    nestedIndexedParamClosedReduced
    (.const "p" [])
  let nestedIndexedParamLocalEnv ← expectOkLabel "parameterized local indexed helper replay"
    (replay MPC.Configs.LeanCore429 emptyEnv
      (baseDeclarations ++ [.indexedInductive vecSpec, .inductive nestedIndexedParamLocalSpec]))
  expectEnvContains
    "parameterized local indexed helper target recursor"
    nestedIndexedParamLocalEnv
    "NestedIndexedParamLocal.rec_1"
  match nestedIndexedParamLocalEnv.find? "NestedIndexedParamLocal.rec_1" with
  | some { kind := .nestedRecursor info, .. } =>
      match listGet? info.targets 1 with
      | some target =>
          expect "parameterized local indexed helper target local count" (target.locals.length == 1)
      | none => throw <| IO.userError "parameterized local indexed helper target missing"
  | some _ => throw <| IO.userError "parameterized local indexed helper recursor has wrong kind"
  | none => throw <| IO.userError "parameterized local indexed helper recursor missing"
  let nestedPairBoxEnv ← expectOkLabel "multi-parameter nested helper replay"
    (replay MPC.Configs.LeanCore429 emptyEnv
      (baseDeclarations ++ [.inductive pairBoxSpec, .inductive nestedPairBoxSpec]))
  expectEnvContains
    "multi-parameter nested helper target recursor"
    nestedPairBoxEnv
    "NestedPairBox.rec_1"
  let nestedIndexedPairBoxEnv ← expectOkLabel "multi-parameter indexed helper replay"
    (replay MPC.Configs.LeanCore429 emptyEnv
      (baseDeclarations ++
        [.indexedInductive indexedPairBoxSpec, .inductive nestedIndexedPairBoxSpec]))
  expectEnvContains
    "multi-parameter indexed helper target recursor"
    nestedIndexedPairBoxEnv
    "NestedIndexedPairBox.rec_1"
  match nestedIndexedPairBoxEnv.find? "NestedIndexedPairBox.rec_1" with
  | some { kind := .nestedRecursor info, .. } =>
      match listGet? info.targets 1 with
      | some target =>
          expect "multi-parameter indexed helper target local count" (target.locals.length == 1)
      | none => throw <| IO.userError "multi-parameter indexed helper target missing"
  | some _ => throw <| IO.userError "multi-parameter indexed helper recursor has wrong kind"
  | none => throw <| IO.userError "multi-parameter indexed helper recursor missing"
  expectError "negative occurrence inside nested container"
    (replay MPC.Configs.LeanCore429 emptyEnv
      (baseDeclarations ++ [.inductive listSpec, .inductive arraySpec, .inductive badNestedArraySpec]))
  expectError "non-covariant user container"
    (replay MPC.Configs.LeanCore429 emptyEnv
      (baseDeclarations ++ [.inductive contraBoxSpec, .inductive badNestedContraBoxSpec]))
  expectError "non-covariant two-parameter user container"
    (replay MPC.Configs.LeanCore429 emptyEnv
      (baseDeclarations ++ [.inductive badPairBoxSpec, .inductive badNestedPairBoxSpec]))
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
  let recNatDecls :=
    [
      .axiom "P" [] propType,
      .axiom "p" [] (.const "P" []),
      .inductive recNatSpec,
      .definition "RecNat.casesOn" [] recNatCasesOnType recNatCasesOnValue
    ]
  let recNatEnv ← expectOkLabel "recursive simple inductive replay"
    (replay MPC.Configs.Poc emptyEnv recNatDecls)
  expectEnvContains "recursive simple inductive recursor" recNatEnv "RecNat.rec"
  expectEnvContains "recursive simple inductive casesOn" recNatEnv "RecNat.casesOn"
  let recNatMotive := .lam "target" recNatType (.const "P" [])
  let recNatSuccMinor :=
    .lam "n" recNatType (.lam "ih" (.const "P" []) (.bvar 0))
  let recNatRecursor :=
    appN
      (.const "RecNat.rec" [.zero])
      [
        recNatMotive,
        .const "p" [],
        recNatSuccMinor,
        recNatSucc recNatZero
      ]
  let recNatReduced ← expectOkLabel "recursive simple recursor reduction"
    (normalize MPC.Configs.Poc recNatEnv [] recNatRecursor)
  expectExprEq "recursive simple recursor iota" recNatReduced (.const "p" [])
  let natLiteralEnv ← expectOkLabel "Nat inductive replay"
    (replay MPC.Configs.Poc emptyEnv
      [.axiom "P" [] propType, .axiom "p" [] (.const "P" []), .inductive natInductiveSpec])
  let natLiteralMotive := .lam "target" natType (.const "P" [])
  let natLiteralSuccMinor :=
    .lam "n" natType (.lam "ih" (.const "P" []) (.bvar 0))
  let natLiteralRecursor :=
    appN
      (.const "Nat.rec" [.zero])
      [
        natLiteralMotive,
        .const "p" [],
        natLiteralSuccMinor,
        .lit (.nat 1)
      ]
  let natLiteralReduced ← expectOkLabel "Nat.rec literal reduction"
    (normalize MPC.Configs.Poc natLiteralEnv [] natLiteralRecursor)
  expectExprEq "Nat.rec literal iota" natLiteralReduced (.const "p" [])
  let ofNatEnv ← expectOkLabel "OfNat replay"
    (replay MPC.Configs.LeanCore429 emptyEnv
      [
        .inductive natInductiveSpec,
        .inductive ofNatSpec,
        .definition "OfNat.ofNat" ["u"] ofNatAccessorType ofNatAccessorValue,
        .definition "instOfNatNat" [] instOfNatNatType instOfNatNatValue
      ])
  let ofNatReduced ← expectOkLabel "OfNat.ofNat projection reduction"
    (normalize MPC.Configs.LeanCore429 ofNatEnv [] ofNatZeroExpr)
  expectExprEq "OfNat.ofNat value" ofNatReduced (.lit (.nat 0))

def checkMutualInductives : IO Unit := do
  let manifest := { MPC.Configs.Poc with inductiveBlocks := .mutual }
  expectError "mutual inductive blocks disabled"
    (replay MPC.Configs.Poc emptyEnv
      (baseDeclarations ++ [.inductiveBlock mutEvenOddBlock]))
  let env ← expectOkLabel "mutual even/odd replay"
    (replay manifest emptyEnv (baseDeclarations ++ [.inductiveBlock mutEvenOddBlock]))
  expectEnvContains "mutual even recursor" env "MutEven.rec"
  expectEnvContains "mutual odd recursor" env "MutOdd.rec"
  expectError "negative mutual occurrence"
    (replay manifest emptyEnv (baseDeclarations ++ [.inductiveBlock badMutualBlock]))
  let evenMotive := .lam "target" (.const "MutEven" []) (.const "P" [])
  let oddMotive := .lam "target" (.const "MutOdd" []) (.const "P" [])
  let zeroMinor := .const "p" []
  let succOddMinor :=
    .lam "pred" (.const "MutOdd" [])
      (.lam "ih" (.const "P" []) (.bvar 0))
  let succEvenMinor :=
    .lam "pred" (.const "MutEven" [])
      (.lam "ih" (.const "P" []) (.bvar 0))
  let oddOne := .app (.const "MutOdd.succEven" []) (.const "MutEven.zero" [])
  let evenTwo := .app (.const "MutEven.succOdd" []) oddOne
  let recursor :=
    appN
      (.const "MutEven.rec" [.zero])
      [
        evenMotive,
        oddMotive,
        zeroMinor,
        succOddMinor,
        succEvenMinor,
        evenTwo
      ]
  let reduced ← expectOkLabel "mutual recursor reduction"
    (normalize manifest env [] recursor)
  expectExprEq "mutual recursor iota" reduced (.const "p" [])

def checkPropInductives : IO Unit := do
  expectError "Prop inductive package requires Prop"
    (replay { MPC.Configs.InductivePropPoc with prop := .disabled } emptyEnv
      (baseDeclarations ++ [.inductive propInductiveSpec]))
  let env ← expectOkLabel "Prop inductive replay"
    (replay MPC.Configs.InductivePropPoc emptyEnv (baseDeclarations ++ [.inductive propInductiveSpec]))
  expectEnvContains "Prop inductive constructor" env "PropOnly.intro"
  expectEnvContains "Prop inductive recursor" env "PropOnly.rec"
  let recursorType ← expectOkLabel "Prop inductive recursor inference"
    (infer MPC.Configs.InductivePropPoc env [] [] (.const "PropOnly.rec" []))
  expectExprEq "Prop inductive recursor type" recursorType propOnlyRecursorType
  let motive := .lam "x" (.const "PropOnly" []) (.const "P" [])
  let recursor :=
    appN
      (.const "PropOnly.rec" [])
      [
        motive,
        .const "p" [],
        .const "PropOnly.intro" []
      ]
  let reduced ← expectOkLabel "Prop inductive recursor reduction"
    (normalize MPC.Configs.InductivePropPoc env [] recursor)
  expectExprEq "Prop inductive recursor value" reduced (.const "p" [])
  let largePropManifest := { MPC.Configs.InductivePropPoc with inductiveProp := .largeElim }
  let propChoiceEnv ← expectOkLabel "multi-constructor Prop replay"
    (replay largePropManifest emptyEnv (baseDeclarations ++ [.inductive propChoiceSpec]))
  let _propChoiceRecursor ← expectOkLabel "multi-constructor Prop recursor level arity"
    (infer largePropManifest propChoiceEnv [] [] (.const "PropChoice.rec" []))
  expectError "multi-constructor Prop recursor rejects large elimination level"
    (infer largePropManifest propChoiceEnv [] [] (.const "PropChoice.rec" [.zero]))

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

def checkIndexedPropInductives : IO Unit := do
  let env ← expectOkLabel "indexed Prop replay"
    (replay MPC.Configs.IndexedPropPoc emptyEnv (baseDeclarations ++ [.indexedInductive propIndexedSpec]))
  expectEnvContains "indexed Prop inductive constructor" env "PropVec.nil"
  expectEnvContains "indexed Prop inductive recursor" env "PropVec.rec"
  let _recursorType ← expectOkLabel "indexed Prop recursor inference"
    (infer MPC.Configs.IndexedPropPoc env [] [] (.const "PropVec.rec" []))
  let motive :=
    .lam "n" natType
      (.lam "target" (propVecType (.bvar 0)) (.const "P" []))
  let nilTarget := appN (.const "PropVec.nil" []) [natType]
  let recursor :=
    appN
      (.const "PropVec.rec" [])
      [
        natType,
        motive,
        .const "p" [],
        natZero,
        nilTarget
      ]
  let reduced ← expectOkLabel "indexed Prop recursor reduction"
    (normalize MPC.Configs.IndexedPropPoc env [] recursor)
  expectExprEq "indexed Prop recursor value" reduced (.const "p" [])

def checkIndexedRecursiveProofFields : IO Unit := do
  let env ← expectOkLabel "Reach replay"
    (replay MPC.Configs.IndexedPropPoc emptyEnv
      (baseDeclarations ++ reachPreDeclarations ++ [.indexedInductive reachSpec] ++ reachPostDeclarations))
  expectEnvContains "Reach constructor" env "Reach.intro"
  expectEnvContains "Reach recursor" env "Reach.rec"
  let _recursorType ← expectOkLabel "Reach recursor inference"
    (infer MPC.Configs.IndexedPropPoc env [] [] (.const "Reach.rec" []))
  let reduced ← expectOkLabel "Reach recursor reduction"
    (normalize MPC.Configs.IndexedPropPoc env [] reachRecursorOnTarget)
  expectExprEq "Reach recursive proof-field value" reduced reachExpectedReduction

def checkPropLargeElimination : IO Unit := do
  let sameEnv ← expectOkLabel "fresh recursor universe replay"
    (replay MPC.Configs.IndexedPropLargeElimPoc emptyEnv [.indexedInductive sameSpec])
  match sameEnv.find? "Same.rec" with
  | some info => expect "fresh recursor universe" (info.levelParams == ["u_1", "u"])
  | none => throw <| IO.userError "fresh recursor universe: missing Same.rec"
  let env ← expectOkLabel "Reach large-elimination replay"
    (replay MPC.Configs.IndexedPropLargeElimPoc emptyEnv
      (baseDeclarations ++ reachPreDeclarations ++ [.indexedInductive reachSpec] ++ reachPostDeclarations))
  let _recursorType ← expectOkLabel "Reach large-elimination recursor inference"
    (infer MPC.Configs.IndexedPropLargeElimPoc env [] [] (.const "Reach.rec" [.succ .zero]))
  let reduced ← expectOkLabel "Reach large-elimination reduction"
    (normalize MPC.Configs.IndexedPropLargeElimPoc env [] reachLargeRecursorOnTarget)
  expectExprEq "Reach large-elimination value" reduced natZero

def checkEquality : IO Unit := do
  expectError "equality primitives disabled"
    (replay MPC.Configs.Poc emptyEnv [.equalityPrimitives])
  expectError "duplicate equality primitives"
    (replay MPC.Configs.EqualityPoc emptyEnv [.equalityPrimitives, .equalityPrimitives])
  let env ← expectOkLabel "equality replay"
    (replay MPC.Configs.EqualityPoc emptyEnv
      (baseDeclarations ++
        [.equalityPrimitives] ++
        [MPC.Packages.Equality.eqNdRecDefinition] ++
        equalityDeclarations ++
        equalityEndpointProofDeclarations ++
        [.axiom "aEqA" [] (eqAlpha (.const "a" []) (.const "a" []))]))
  expectEnvContains "equality primitives" env "Eq.rec"
  expect "Eq proof type metadata"
    (env.knownPropType (eqAlpha (.const "a" []) (.const "a" [])))
  expect "underapplied Eq metadata" (!env.knownPropType (.const "Eq" [.succ .zero]))
  expectOkLabel "proof irrelevance"
    (defEq MPC.Configs.EqualityPoc env [] [] (.const "p" []) (.const "q" []))
  expectError "sort mismatch conversion terminates"
    (defEq MPC.Configs.EqualityPoc env [] [] propType type0)
  let inferred ← expectOkLabel "Eq.rec inference"
    (infer MPC.Configs.EqualityPoc env [] [] eqRecTransport)
  let inferred ← expectOkLabel "Eq.rec inferred type normalization"
    (normalize MPC.Configs.EqualityPoc env [] inferred)
  expectExprEq "Eq.rec type" inferred predA
  let reduced ← expectOkLabel "Eq.rec reduction"
    (normalize MPC.Configs.EqualityPoc env [] eqRecTransport)
  expectExprEq "Eq.rec value" reduced (.const "predProof" [])
  let kReduced ← expectOkLabel "Eq.rec K reduction"
    (normalize MPC.Configs.EqualityPoc env [] eqRecKTransport)
  expectExprEq "Eq.rec K value" kReduced (.const "predProof" [])
  let nestedEndpointReduced ← expectOkLabel "Eq.rec nested endpoint reduction"
    (normalize MPC.Configs.EqualityPoc env [] eqRecNestedEndpointTransport)
  expectExprEq "Eq.rec nested endpoint value" nestedEndpointReduced (.const "famValue" [])
  let proofBoxEnv ← expectOkLabel "Eq.rec proof endpoint replay"
    (replay MPC.Configs.EqualityPoc env
      [.inductive proofBoxSpec, .axiom "proofBoxEq" [] proofBoxEqType])
  match proofBoxEnv.findConstructorFieldInfo? "ProofBox.mk" with
  | some info => expect "ProofBox proof field metadata" (info.proofFields == [false, true])
  | none => throw <| IO.userError "ProofBox proof field metadata: missing"
  expectOkLabel "constructor proof-field conversion"
    (defEq MPC.Configs.EqualityPoc proofBoxEnv [] [] proofBoxP proofBoxQ)
  expectOkLabel "Eq.rec proof endpoint K conversion"
    (defEq MPC.Configs.EqualityPoc proofBoxEnv [] [] proofBoxEqRecTransport (.const "b" []))
  let ndInferred ← expectOkLabel "Eq.ndrec inference"
    (infer MPC.Configs.EqualityPoc env [] [] eqNdRecTransport)
  let ndInferred ← expectOkLabel "Eq.ndrec inferred type normalization"
    (normalize MPC.Configs.EqualityPoc env [] ndInferred)
  expectExprEq "Eq.ndrec type" ndInferred betaType
  let ndReduced ← expectOkLabel "Eq.ndrec reduction"
    (normalize MPC.Configs.EqualityPoc env [] eqNdRecTransport)
  expectExprEq "Eq.ndrec value" ndReduced (.const "b" [])
  let _eqSymmEnv ← expectOkLabel "Eq.rec Prop motive replay"
    (replay MPC.Configs.EqualityPoc env [.theorem "Alpha.eqSymm" [] eqSymmType eqSymmValue])

def checkSingletonInductives : IO Unit := do
  let declarations :=
    baseDeclarations ++
      [
        .inductive unitLikeSpec,
        .axiom "unitLikeA" [] (.const "UnitLike" []),
        .axiom "unitLikeB" [] (.const "UnitLike" []),
        .inductive phantomSpec,
        .axiom "phantomA" [] (.app (.const "Phantom" []) natType),
        .axiom "phantomB" [] (.app (.const "Phantom" []) natType),
        .inductive unitBoxSpec,
        .axiom "unitBoxA" [] (.const "UnitBox" []),
        .axiom "unitBoxB" [] (.const "UnitBox" [])
      ]
  let env ← expectOkLabel "singleton inductive replay"
    (replay MPC.Configs.Poc emptyEnv declarations)
  expectOkLabel "singleton inductive conversion"
    (defEq MPC.Configs.Poc env [] []
      (.const "unitLikeA" []) (.const "unitLikeB" []))
  expectOkLabel "parameterized singleton inductive conversion"
    (defEq MPC.Configs.Poc env [] []
      (.const "phantomA" []) (.const "phantomB" []))
  expectError "singleton conversion does not imply structure eta"
    (defEq MPC.Configs.Poc env [] []
      (.const "unitBoxA" []) (.const "unitBoxB" []))

def checkProjections : IO Unit := do
  let declarations :=
    baseDeclarations ++ equalityDeclarations ++
      [
        .inductive dPairSpec,
        .axiom "dPairStuck" [] dPairType
      ]
  let baseEnv ← expectOkLabel "projection baseline replay"
    (replay MPC.Configs.Poc emptyEnv declarations)
  expectError "projection disabled"
    (infer MPC.Configs.Poc baseEnv [] [] dPairFst)
  let etaDisabled ← expectOkLabel "structure recursor eta disabled"
    (normalize MPC.Configs.Poc baseEnv [] dPairRecFstEta)
  expectExprEq "structure recursor eta disabled value" etaDisabled dPairRecFstEta
  expectError "structure eta disabled"
    (defEq MPC.Configs.Poc baseEnv [] [] dPairEtaConstructor dPairStuckTarget)
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
  let fstEtaType ← expectOkLabel "first structure recursor eta inference"
    (infer MPC.Configs.ProjectionPoc env [] [] dPairRecFstEta)
  let fstEtaType ← expectOkLabel "first structure recursor eta type normalization"
    (normalize MPC.Configs.ProjectionPoc env [] fstEtaType)
  expectExprEq "first structure recursor eta type" fstEtaType alphaType
  let fstEtaReduced ← expectOkLabel "first structure recursor eta reduction"
    (normalize MPC.Configs.ProjectionPoc env [] dPairRecFstEta)
  expectExprEq "first structure recursor eta value" fstEtaReduced dPairStuckFst
  let sndEtaType ← expectOkLabel "second structure recursor eta inference"
    (infer MPC.Configs.ProjectionPoc env [] [] dPairRecSndEta)
  let sndEtaType ← expectOkLabel "second structure recursor eta type normalization"
    (normalize MPC.Configs.ProjectionPoc env [] sndEtaType)
  expectExprEq "second structure recursor eta type" sndEtaType (.app (.const "Pred" []) dPairStuckFst)
  let sndEtaReduced ← expectOkLabel "second structure recursor eta reduction"
    (normalize MPC.Configs.ProjectionPoc env [] dPairRecSndEta)
  expectExprEq "second structure recursor eta value" sndEtaReduced dPairStuckSnd
  expectOkLabel "structure recursor eta conversion"
    (defEq MPC.Configs.ProjectionPoc env [] [] dPairRecSndEta dPairStuckSnd)
  expectOkLabel "structure eta constructor left"
    (defEq MPC.Configs.ProjectionPoc env [] [] dPairEtaConstructor dPairStuckTarget)
  expectOkLabel "structure eta constructor right"
    (defEq MPC.Configs.ProjectionPoc env [] [] dPairStuckTarget dPairEtaConstructor)
  expectError "projection field out of range"
    (infer MPC.Configs.ProjectionPoc env [] [] (.proj "DPair" 2 dPairTarget))
  let hAddLikeDeclarations :=
    [
      .axiom "Alpha" [] type0,
      .inductive hAddLikeSpec,
      .definition "HAddLike.hAdd" ["u", "v", "w"]
        hAddLikeAccessorType hAddLikeAccessorValue,
      .axiom "hAddFn" [] (pi "x" alphaType (pi "y" alphaType alphaType))
    ]
  let hAddLikeEnv ← expectOkLabel "dependent projection with binders replay"
    (replay MPC.Configs.ProjectionPoc emptyEnv hAddLikeDeclarations)
  expectEnvContains "dependent projection accessor" hAddLikeEnv "HAddLike.hAdd"
  let hAddLikeLevels := [.succ .zero, .succ .zero, .succ .zero]
  let hAddLikeSelf :=
    appN (.const "HAddLike.mk" hAddLikeLevels)
      [alphaType, alphaType, alphaType, .const "hAddFn" []]
  let hAddLikeProjected :=
    appN (.const "HAddLike.hAdd" hAddLikeLevels)
      [alphaType, alphaType, alphaType, hAddLikeSelf]
  let hAddLikeReduced ← expectOkLabel "projection constant reduction"
    (normalize MPC.Configs.ProjectionPoc hAddLikeEnv [] hAddLikeProjected)
  expectExprEq "projection constant value" hAddLikeReduced (.const "hAddFn" [])
  let universeFieldEnv ← expectOkLabel "projection universe substitution replay"
    (replay MPC.Configs.ProjectionPoc emptyEnv (baseDeclarations ++ [.inductive universeFieldSpec]))
  let universeFieldType ← expectOkLabel "projection universe substitution inference"
    (infer MPC.Configs.ProjectionPoc universeFieldEnv [] [] universeFieldProjection)
  expectExprEq "projection universe substitution type" universeFieldType propType

def checkPrimitiveNat : IO Unit := do
  let declarations := baseDeclarations ++ primitiveNatDeclarations
  let baseEnv ← expectOkLabel "primitive Nat baseline replay"
    (replay MPC.Configs.Poc emptyEnv declarations)
  let addBase ← expectOkLabel "primitive Nat disabled delta"
    (normalize MPC.Configs.Poc baseEnv [] (appN (.const "Nat.add" []) [.const "m" [], natZero]))
  expectExprEq "primitive Nat disabled uses transparent value" addBase natZero
  let env ← expectOkLabel "primitive Nat replay"
    (replay MPC.Configs.PrimitiveNatPoc emptyEnv declarations)
  let addZero ← expectOkLabel "Nat.add zero reduction"
    (normalize MPC.Configs.PrimitiveNatPoc env [] (appN (.const "Nat.add" []) [.const "m" [], natZero]))
  expectExprEq "Nat.add zero value" addZero (.const "m" [])
  let addOne ← expectOkLabel "Nat.add one reduction"
    (normalize MPC.Configs.PrimitiveNatPoc env [] (appN (.const "Nat.add" []) [.const "m" [], .lit (.nat 1)]))
  expectExprEq "Nat.add one value" addOne (natSucc (.const "m" []))
  expectOkLabel "Nat.add conversion"
    (defEq MPC.Configs.PrimitiveNatPoc env [] [] (appN (.const "Nat.add" []) [.const "m" [], .lit (.nat 1)]) (natSucc (.const "m" [])))
  let addCongruenceLeft :=
    appN (.const "Nat.add" []) [appN (.const "Nat.add" []) [.const "m" [], natZero], .const "m" []]
  let addCongruenceRight :=
    appN (.const "Nat.add" []) [.const "m" [], .const "m" []]
  let addCongruence? ← expectOkLabel "same constant application congruence"
    (constAppCongruence? MPC.Configs.PrimitiveNatPoc env [] [] addCongruenceLeft addCongruenceRight)
  expect "same constant application congruence succeeds" addCongruence?.isSome
  let mulValue ← expectOkLabel "Nat.mul primitive reduction"
    (normalize MPC.Configs.PrimitiveNatPoc env [] (appN (.const "Nat.mul" []) [.lit (.nat 65536), .lit (.nat 65536)]))
  expectExprEq "Nat.mul primitive value" mulValue (.lit (.nat 4294967296))
  let mulRightZero ← expectOkLabel "Nat.mul right zero primitive reduction"
    (normalize MPC.Configs.PrimitiveNatPoc env [] (appN (.const "Nat.mul" []) [.const "m" [], natZero]))
  expectExprEq "Nat.mul right zero value" mulRightZero (.lit (.nat 0))
  let powValue ← expectOkLabel "Nat.pow primitive reduction"
    (normalize MPC.Configs.PrimitiveNatPoc env [] (appN (.const "Nat.pow" []) [.lit (.nat 2), .lit (.nat 32)]))
  expectExprEq "Nat.pow primitive value" powValue (.lit (.nat 4294967296))
  let powRightZero ← expectOkLabel "Nat.pow right zero primitive reduction"
    (normalize MPC.Configs.PrimitiveNatPoc env [] (appN (.const "Nat.pow" []) [.const "m" [], natZero]))
  expectExprEq "Nat.pow right zero value" powRightZero (.lit (.nat 1))
  let subPositive ← expectOkLabel "Nat.sub positive primitive reduction"
    (normalize MPC.Configs.PrimitiveNatPoc env [] (appN (.const "Nat.sub" []) [.lit (.nat 1114112), .lit (.nat 12)]))
  expectExprEq "Nat.sub positive value" subPositive (.lit (.nat 1114100))
  let subTruncated ← expectOkLabel "Nat.sub truncated primitive reduction"
    (normalize MPC.Configs.PrimitiveNatPoc env [] (appN (.const "Nat.sub" []) [.lit (.nat 12), .lit (.nat 1114112)]))
  expectExprEq "Nat.sub truncated value" subTruncated (.lit (.nat 0))
  let subRightZero ← expectOkLabel "Nat.sub right zero primitive reduction"
    (normalize MPC.Configs.PrimitiveNatPoc env [] (appN (.const "Nat.sub" []) [.const "m" [], natZero]))
  expectExprEq "Nat.sub right zero value" subRightZero (.const "m" [])
  let beqTrue ← expectOkLabel "Nat.beq true primitive reduction"
    (normalize MPC.Configs.PrimitiveNatPoc env [] (appN (.const "Nat.beq" []) [.lit (.nat 9), .lit (.nat 9)]))
  expectExprEq "Nat.beq true value" beqTrue boolTrue
  let beqFalse ← expectOkLabel "Nat.beq false primitive reduction"
    (normalize MPC.Configs.PrimitiveNatPoc env [] (appN (.const "Nat.beq" []) [.lit (.nat 9), natZero]))
  expectExprEq "Nat.beq false value" beqFalse boolFalse
  let bleTrue ← expectOkLabel "Nat.ble true primitive reduction"
    (normalize MPC.Configs.PrimitiveNatPoc env [] (appN (.const "Nat.ble" []) [natZero, .lit (.nat 9)]))
  expectExprEq "Nat.ble true value" bleTrue boolTrue
  let bleFalse ← expectOkLabel "Nat.ble false primitive reduction"
    (normalize MPC.Configs.PrimitiveNatPoc env [] (appN (.const "Nat.ble" []) [.lit (.nat 9), natZero]))
  expectExprEq "Nat.ble false value" bleFalse boolFalse
  let badNatAddInfo : ConstantInfo :=
    { name := "Nat.add", levelParams := [], type := natBinaryBoolType, value? := some natBinaryBoolFalseValue, kind := .definition }
  expectError "Nat.add primitive declaration shape"
    (normalize MPC.Configs.PrimitiveNatPoc (shadowEnv env badNatAddInfo) [] (appN (.const "Nat.add" []) [natZero, natZero]))
  let badNatBeqInfo : ConstantInfo :=
    { name := "Nat.beq", levelParams := [], type := natBinaryBoolType, kind := .axiom }
  expectError "Nat.beq primitive declaration kind"
    (normalize MPC.Configs.PrimitiveNatPoc (shadowEnv env badNatBeqInfo) [] (appN (.const "Nat.beq" []) [natZero, natZero]))
  let badBoolTrueInfo : ConstantInfo :=
    { name := "Bool.true", levelParams := [], type := natType, kind := .constructor "Bool" 1 0 }
  expectError "Nat.beq primitive Bool constructor shape"
    (normalize MPC.Configs.PrimitiveNatPoc (shadowEnv env badBoolTrueInfo) [] (appN (.const "Nat.beq" []) [natZero, natZero]))

def checkFunctionEta : IO Unit := do
  let declarations := baseDeclarations ++ etaDeclarations
  let baseEnv ← expectOkLabel "function eta baseline replay"
    (replay MPC.Configs.Poc emptyEnv declarations)
  expectError "function eta disabled"
    (defEq MPC.Configs.Poc baseEnv [] [] etaExpandedF (.const "f" []))
  let etaEnv ← expectOkLabel "function eta replay"
    (replay MPC.Configs.FunctionEtaPoc emptyEnv declarations)
  expectOkLabel "function eta lambda left"
    (defEq MPC.Configs.FunctionEtaPoc etaEnv [] [] etaExpandedF (.const "f" []))
  expectOkLabel "function eta lambda right"
    (defEq MPC.Configs.FunctionEtaPoc etaEnv [] [] (.const "f" []) etaExpandedF)
  let etaDefinitionEnv ← expectOkLabel "function eta definition replay"
    (addDecl MPC.Configs.FunctionEtaPoc etaEnv
      (.definition "etaSource" [] (pi "x" natType natType) etaExpandedF))
  expectOkLabel "function eta unfolds definition"
    (defEq MPC.Configs.FunctionEtaPoc etaDefinitionEnv [] []
      (.const "etaSource" []) (.const "f" []))
  let primitiveEtaManifest := { MPC.Configs.PrimitiveNatPoc with functionEta := .enabled }
  let primitiveEnv ← expectOkLabel "function eta primitive replay"
    (replay primitiveEtaManifest emptyEnv (baseDeclarations ++ primitiveNatDeclarations))
  expectOkLabel "function eta uses configured body conversion"
    (defEq primitiveEtaManifest primitiveEnv [] [] etaNatAddOne (.const "Nat.succ" []))

def checkUniverseComparison : IO Unit := do
  let u : Level := .param "u"
  let v : Level := .param "v"
  let one : Level := .succ .zero
  expect "universe comparison removes dominated max summands"
    (Level.defEq (.max one (.succ u)) (.succ u))
  expect "universe comparison proves imax zero equation"
    (Level.defEq (.imax .zero u) u)
  expect "universe comparison proves imax one equation"
    (Level.defEq (.imax one u) u)
  expect "universe comparison proves imax idempotence"
    (Level.defEq (.imax u u) u)
  expect "universe comparison proves unresolved imax upper bound"
    (Level.le (.imax u v) (.max u v))
  expect "universe comparison keeps unrelated parameters distinct"
    (!(Level.defEq u v))
  expect "universe comparison removes nested imax zero left sides"
    (Level.defEq
      (.imax one (.imax .zero (.imax .zero (.max one u))))
      (.imax one (.max one u)))
  expect "zero universe recognizes imax with zero right side"
    (Level.defEqZero (.imax u (.max .zero .zero)))
  expect "zero universe rejects unresolved imax right side"
    (!(Level.defEqZero (.imax u v)))
  expect "zero universe rejects positive max summand"
    (!(Level.defEqZero (.max .zero one)))

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
  let alphaRelationEnv ← expectOkLabel "quotient alpha relation replay"
    (replay MPC.Configs.QuotPoc emptyEnv
      (baseDeclarations ++ [.equalityPrimitives, .quotientPrimitives] ++
        quotientAlphaRelationDeclarations))
  let alphaRelationReduced ← expectOkLabel "quotient alpha relation reduction"
    (normalize MPC.Configs.QuotPoc alphaRelationEnv [] quotLiftAlphaRenamedRelation)
  expectExprEq "quotient alpha relation value"
    alphaRelationReduced (.app (.const "f" []) (.const "a" []))
  let transparentRelationEnv ← expectOkLabel "quotient transparent relation replay"
    (replay MPC.Configs.QuotPoc emptyEnv
      (baseDeclarations ++ [.equalityPrimitives, .quotientPrimitives] ++
        quotientTransparentRelationDeclarations))
  let transparentRelationReduced ← expectOkLabel "quotient transparent relation reduction"
    (normalize MPC.Configs.QuotPoc transparentRelationEnv [] quotLiftTransparentRelation)
  expectExprEq "quotient transparent relation value"
    transparentRelationReduced (.app (.const "f" []) (.const "a" []))
  let liftHeadEnv ← expectOkLabel "quotient lifted head replay"
    (replay MPC.Configs.QuotPoc emptyEnv
      (baseDeclarations ++ [.equalityPrimitives, .quotientPrimitives] ++
        quotientLiftHeadDefinitionDeclarations))
  let liftHeadReduced ← expectOkLabel "quotient lifted head reduction"
    (normalize MPC.Configs.QuotPoc liftHeadEnv [] quotLiftViaDefinition)
  expectExprEq "quotient lifted head value"
    liftHeadReduced (.app (.const "f" []) (.const "a" []))

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

def checkSHA256 : IO Unit := do
  expect "SHA-256 empty string"
    (MPC.Adapters.SHA256.hashString "" ==
      "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
  expect "SHA-256 abc"
    (MPC.Adapters.SHA256.hashString "abc" ==
      "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")

def alphaLayerTheoremType (name : Name) : Expr :=
  pi name natType (.const "P" [])

def alphaLayerTheoremValue (name : Name) : Expr :=
  .lam name natType (.const "p" [])

def checkLayerAlphaReuse : IO Unit := do
  let first :=
    .theorem "alphaLayerTheorem" []
      (alphaLayerTheoremType "x")
      (alphaLayerTheoremValue "x")
  let second :=
    .theorem "alphaLayerTheorem" []
      (alphaLayerTheoremType "y")
      (alphaLayerTheoremValue "z")
  let declarations := baseDeclarations ++ [first]
  let layer ← expectOkLabel "checked layer build"
    (MPC.Adapters.Layer.build MPC.Configs.Poc { declarations, audit := {} })
  let summary ← expectOkLabel "checked layer alpha replay"
    (MPC.Adapters.Layer.replay MPC.Configs.Poc layer {} (baseDeclarations ++ [second]))
  expect "checked layer alpha reuse count" (summary.reused == declarations.length)
  expect "checked layer alpha checked count" (summary.checked == 0)

def alphaLayerInductiveSpec (paramName fieldName : Name) : SimpleInductiveSpec :=
  {
    name := "AlphaLayerBox"
    params := [{ name := paramName, type := type0 }]
    resultLevel := .succ .zero
    constructors :=
      [
        {
          name := "AlphaLayerBox.mk"
          fields := [{ name := fieldName, type := .bvar 0 }]
        }
      ]
  }

def checkLayerInductiveAlphaReuse : IO Unit := do
  let first := .inductive (alphaLayerInductiveSpec "α" "value")
  let second := .inductive (alphaLayerInductiveSpec "β" "item")
  let declarations := baseDeclarations ++ [first]
  let layer ← expectOkLabel "checked layer inductive build"
    (MPC.Adapters.Layer.build MPC.Configs.Poc { declarations, audit := {} })
  let summary ← expectOkLabel "checked layer inductive alpha replay"
    (MPC.Adapters.Layer.replay MPC.Configs.Poc layer {} (baseDeclarations ++ [second]))
  expect "checked layer inductive alpha reuse count" (summary.reused == declarations.length)
  expect "checked layer inductive alpha checked count" (summary.checked == 0)

def checkSqliteOnDemandLayerReuse : IO Unit :=
  IO.FS.withTempDir fun dir => do
    let path := dir / "layer.db"
    let first :=
      .theorem "sqliteLayerTheorem" []
        (alphaLayerTheoremType "x")
        (alphaLayerTheoremValue "x")
    let second :=
      .theorem "sqliteLayerTheorem" []
        (alphaLayerTheoremType "y")
        (alphaLayerTheoremValue "z")
    let declarations := baseDeclarations ++ [first]
    let summary1 ← expectOkLabel "SQLite on-demand layer first replay"
      (← MPC.Adapters.Layer.cacheSqlite MPC.Configs.Poc path {} declarations)
    expect "SQLite on-demand first replay reused count" (summary1.reused == 0)
    expect "SQLite on-demand first replay checked count" (summary1.checked == declarations.length)
    let version ← expectOkLabel "SQLite on-demand layer version"
      (← MPC.Adapters.Layer.sqliteLayerFormatVersion path)
    expect "SQLite on-demand layer format version"
      (version == MPC.Adapters.Layer.sqliteOnDemandFormatVersion)
    let summary2 ← expectOkLabel "SQLite on-demand layer exact second replay"
      (← MPC.Adapters.Layer.cacheSqlite MPC.Configs.Poc path {} declarations)
    expect "SQLite on-demand exact second replay reused count"
      (summary2.reused == declarations.length)
    expect "SQLite on-demand second replay checked count" (summary2.checked == 0)
    let summary3 ← expectOkLabel "SQLite on-demand layer alpha replay"
      (← MPC.Adapters.Layer.cacheSqlite MPC.Configs.Poc path {} (baseDeclarations ++ [second]))
    expect "SQLite on-demand alpha replay reused count"
      (summary3.reused == baseDeclarations.length)
    expect "SQLite on-demand alpha replay checked count" (summary3.checked == 1)

def checkSqliteLayerMigration : IO Unit :=
  IO.FS.withTempDir fun dir => do
    let source := dir / "layer-v2.db"
    let target := dir / "layer-v4.db"
    let theoremDecl :=
      .theorem "sqliteMigratedTheorem" []
        (alphaLayerTheoremType "x")
        (alphaLayerTheoremValue "x")
    let declarations := baseDeclarations ++ [theoremDecl]
    let layer ← expectOkLabel "SQLite v2 migration source build"
      (MPC.Adapters.Layer.build MPC.Configs.Poc { declarations, audit := {} })
    expectOkLabel "SQLite v2 migration source save"
      (← MPC.Adapters.Layer.saveSqliteFromLayer source layer)
    let summary ← expectOkLabel "SQLite v2 migration"
      (← MPC.Adapters.Layer.migrateSqliteToOnDemand source target)
    expect "SQLite v2 migration declaration count" (summary.declarations == declarations.length)
    let replaySummary ← expectOkLabel "SQLite v2 migrated replay"
      (← MPC.Adapters.Layer.replaySqlite MPC.Configs.Poc target {} declarations)
    expect "SQLite v2 migrated replay reused count"
      (replaySummary.reused == declarations.length)
    expect "SQLite v2 migrated replay checked count" (replaySummary.checked == 0)

def checkExportNameEncoding : IO Unit := do
  let singleComponent := Lean.Name.str Lean.Name.anonymous "a.b"
  let dotted := Lean.Name.str (Lean.Name.str Lean.Name.anonymous "a") "b"
  let reserved := Lean.Name.str Lean.Name.anonymous "__mpc_name:reserved"
  expect "export name encoding distinguishes dotted spelling"
    (MPC.Adapters.Export.localName singleComponent != MPC.Adapters.Export.localName dotted)
  expect "export name encoding keeps ordinary dotted name"
    (MPC.Adapters.Export.localName dotted == "a.b")
  expect "export name encoding protects reserved prefix"
    ((MPC.Adapters.Export.localName reserved).startsWith MPC.Adapters.Export.encodedNamePrefix)

def main : IO Unit := do
  checkUniverseComparison
  checkBasePackages
  checkSimpleInductives
  checkMutualInductives
  checkPropInductives
  checkSingletonInductives
  checkIndexedInductives
  checkIndexedPropInductives
  checkIndexedRecursiveProofFields
  checkPropLargeElimination
  checkEquality
  checkProjections
  checkPrimitiveNat
  checkFunctionEta
  checkQuotients
  checkAdapters
  checkSHA256
  checkExportNameEncoding
  checkLayerAlphaReuse
  checkLayerInductiveAlphaReuse
  checkSqliteOnDemandLayerReuse
  checkSqliteLayerMigration
