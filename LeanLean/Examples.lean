import LeanLean.Kernel

namespace LeanLean

def const0 (name : Name) : Expr :=
  .const name []

def propLevel : Level :=
  0

def type0Level : Level :=
  1

def type1Level : Level :=
  2

def type2Level : Level :=
  3

def type0Param : Level :=
  0

def type1Param : Level :=
  1

def typeLevel (level : Level) : Level :=
  .succ level

def type0Sort : Expr :=
  .sort type0Level

def type1Sort : Expr :=
  .sort type1Level

def propSort : Expr :=
  .sort propLevel

def recConstAt (level : Level) (name : Name) : Expr :=
  .const name [level]

def recConst (name : Name) : Expr :=
  recConstAt type0Level name

def boolType : Expr :=
  const0 "Bool"

def natType : Expr :=
  const0 "Nat"

def listType (elem : Expr) : Expr :=
  Expr.mkApps (const0 "List") [elem]

def boolSpec : InductiveSpec :=
  {
    name := "Bool"
    params := []
    level := type0Level
    ctors :=
      [
        { name := "Bool.false", fields := [] },
        { name := "Bool.true", fields := [] }
      ]
  }

def natSpec : InductiveSpec :=
  {
    name := "Nat"
    params := []
    level := type0Level
    ctors :=
      [
        { name := "Nat.zero", fields := [] },
        { name := "Nat.succ", fields := [{ name := "n", type := const0 "Nat" }] }
      ]
  }

def listSpec : InductiveSpec :=
  {
    name := "List"
    params := [{ name := "α", type := type0Sort }]
    level := type0Level
    ctors :=
      [
        { name := "List.nil", fields := [] },
        {
          name := "List.cons"
          fields :=
            [
              { name := "head", type := .bvar 0 },
              { name := "tail", type := Expr.mkApps (const0 "List") [.bvar 1] }
            ]
        }
      ]
  }

def pairSpec : InductiveSpec :=
  {
    name := "Pair"
    params := []
    level := type0Level
    ctors :=
      [
        {
          name := "Pair.mk"
          fields :=
            [
              { name := "fst", type := natType },
              { name := "snd", type := boolType }
            ]
        }
      ]
  }

def sigmaBoxSpec : InductiveSpec :=
  {
    name := "SigmaBox"
    params := []
    level := type1Level
    ctors :=
      [
        {
          name := "SigmaBox.mk"
          fields :=
            [
              { name := "α", type := type0Sort },
              { name := "value", type := .bvar 0 }
            ]
        }
      ]
  }

def vec1Spec : InductiveSpec :=
  {
    name := "Vec1"
    params := [{ name := "α", type := type0Sort }]
    indices := [{ name := "n", type := natType }]
    level := type0Level
    ctors :=
      [
        {
          name := "Vec1.mk"
          fields :=
            [
              { name := "n", type := natType },
              { name := "value", type := .bvar 1 }
            ]
          target? := some (Expr.mkApps (const0 "Vec1") [.bvar 2, .bvar 1])
        }
      ]
  }

def shiftedStructSpec : InductiveSpec :=
  {
    name := "ShiftedStruct"
    params := [{ name := "α", type := type0Sort }]
    indices := [{ name := "n", type := natType }]
    level := type0Level
    ctors :=
      [
        {
          name := "ShiftedStruct.mk"
          fields :=
            [
              { name := "n", type := natType },
              { name := "value", type := .bvar 1 }
            ]
          target? :=
            some
              (Expr.mkApps
                (const0 "ShiftedStruct")
                [.bvar 2, Expr.mkApps (const0 "Nat.succ") [.bvar 1]])
        }
      ]
  }

def eqSpec : InductiveSpec :=
  {
    name := "Eq"
    levelParams := ["u"]
    params :=
      [
        { name := "α", type := .sort (.param "u") },
        { name := "lhs", type := .bvar 0 }
      ]
    indices := [{ name := "rhs", type := .bvar 1 }]
    level := propLevel
    ctors :=
      [
        {
          name := "Eq.refl"
          fields := []
          target? := some (Expr.mkApps (.const "Eq" [.param "u"]) [.bvar 1, .bvar 0, .bvar 0])
        }
      ]
  }

def vecSpec : InductiveSpec :=
  {
    name := "Vec"
    params := [{ name := "α", type := type0Sort }]
    indices := [{ name := "n", type := natType }]
    level := type0Level
    ctors :=
      [
        {
          name := "Vec.nil"
          fields := []
          target? := some (Expr.mkApps (const0 "Vec") [.bvar 0, const0 "Nat.zero"])
        },
        {
          name := "Vec.cons"
          fields :=
            [
              { name := "n", type := natType },
              { name := "head", type := .bvar 1 },
              { name := "tail", type := Expr.mkApps (const0 "Vec") [.bvar 2, .bvar 1] }
            ]
          target? :=
            some
              (Expr.mkApps
                (const0 "Vec")
                [.bvar 3, Expr.mkApps (const0 "Nat.succ") [.bvar 2]])
        }
      ]
  }

def heightTreeSpec : InductiveSpec :=
  {
    name := "HeightTree"
    params := []
    indices := [{ name := "height", type := natType }]
    level := type0Level
    ctors :=
      [
        {
          name := "HeightTree.leaf"
          fields := []
          target? := some (Expr.mkApps (const0 "HeightTree") [const0 "Nat.zero"])
        },
        {
          name := "HeightTree.node"
          fields :=
            [
              { name := "height", type := natType },
              { name := "child", type := Expr.mkApps (const0 "HeightTree") [.bvar 0] }
            ]
          target? :=
            some
              (Expr.mkApps
                (const0 "HeightTree")
                [Expr.mkApps (const0 "Nat.succ") [.bvar 1]])
        }
      ]
  }

def sortBoxSpec : InductiveSpec :=
  {
    name := "SortBox"
    params := []
    level := type1Level
    ctors :=
      [
        { name := "SortBox.mk", fields := [{ name := "α", type := type0Sort }] }
      ]
  }

def spuriousSpec : InductiveSpec :=
  {
    name := "Spurious"
    params := [{ name := "α", type := .sort type2Level }]
    level := type0Level
    ctors := []
  }

def badSpuriousSpec : InductiveSpec :=
  {
    name := "BadSpurious"
    params := [{ name := "α", type := .sort type2Level }]
    level := type0Level
    ctors :=
      [
        { name := "BadSpurious.mk", fields := [{ name := "x", type := .bvar 0 }] }
      ]
  }

def lowSortBoxSpec : InductiveSpec :=
  {
    name := "LowSortBox"
    params := []
    level := type0Level
    ctors :=
      [
        { name := "LowSortBox.mk", fields := [{ name := "α", type := type0Sort }] }
      ]
  }

def badParamSpec : InductiveSpec :=
  {
    name := "BadParam"
    params := [{ name := "α", type := type0Sort }]
    level := type0Level
    ctors :=
      [
        {
          name := "BadParam.mk"
          fields := [{ name := "f", type := .forallE "x" (.bvar 0) natType }]
        }
      ]
  }

def badWrapSpec : InductiveSpec :=
  {
    name := "BadWrap"
    params := []
    level := type0Level
    ctors :=
      [
        {
          name := "BadWrap.mk"
          fields := [{ name := "x", type := Expr.mkApps (const0 "BadParam") [const0 "BadWrap"] }]
        }
      ]
  }

def natListTreeSpec : InductiveSpec :=
  {
    name := "NatListTree"
    params := []
    level := type0Level
    ctors :=
      [
        { name := "NatListTree.leaf", fields := [{ name := "n", type := natType }] },
        {
          name := "NatListTree.node"
          fields :=
            [{ name := "children", type := Expr.mkApps (const0 "List") [const0 "NatListTree"] }]
        }
      ]
  }

def letTreeSpec : InductiveSpec :=
  {
    name := "LetTree"
    params := []
    level := type0Level
    ctors :=
      [
        { name := "LetTree.leaf", fields := [{ name := "n", type := natType }] },
        {
          name := "LetTree.node"
          fields :=
            [
              {
                name := "children"
                type := .letE "T" type0Sort (const0 "LetTree") (Expr.mkApps (const0 "List") [.bvar 0])
              }
            ]
        }
      ]
  }

def harmlessWrapSpec : InductiveSpec :=
  {
    name := "HarmlessWrap"
    params := [{ name := "α", type := type0Sort }]
    level := type0Level
    ctors :=
      [
        {
          name := "HarmlessWrap.mk"
          fields := [{ name := "x", type := .letE "y" type0Sort (.bvar 0) natType }]
        }
      ]
  }

def nestThroughHarmlessWrapSpec : InductiveSpec :=
  {
    name := "NestThroughHarmlessWrap"
    params := []
    level := type0Level
    ctors :=
      [
        {
          name := "NestThroughHarmlessWrap.mk"
          fields :=
            [{ name := "x", type := Expr.mkApps (const0 "HarmlessWrap") [const0 "NestThroughHarmlessWrap"] }]
        }
      ]
  }

def harmlessBadParamSpec : InductiveSpec :=
  {
    name := "HarmlessBadParam"
    params := []
    level := type0Level
    ctors :=
      [
        {
          name := "HarmlessBadParam.mk"
          fields :=
            [
              {
                name := "x"
                type := Expr.mkApps (const0 "BadParam") [.letE "y" type0Sort (const0 "HarmlessBadParam") natType]
              }
            ]
        }
      ]
  }

def dupHelperSpec : InductiveSpec :=
  {
    name := "DupHelper"
    params := []
    level := type0Level
    ctors :=
      [
        {
          name := "DupHelper.mk"
          fields :=
            [
              { name := "a", type := Expr.mkApps (const0 "List") [const0 "DupHelper"] },
              {
                name := "b"
                type := Expr.mkApps (const0 "List") [.letE "T" type0Sort (const0 "DupHelper") (.bvar 0)]
              }
            ]
        }
      ]
  }

def wrapAtSpec : InductiveSpec :=
  {
    name := "WrapAt"
    params :=
      [
        { name := "n", type := natType },
        { name := "α", type := type0Sort }
      ]
    level := type0Level
    ctors :=
      [
        {
          name := "WrapAt.mk"
          fields := [{ name := "x", type := .bvar 0 }]
        }
      ]
  }

def depNestSpec : InductiveSpec :=
  {
    name := "DepNest"
    params := []
    level := type0Level
    ctors :=
      [
        {
          name := "DepNest.mk"
          fields :=
            [
              {
                name := "f"
                type :=
                  .forallE
                    "n"
                    natType
                    (Expr.mkApps (const0 "WrapAt") [.bvar 0, const0 "DepNest"])
              }
            ]
        }
      ]
  }

def depNestPSpec : InductiveSpec :=
  {
    name := "DepNestP"
    params := [{ name := "β", type := type0Sort }]
    level := type0Level
    ctors :=
      [
        {
          name := "DepNestP.mk"
          fields :=
            [
              {
                name := "f"
                type :=
                  .forallE
                    "n"
                    natType
                    (Expr.mkApps (const0 "WrapAt") [.bvar 0, Expr.mkApps (const0 "DepNestP") [.bvar 1]])
              }
            ]
        }
      ]
  }

def depAfterRecSpec : InductiveSpec :=
  {
    name := "DepAfterRec"
    params := []
    level := type0Level
    ctors :=
      [
        {
          name := "DepAfterRec.mk"
          fields :=
            [
              { name := "n", type := natType },
              { name := "child", type := const0 "DepAfterRec" },
              { name := "box", type := Expr.mkApps (const0 "WrapAt") [.bvar 1, boolType] }
            ]
        }
      ]
  }

def depFieldTreeSpec : InductiveSpec :=
  {
    name := "DepFieldTree"
    params := []
    level := type0Level
    ctors :=
      [
        {
          name := "DepFieldTree.mk"
          fields :=
            [
              { name := "n", type := natType },
              { name := "child", type := Expr.mkApps (const0 "WrapAt") [.bvar 0, const0 "DepFieldTree"] }
            ]
        }
      ]
  }

def badForwardFieldSpec : InductiveSpec :=
  {
    name := "BadForwardField"
    params := []
    level := type0Level
    ctors :=
      [
        {
          name := "BadForwardField.mk"
          fields := [{ name := "x", type := .bvar 0 }]
        }
      ]
  }

def badParamTargetSpec : InductiveSpec :=
  {
    name := "BadParamTarget"
    params :=
      [
        { name := "α", type := type0Sort },
        { name := "β", type := type0Sort }
      ]
    level := type0Level
    ctors :=
      [
        {
          name := "BadParamTarget.mk"
          fields := []
          target? := some (Expr.mkApps (const0 "BadParamTarget") [.bvar 0, .bvar 0])
        }
      ]
  }

def polyIdType : Expr :=
  .forallE
    "α"
    (.sort (.param "u"))
    (.forallE "x" (.bvar 0) (.bvar 1))

def polyIdValue : Expr :=
  .lam
    "α"
    (.sort (.param "u"))
    (.lam "x" (.bvar 0) (.bvar 0))

def polyBoxSpec : InductiveSpec :=
  {
    name := "PolyBox"
    levelParams := ["u"]
    params := [{ name := "α", type := .sort (typeLevel (.param "u")) }]
    level := typeLevel (.param "u")
    ctors :=
      [
        { name := "PolyBox.mk", fields := [{ name := "value", type := .bvar 0 }] }
      ]
  }

def pFalseSpec : InductiveSpec :=
  {
    name := "PFalse"
    params := []
    level := propLevel
    ctors := []
  }

def pTrueSpec : InductiveSpec :=
  {
    name := "PTrue"
    params := []
    level := propLevel
    ctors :=
      [
        { name := "PTrue.intro", fields := [] }
      ]
  }

def pOrSpec : InductiveSpec :=
  {
    name := "POr"
    params :=
      [
        { name := "a", type := propSort },
        { name := "b", type := propSort }
      ]
    level := propLevel
    ctors :=
      [
        { name := "POr.inl", fields := [{ name := "h", type := .bvar 1 }] },
        { name := "POr.inr", fields := [{ name := "h", type := .bvar 0 }] }
      ]
  }

def indexSingletonSpec : InductiveSpec :=
  {
    name := "IndexSingleton"
    params := []
    indices := [{ name := "n", type := natType }]
    level := propLevel
    ctors :=
      [
        {
          name := "IndexSingleton.mk"
          fields := [{ name := "n", type := natType }]
          target? := some (Expr.mkApps (const0 "IndexSingleton") [.bvar 0])
        }
      ]
  }

def shiftedIndexPropSpec : InductiveSpec :=
  {
    name := "ShiftedIndexProp"
    params := []
    indices := [{ name := "n", type := natType }]
    level := propLevel
    ctors :=
      [
        {
          name := "ShiftedIndexProp.mk"
          fields := [{ name := "n", type := natType }]
          target? :=
            some
              (Expr.mkApps
                (const0 "ShiftedIndexProp")
                [Expr.mkApps (const0 "Nat.succ") [.bvar 0]])
        }
      ]
  }

def dataWitnessPropSpec : InductiveSpec :=
  {
    name := "DataWitnessProp"
    params := [{ name := "α", type := type0Sort }]
    level := propLevel
    ctors :=
      [
        {
          name := "DataWitnessProp.mk"
          fields := [{ name := "value", type := .bvar 0 }]
        }
      ]
  }

def proofBoxSpec : InductiveSpec :=
  {
    name := "ProofBox"
    params := [{ name := "p", type := propSort }]
    level := propLevel
    ctors :=
      [
        { name := "ProofBox.mk", fields := [{ name := "h", type := .bvar 0 }] }
      ]
  }

def mutEvenSpec : InductiveSpec :=
  {
    name := "MutEven"
    params := []
    level := type0Level
    ctors :=
      [
        { name := "MutEven.zero", fields := [] },
        { name := "MutEven.succOdd", fields := [{ name := "pred", type := const0 "MutOdd" }] }
      ]
  }

def mutOddSpec : InductiveSpec :=
  {
    name := "MutOdd"
    params := []
    level := type0Level
    ctors :=
      [
        { name := "MutOdd.succEven", fields := [{ name := "pred", type := const0 "MutEven" }] }
      ]
  }

def mutEvenOddBlock : InductiveBlockSpec :=
  { levelParams := [], specs := [mutEvenSpec, mutOddSpec] }

def badMutAType : Expr :=
  const0 "BadMutA"

def badMutBType : Expr :=
  const0 "BadMutB"

def badMutASpec : InductiveSpec :=
  {
    name := "BadMutA"
    params := []
    level := type0Level
    ctors :=
      [
        {
          name := "BadMutA.mk"
          fields := [{ name := "f", type := .forallE "x" badMutBType natType }]
        }
      ]
  }

def badMutBSpec : InductiveSpec :=
  {
    name := "BadMutB"
    params := []
    level := type0Level
    ctors :=
      [
        { name := "BadMutB.mk", fields := [{ name := "x", type := badMutAType }] }
      ]
  }

def badMutualBlock : InductiveBlockSpec :=
  { levelParams := [], specs := [badMutASpec, badMutBSpec] }

def mutNestASpec : InductiveSpec :=
  {
    name := "MutNestA"
    params := []
    level := type0Level
    ctors :=
      [
        {
          name := "MutNestA.mk"
          fields := [{ name := "children", type := Expr.mkApps (const0 "List") [const0 "MutNestB"] }]
        }
      ]
  }

def mutNestBSpec : InductiveSpec :=
  {
    name := "MutNestB"
    params := []
    level := type0Level
    ctors :=
      [
        { name := "MutNestB.mk", fields := [{ name := "child", type := const0 "MutNestA" }] }
      ]
  }

def mutNestBlock : InductiveBlockSpec :=
  { levelParams := [], specs := [mutNestASpec, mutNestBSpec] }

def pProp : Expr :=
  const0 "P"

def pProof : Expr :=
  const0 "pProof"

def qProof : Expr :=
  const0 "qProof"

def pTheorem : Expr :=
  const0 "pTheorem"

def propSelfImpType : Expr :=
  .forallE "h" pProp pProp

def pTrueType : Expr :=
  const0 "PTrue"

def pTrueIntro : Expr :=
  const0 "PTrue.intro"

def pTrueMotive : Expr :=
  .lam "t" pTrueType pProp

def pTrueCase : Expr :=
  pProof

def pTrueRecOnIntro : Expr :=
  Expr.mkApps (.const "PTrue.rec" [propLevel]) [pTrueMotive, pTrueCase, pTrueIntro]

def pTrueBoolMotive : Expr :=
  .lam "t" pTrueType boolType

def pTrueRecToBool : Expr :=
  Expr.mkApps (.const "PTrue.rec" [type0Level]) [pTrueBoolMotive, const0 "Bool.true", pTrueIntro]

def pOrType (left right : Expr) : Expr :=
  Expr.mkApps (const0 "POr") [left, right]

def pOrInl (left right proof : Expr) : Expr :=
  Expr.mkApps (const0 "POr.inl") [left, right, proof]

def pOrBoolMotive : Expr :=
  .lam "h" (pOrType pProp pProp) boolType

def pOrRecToBool : Expr :=
  Expr.mkApps
    (const0 "POr.rec")
    [
      pProp,
      pProp,
      pOrBoolMotive,
      const0 "Bool.true",
      const0 "Bool.false",
      pOrInl pProp pProp pProof
    ]

def indexSingletonType (index : Expr) : Expr :=
  Expr.mkApps (const0 "IndexSingleton") [index]

def indexSingletonMk (index : Expr) : Expr :=
  Expr.mkApps (const0 "IndexSingleton.mk") [index]

def indexSingletonMotive : Expr :=
  .lam "n" natType (.lam "h" (indexSingletonType (.bvar 0)) natType)

def indexSingletonCase : Expr :=
  .lam "n" natType (.bvar 0)

def indexSingletonRecOnZero : Expr :=
  Expr.mkApps
    (.const "IndexSingleton.rec" [type0Level])
    [
      indexSingletonMotive,
      indexSingletonCase,
      const0 "Nat.zero",
      indexSingletonMk (const0 "Nat.zero")
    ]

def shiftedIndexPropType (index : Expr) : Expr :=
  Expr.mkApps (const0 "ShiftedIndexProp") [index]

def shiftedIndexPropMk (index : Expr) : Expr :=
  Expr.mkApps (const0 "ShiftedIndexProp.mk") [index]

def shiftedIndexPropMotive : Expr :=
  .lam "n" natType (.lam "h" (shiftedIndexPropType (.bvar 0)) boolType)

def shiftedIndexPropCase : Expr :=
  .lam "n" natType (const0 "Bool.true")

def shiftedIndexPropRecToBool : Expr :=
  let one := Expr.mkApps (const0 "Nat.succ") [const0 "Nat.zero"]
  Expr.mkApps
    (.const "ShiftedIndexProp.rec" [type0Level])
    [
      shiftedIndexPropMotive,
      shiftedIndexPropCase,
      one,
      shiftedIndexPropMk (const0 "Nat.zero")
    ]

def dataWitnessPropType (elem : Expr) : Expr :=
  Expr.mkApps (const0 "DataWitnessProp") [elem]

def dataWitnessPropMk (elem value : Expr) : Expr :=
  Expr.mkApps (const0 "DataWitnessProp.mk") [elem, value]

def dataWitnessPropMotive : Expr :=
  .lam "h" (dataWitnessPropType boolType) boolType

def dataWitnessPropCase : Expr :=
  .lam "value" boolType (const0 "Bool.true")

def dataWitnessPropRecToBool : Expr :=
  Expr.mkApps
    (.const "DataWitnessProp.rec" [type0Level])
    [
      boolType,
      dataWitnessPropMotive,
      dataWitnessPropCase,
      dataWitnessPropMk boolType (const0 "Bool.false")
    ]

def dataWitnessPropProjection : Expr :=
  .proj "DataWitnessProp" 0 (dataWitnessPropMk boolType (const0 "Bool.false"))

def proofBoxType (prop : Expr) : Expr :=
  Expr.mkApps (const0 "ProofBox") [prop]

def proofBoxMk (prop proof : Expr) : Expr :=
  Expr.mkApps (const0 "ProofBox.mk") [prop, proof]

def proofBoxProjection : Expr :=
  .proj "ProofBox" 0 (proofBoxMk pProp pProof)

def proofBoxProjectionFn : Expr :=
  Expr.mkApps (const0 "ProofBox.proof") [pProp, proofBoxMk pProp pProof]

def propDemoChecks (env : Env) : Result Unit := do
  let pTy ← infer env [] pProp
  let _ ← checkDefEq env pTy propSort
  let pProofTy ← infer env [] pProof
  let _ ← checkDefEq env pProofTy pProp
  let _ ← checkDefEq env pProof qProof
  let pTheoremTy ← infer env [] pTheorem
  let _ ← checkDefEq env pTheoremTy pProp
  let pTheoremNf ← normalize env pTheorem
  if pTheoremNf != pTheorem then
    .error s!"theorem constants should not unfold during normalization: {repr pTheoremNf}"
  else
    pure ()
  let _ ← checkDefEq env pTheorem qProof
  let propSelfImpTy ← infer env [] propSelfImpType
  let _ ← checkDefEq env propSelfImpTy propSort
  let pTrueTy ← infer env [] pTrueType
  let _ ← checkDefEq env pTrueTy propSort
  let pTrueRecTy ← infer env [] pTrueRecOnIntro
  let _ ← checkDefEq env pTrueRecTy pProp
  let pTrueRecNf ← normalize env pTrueRecOnIntro
  let _ ← checkDefEq env pTrueRecNf pProof
  let pTrueBoolTy ← infer env [] pTrueRecToBool
  let _ ← checkDefEq env pTrueBoolTy boolType
  let pTrueBoolNf ← normalize env pTrueRecToBool
  let _ ← checkDefEq env pTrueBoolNf (const0 "Bool.true")
  let indexSingletonTy ← infer env [] indexSingletonRecOnZero
  let _ ← checkDefEq env indexSingletonTy natType
  let indexSingletonNf ← normalize env indexSingletonRecOnZero
  let _ ← checkDefEq env indexSingletonNf (const0 "Nat.zero")
  match infer env [] (const0 "PTrue.rec") with
  | .ok _ => .error "PTrue.rec should require a motive universe argument"
  | .error _ => pure ()
  match infer env [] pOrRecToBool with
  | .ok _ => .error "POr.rec should reject data-valued motives"
  | .error _ => pure ()
  match infer env [] shiftedIndexPropRecToBool with
  | .ok _ => .error "ShiftedIndexProp.rec should reject data-valued motives"
  | .error _ => pure ()
  match infer env [] dataWitnessPropRecToBool with
  | .ok _ => .error "DataWitnessProp.rec should reject data-valued motives"
  | .error _ => pure ()

def sampleDeclarations : List Declaration :=
  [
    .inductive boolSpec,
    .inductive natSpec,
    .inductive listSpec,
    .inductive pairSpec,
    .projection "Pair.fst" "Pair" 0,
    .projection "Pair.snd" "Pair" 1,
    .inductive sigmaBoxSpec,
    .projection "SigmaBox.type" "SigmaBox" 0,
    .projection "SigmaBox.value" "SigmaBox" 1,
    .inductive vec1Spec,
    .projection "Vec1.value" "Vec1" 0,
    .inductive shiftedStructSpec,
    .projection "ShiftedStruct.pred" "ShiftedStruct" 0,
    .projection "ShiftedStruct.value" "ShiftedStruct" 1,
    .inductive eqSpec,
    .quotientPrimitives,
    .inductive vecSpec,
    .inductive heightTreeSpec,
    .inductive sortBoxSpec,
    .inductive spuriousSpec,
    .inductive badParamSpec,
    .inductive natListTreeSpec,
    .inductive letTreeSpec,
    .inductive polyBoxSpec,
    .inductive pFalseSpec,
    .inductive pTrueSpec,
    .inductive pOrSpec,
    .inductive indexSingletonSpec,
    .inductive shiftedIndexPropSpec,
    .inductive dataWitnessPropSpec,
    .inductive proofBoxSpec,
    .projection "ProofBox.proof" "ProofBox" 0,
    .inductiveBlock mutEvenOddBlock,
    .inductiveBlock mutNestBlock,
    .definition "one" [] natType (Expr.mkApps (const0 "Nat.succ") [const0 "Nat.zero"]),
    .opaqueDefinition "opaqueTrue" [] boolType (const0 "Bool.true"),
    .definition "polyId" ["u"] polyIdType polyIdValue,
    .axiom "pairSeed" [] (const0 "Pair"),
    .axiom "sigmaSeed" [] (const0 "SigmaBox"),
    .axiom "vec1Seed" [] (Expr.mkApps (const0 "Vec1") [boolType, const0 "Nat.zero"]),
    .axiom
      "shiftedSeed"
      []
      (Expr.mkApps (const0 "ShiftedStruct") [boolType, Expr.mkApps (const0 "Nat.succ") [const0 "Nat.zero"]]),
    .axiom "P" [] propSort,
    .axiom "pProof" [] pProp,
    .axiom "qProof" [] pProp,
    .theorem "pTheorem" [] pProp pProof
  ]

def sampleEnv : Result Env :=
  addDeclarations [] sampleDeclarations

def natSucc (value : Expr) : Expr :=
  Expr.mkApps (const0 "Nat.succ") [value]

def boolFalse : Expr :=
  const0 "Bool.false"

def boolTrue : Expr :=
  const0 "Bool.true"

def opaqueTrue : Expr :=
  const0 "opaqueTrue"

def natZero : Expr :=
  const0 "Nat.zero"

def pairType : Expr :=
  const0 "Pair"

def pairMk (fst snd : Expr) : Expr :=
  Expr.mkApps (const0 "Pair.mk") [fst, snd]

def pairSeedName : Name :=
  "pairSeed"

def pairSeed : Expr :=
  const0 pairSeedName

def pairZeroTrue : Expr :=
  pairMk natZero boolTrue

def pairFst (pair : Expr) : Expr :=
  .proj "Pair" 0 pair

def pairSnd (pair : Expr) : Expr :=
  .proj "Pair" 1 pair

def pairFstFn (pair : Expr) : Expr :=
  Expr.mkApps (const0 "Pair.fst") [pair]

def pairEtaExpansion : Expr :=
  pairMk (pairFst pairSeed) (pairSnd pairSeed)

def sigmaBoxType : Expr :=
  const0 "SigmaBox"

def sigmaBoxMk (elem value : Expr) : Expr :=
  Expr.mkApps (const0 "SigmaBox.mk") [elem, value]

def sigmaSeedName : Name :=
  "sigmaSeed"

def sigmaSeed : Expr :=
  const0 sigmaSeedName

def sigmaBoolTrue : Expr :=
  sigmaBoxMk boolType boolTrue

def sigmaTypeProj (box : Expr) : Expr :=
  .proj "SigmaBox" 0 box

def sigmaValueProj (box : Expr) : Expr :=
  .proj "SigmaBox" 1 box

def sigmaValueFn (box : Expr) : Expr :=
  Expr.mkApps (const0 "SigmaBox.value") [box]

def sigmaEtaExpansion : Expr :=
  sigmaBoxMk (sigmaTypeProj sigmaSeed) (sigmaValueProj sigmaSeed)

def vec1Type (elem index : Expr) : Expr :=
  Expr.mkApps (const0 "Vec1") [elem, index]

def vec1Mk (elem index value : Expr) : Expr :=
  Expr.mkApps (const0 "Vec1.mk") [elem, index, value]

def vec1SeedName : Name :=
  "vec1Seed"

def vec1Seed : Expr :=
  const0 vec1SeedName

def vec1BoolZeroTrue : Expr :=
  vec1Mk boolType natZero boolTrue

def vec1ValueProj (box : Expr) : Expr :=
  .proj "Vec1" 0 box

def vec1ValueFn (box : Expr) : Expr :=
  Expr.mkApps (const0 "Vec1.value") [boolType, natZero, box]

def vec1EtaExpansion : Expr :=
  vec1Mk boolType natZero (vec1ValueProj vec1Seed)

def shiftedStructType (elem index : Expr) : Expr :=
  Expr.mkApps (const0 "ShiftedStruct") [elem, index]

def shiftedStructMk (elem pred value : Expr) : Expr :=
  Expr.mkApps (const0 "ShiftedStruct.mk") [elem, pred, value]

def shiftedSeedName : Name :=
  "shiftedSeed"

def shiftedSeed : Expr :=
  const0 shiftedSeedName

def shiftedBoolOneTrue : Expr :=
  shiftedStructMk boolType natZero boolTrue

def shiftedPredProj (box : Expr) : Expr :=
  .proj "ShiftedStruct" 0 box

def shiftedValueProj (box : Expr) : Expr :=
  .proj "ShiftedStruct" 1 box

def shiftedValueFn (box : Expr) : Expr :=
  Expr.mkApps (const0 "ShiftedStruct.value") [boolType, natSucc natZero, box]

def shiftedEtaExpansion : Expr :=
  shiftedStructMk boolType (shiftedPredProj shiftedSeed) (shiftedValueProj shiftedSeed)

def mutEvenType : Expr :=
  const0 "MutEven"

def mutOddType : Expr :=
  const0 "MutOdd"

def mutEvenZero : Expr :=
  const0 "MutEven.zero"

def mutEvenSuccOdd (pred : Expr) : Expr :=
  Expr.mkApps (const0 "MutEven.succOdd") [pred]

def mutOddSuccEven (pred : Expr) : Expr :=
  Expr.mkApps (const0 "MutOdd.succEven") [pred]

def mutEvenTwo : Expr :=
  mutEvenSuccOdd (mutOddSuccEven mutEvenZero)

def mutOddOne : Expr :=
  mutOddSuccEven mutEvenZero

def mutEvenMotive : Expr :=
  .lam "x" mutEvenType natType

def mutOddMotive : Expr :=
  .lam "x" mutOddType natType

def mutEvenZeroCase : Expr :=
  natZero

def mutEvenSuccOddCase : Expr :=
  .lam "pred" mutOddType (.lam "ih" natType (natSucc (.bvar 0)))

def mutOddSuccEvenCase : Expr :=
  .lam "pred" mutEvenType (.lam "ih" natType (natSucc (.bvar 0)))

def mutEvenRecOnTwo : Expr :=
  Expr.mkApps
    (recConst "MutEven.rec")
    [
      mutEvenMotive,
      mutOddMotive,
      mutEvenZeroCase,
      mutEvenSuccOddCase,
      mutOddSuccEvenCase,
      mutEvenTwo
    ]

def mutEvenRecOnOddOne : Expr :=
  Expr.mkApps
    (recConst "MutOdd.rec")
    [
      mutEvenMotive,
      mutOddMotive,
      mutEvenZeroCase,
      mutEvenSuccOddCase,
      mutOddSuccEvenCase,
      mutOddOne
    ]

def listNil (elem : Expr) : Expr :=
  Expr.mkApps (const0 "List.nil") [elem]

def listCons (elem head tail : Expr) : Expr :=
  Expr.mkApps (const0 "List.cons") [elem, head, tail]

def mutNestAType : Expr :=
  const0 "MutNestA"

def mutNestBType : Expr :=
  const0 "MutNestB"

def mutNestAMk (children : Expr) : Expr :=
  Expr.mkApps (const0 "MutNestA.mk") [children]

def mutNestBMk (child : Expr) : Expr :=
  Expr.mkApps (const0 "MutNestB.mk") [child]

def mutNestANil : Expr :=
  mutNestAMk (listNil mutNestBType)

def mutNestBLeaf : Expr :=
  mutNestBMk mutNestANil

def mutNestAOne : Expr :=
  mutNestAMk (listCons mutNestBType mutNestBLeaf (listNil mutNestBType))

def mutNestAMotive : Expr :=
  .lam "x" mutNestAType natType

def mutNestListMotive : Expr :=
  .lam "xs" (listType mutNestBType) natType

def mutNestBMotive : Expr :=
  .lam "x" mutNestBType natType

def mutNestACase : Expr :=
  .lam "children" (listType mutNestBType) (.lam "ih" natType (natSucc (.bvar 0)))

def mutNestNilCase : Expr :=
  natZero

def mutNestConsCase : Expr :=
  .lam
    "head"
    mutNestBType
    (.lam
      "tail"
      (listType mutNestBType)
      (.lam
        "ihHead"
        natType
        (.lam "ihTail" natType (.bvar 1))))

def mutNestBCase : Expr :=
  .lam "child" mutNestAType (.lam "ih" natType (natSucc (.bvar 0)))

def mutNestARecOnOne : Expr :=
  Expr.mkApps
    (recConst "MutNestA.rec")
    [
      mutNestAMotive,
      mutNestBMotive,
      mutNestListMotive,
      mutNestACase,
      mutNestBCase,
      mutNestNilCase,
      mutNestConsCase,
      mutNestAOne
    ]

def polyId (level : Level) (type value : Expr) : Expr :=
  Expr.mkApps (.const "polyId" [level]) [type, value]

def polyIdBool : Expr :=
  polyId type0Level boolType boolTrue

def polyIdTypeArg : Expr :=
  polyId type1Level type0Sort boolType

def polyBoxType (level : Level) (elem : Expr) : Expr :=
  Expr.mkApps (.const "PolyBox" [level]) [elem]

def polyBoxMk (level : Level) (elem value : Expr) : Expr :=
  Expr.mkApps (.const "PolyBox.mk" [level]) [elem, value]

def polyBoxBool : Expr :=
  polyBoxMk type0Param boolType boolTrue

def polyBoxBoolMotive : Expr :=
  .lam "box" (polyBoxType type0Param boolType) boolType

def polyBoxBoolCase : Expr :=
  .lam "value" boolType (.bvar 0)

def polyBoxRecOnTrue : Expr :=
  Expr.mkApps
    (.const "PolyBox.rec" [type0Level, type0Param])
    [
      boolType,
      polyBoxBoolMotive,
      polyBoxBoolCase,
      polyBoxBool
    ]

def polyBoxTypeBox : Expr :=
  polyBoxMk type1Param type0Sort boolType

def polyBoxTypeMotive : Expr :=
  .lam "box" (polyBoxType type1Param type0Sort) type0Sort

def polyBoxTypeCase : Expr :=
  .lam "value" type0Sort (.bvar 0)

def polyBoxRecOnBoolType : Expr :=
  Expr.mkApps
    (.const "PolyBox.rec" [type1Level, type1Param])
    [
      type0Sort,
      polyBoxTypeMotive,
      polyBoxTypeCase,
      polyBoxTypeBox
    ]

def polyBoxRecCtorLevelMismatch : Expr :=
  Expr.mkApps
    (.const "PolyBox.rec" [type0Level, type0Param])
    [
      boolType,
      polyBoxBoolMotive,
      polyBoxBoolCase,
      polyBoxTypeBox
    ]

def eqTypeAt (level : Level) (elem lhs rhs : Expr) : Expr :=
  Expr.mkApps (.const "Eq" [level]) [elem, lhs, rhs]

def eqType (elem lhs rhs : Expr) : Expr :=
  eqTypeAt type0Level elem lhs rhs

def eqReflAt (level : Level) (elem value : Expr) : Expr :=
  Expr.mkApps (.const "Eq.refl" [level]) [elem, value]

def eqRefl (elem value : Expr) : Expr :=
  eqReflAt type0Level elem value

def eqBoolTrueMotive : Expr :=
  .lam
    "rhs"
    boolType
    (.lam "h" (eqType boolType boolTrue (.bvar 0)) boolType)

def eqRecOnRefl : Expr :=
  Expr.mkApps
    (.const "Eq.rec" [type0Level, type0Level])
    [
      boolType,
      boolTrue,
      eqBoolTrueMotive,
      boolFalse,
      boolTrue,
      eqRefl boolType boolTrue
    ]

def boolEqRel : Expr :=
  .lam
    "a"
    boolType
    (.lam "b" boolType (eqType boolType (.bvar 1) (.bvar 0)))

def boolTrivialRel : Expr :=
  .lam "a" boolType (.lam "b" boolType pProp)

def boolQuotType : Expr :=
  quotientTypeExpr type0Level boolType boolEqRel

def boolQuotTrue : Expr :=
  quotientMkExpr type0Level boolType boolEqRel boolTrue

def boolQuotTrueOtherRel : Expr :=
  quotientMkExpr type0Level boolType boolTrivialRel boolTrue

def boolId : Expr :=
  .lam "x" boolType (.bvar 0)

def boolQuotLiftResp : Expr :=
  .lam
    "a"
    boolType
    (.lam
      "b"
      boolType
      (.lam "h" (Expr.mkApps boolEqRel [.bvar 1, .bvar 0]) (.bvar 0)))

def boolQuotLiftOnTrue : Expr :=
  Expr.mkApps
    (.const "Quot.lift" [type0Level, type0Level])
    [
      boolType,
      boolEqRel,
      boolType,
      boolId,
      boolQuotLiftResp,
      boolQuotTrue
    ]

def boolQuotLiftRelationMismatch : Expr :=
  Expr.mkApps
    (.const "Quot.lift" [type0Level, type0Level])
    [
      boolType,
      boolEqRel,
      boolType,
      boolId,
      boolQuotLiftResp,
      boolQuotTrueOtherRel
    ]

def boolQuotSoundRefl : Expr :=
  Expr.mkApps
    (.const "Quot.sound" [type0Level])
    [
      boolType,
      boolEqRel,
      boolTrue,
      boolTrue,
      eqRefl boolType boolTrue
    ]

def vecType (elem index : Expr) : Expr :=
  Expr.mkApps (const0 "Vec") [elem, index]

def vecNil (elem : Expr) : Expr :=
  Expr.mkApps (const0 "Vec.nil") [elem]

def vecCons (elem index head tail : Expr) : Expr :=
  Expr.mkApps (const0 "Vec.cons") [elem, index, head, tail]

def vecOneBool : Expr :=
  vecCons boolType natZero boolTrue (vecNil boolType)

def vecBoolMotive : Expr :=
  .lam "n" natType (.lam "xs" (vecType boolType (.bvar 0)) natType)

def vecBoolNilCase : Expr :=
  natZero

def vecBoolConsCase : Expr :=
  .lam
    "n"
    natType
    (.lam
      "head"
      boolType
      (.lam
        "tail"
        (vecType boolType (.bvar 1))
        (.lam "ih" natType (natSucc (.bvar 0)))))

def vecRecOnOne : Expr :=
  Expr.mkApps
    (recConst "Vec.rec")
    [
      boolType,
      vecBoolMotive,
      vecBoolNilCase,
      vecBoolConsCase,
      natSucc natZero,
      vecOneBool
    ]

def vecRecIndexMismatch : Expr :=
  Expr.mkApps
    (recConst "Vec.rec")
    [
      boolType,
      vecBoolMotive,
      vecBoolNilCase,
      vecBoolConsCase,
      natZero,
      vecOneBool
    ]

def heightTreeType (height : Expr) : Expr :=
  Expr.mkApps (const0 "HeightTree") [height]

def heightTreeLeaf : Expr :=
  const0 "HeightTree.leaf"

def heightTreeNode (height child : Expr) : Expr :=
  Expr.mkApps (const0 "HeightTree.node") [height, child]

def heightTreeOne : Expr :=
  heightTreeNode natZero heightTreeLeaf

def heightTreeMotive : Expr :=
  .lam "height" natType (.lam "tree" (heightTreeType (.bvar 0)) natType)

def heightTreeLeafCase : Expr :=
  natZero

def heightTreeNodeCase : Expr :=
  .lam
    "height"
    natType
    (.lam
      "child"
      (heightTreeType (.bvar 0))
      (.lam "ih" natType (natSucc (.bvar 0))))

def heightTreeRecOnOne : Expr :=
  Expr.mkApps
    (recConst "HeightTree.rec")
    [
      heightTreeMotive,
      heightTreeLeafCase,
      heightTreeNodeCase,
      natSucc natZero,
      heightTreeOne
    ]

def natToBoolMotive : Expr :=
  .lam "n" natType boolType

def natRecStepType : Expr :=
  .forallE "n" natType (.forallE "ih" boolType boolType)

def natRecPartial : Expr :=
  Expr.mkApps (recConst "Nat.rec") [natToBoolMotive, boolTrue]

def natRecMissingLevel : Expr :=
  Expr.mkApps
    (const0 "Nat.rec")
    [
      natToBoolMotive,
      boolTrue,
      .lam "n" natType (.lam "ih" boolType boolFalse),
      const0 "one"
    ]

def natRecExtraLevels : Expr :=
  Expr.mkApps
    (.const "Nat.rec" [type0Level, type1Level])
    [
      natToBoolMotive,
      boolTrue,
      .lam "n" natType (.lam "ih" boolType boolFalse),
      const0 "one"
    ]

def natIsZeroOnOne : Expr :=
  Expr.mkApps
    (recConst "Nat.rec")
    [
      natToBoolMotive,
      boolTrue,
      .lam "n" natType (.lam "ih" boolType boolFalse),
      const0 "one"
    ]

def listRecParamMismatch : Expr :=
  Expr.mkApps
    (recConst "List.rec")
    [
      natType,
      .lam "xs" (listType natType) boolType,
      boolFalse,
      .lam "head" natType (.lam "tail" (listType natType) (.lam "ih" boolType boolTrue)),
      listNil boolType
    ]

def singletonTrue : Expr :=
  listCons boolType boolTrue (listNil boolType)

def natListTreeType : Expr :=
  const0 "NatListTree"

def leafZero : Expr :=
  Expr.mkApps (const0 "NatListTree.leaf") [natZero]

def leafList : Expr :=
  listCons natListTreeType leafZero (listNil natListTreeType)

def nodeLeafList : Expr :=
  Expr.mkApps (const0 "NatListTree.node") [leafList]

def natListTreeMotive : Expr :=
  .lam "t" natListTreeType natType

def natListMotive : Expr :=
  .lam "ts" (listType natListTreeType) natType

def natListTreeLeafCase : Expr :=
  .lam "n" natType (natSucc natZero)

def natListTreeNodeCase : Expr :=
  .lam "ts" (listType natListTreeType) (.lam "ih" natType (.bvar 0))

def natListTreeNilCase : Expr :=
  natZero

def natListTreeConsCase : Expr :=
  .lam
    "head"
    natListTreeType
    (.lam
      "tail"
      (listType natListTreeType)
      (.lam
        "ihHead"
        natType
        (.lam "ihTail" natType (natSucc (.bvar 0)))))

def natListTreeRecOnNode : Expr :=
  Expr.mkApps
    (recConst "NatListTree.rec")
    [
      natListTreeMotive,
      natListMotive,
      natListTreeLeafCase,
      natListTreeNodeCase,
      natListTreeNilCase,
      natListTreeConsCase,
      nodeLeafList
    ]

def natListTreeRecOnList : Expr :=
  Expr.mkApps
    (recConst "NatListTree.rec_1")
    [
      natListTreeMotive,
      natListMotive,
      natListTreeLeafCase,
      natListTreeNodeCase,
      natListTreeNilCase,
      natListTreeConsCase,
      leafList
    ]

def depNestType : Expr :=
  const0 "DepNest"

def wrapAtType (index elem : Expr) : Expr :=
  Expr.mkApps (const0 "WrapAt") [index, elem]

def wrapAtMk (index elem value : Expr) : Expr :=
  Expr.mkApps (const0 "WrapAt.mk") [index, elem, value]

def wrapAtZeroBoolType : Expr :=
  wrapAtType natZero boolType

def wrapAtTrueZero : Expr :=
  wrapAtMk natZero boolType boolTrue

def wrapAtBoolMotive : Expr :=
  .lam "t" wrapAtZeroBoolType natType

def wrapAtBoolCase : Expr :=
  .lam "x" boolType natZero

def wrapAtRecOnTrueZero : Expr :=
  Expr.mkApps
    (recConst "WrapAt.rec")
    [
      natZero,
      boolType,
      wrapAtBoolMotive,
      wrapAtBoolCase,
      wrapAtTrueZero
    ]

def depNestFieldType : Expr :=
  .forallE "n" natType (wrapAtType (.bvar 0) depNestType)

def depNestMotive : Expr :=
  .lam "t" depNestType boolType

def wrapAtDepNestMotive : Expr :=
  .lam "n" natType (.lam "t" (wrapAtType (.bvar 0) depNestType) boolType)

def depNestRootCase : Expr :=
  .lam "f" depNestFieldType (.lam "ih" (.forallE "n" natType boolType) boolFalse)

def depNestWrapCase : Expr :=
  .lam "n" natType (.lam "x" depNestType (.lam "ih" boolType boolTrue))

def depNestSeedName : Name :=
  "depNestSeed"

def depNestSeed : Expr :=
  const0 depNestSeedName

def wrapAtSeedZero : Expr :=
  wrapAtMk natZero depNestType depNestSeed

def depNestHelperRecOnSeed : Expr :=
  Expr.mkApps
    (recConst "DepNest.rec_1")
    [
      depNestMotive,
      wrapAtDepNestMotive,
      depNestRootCase,
      depNestWrapCase,
      natZero,
      wrapAtSeedZero
    ]

def depNestPType (param : Expr) : Expr :=
  Expr.mkApps (const0 "DepNestP") [param]

def depNestPBoolType : Expr :=
  depNestPType boolType

def depNestPFieldType : Expr :=
  .forallE "n" natType (wrapAtType (.bvar 0) depNestPBoolType)

def depNestPMotive : Expr :=
  .lam "t" depNestPBoolType boolType

def wrapAtDepNestPMotive : Expr :=
  .lam "n" natType (.lam "t" (wrapAtType (.bvar 0) depNestPBoolType) boolType)

def depNestPRootCase : Expr :=
  .lam "f" depNestPFieldType (.lam "ih" (.forallE "n" natType boolType) boolFalse)

def depNestPWrapCase : Expr :=
  .lam "n" natType (.lam "x" depNestPBoolType (.lam "ih" boolType boolTrue))

def depNestPSeedName : Name :=
  "depNestPSeed"

def depNestPSeed : Expr :=
  const0 depNestPSeedName

def wrapAtDepNestPSeedZero : Expr :=
  wrapAtMk natZero depNestPBoolType depNestPSeed

def depNestPHelperRecOnSeed : Expr :=
  Expr.mkApps
    (recConst "DepNestP.rec_1")
    [
      boolType,
      depNestPMotive,
      wrapAtDepNestPMotive,
      depNestPRootCase,
      depNestPWrapCase,
      natZero,
      wrapAtDepNestPSeedZero
    ]

def depAfterRecType : Expr :=
  const0 "DepAfterRec"

def depAfterRecMotive : Expr :=
  .lam "t" depAfterRecType natType

def depAfterRecCase : Expr :=
  .lam
    "n"
    natType
    (.lam
      "child"
      depAfterRecType
      (.lam
        "box"
        (wrapAtType (.bvar 1) boolType)
        (.lam "ih" natType (.bvar 0))))

def depAfterRecSeedName : Name :=
  "depAfterRecSeed"

def depAfterRecSeed : Expr :=
  const0 depAfterRecSeedName

def depAfterRecOnSeed : Expr :=
  Expr.mkApps
    (recConst "DepAfterRec.rec")
    [
      depAfterRecMotive,
      depAfterRecCase,
      depAfterRecSeed
    ]

def depFieldTreeType : Expr :=
  const0 "DepFieldTree"

def depFieldTreeMotive : Expr :=
  .lam "t" depFieldTreeType natType

def wrapAtDepFieldTreeMotive : Expr :=
  .lam "n" natType (.lam "t" (wrapAtType (.bvar 0) depFieldTreeType) natType)

def depFieldTreeRootCase : Expr :=
  .lam
    "n"
    natType
    (.lam
      "child"
      (wrapAtType (.bvar 0) depFieldTreeType)
      (.lam "ih" natType (.bvar 0)))

def depFieldTreeWrapCase : Expr :=
  .lam "n" natType (.lam "x" depFieldTreeType (.lam "ih" natType natZero))

def depFieldTreeSeedName : Name :=
  "depFieldTreeSeed"

def depFieldTreeSeed : Expr :=
  const0 depFieldTreeSeedName

def wrapAtDepFieldTreeSeedZero : Expr :=
  wrapAtMk natZero depFieldTreeType depFieldTreeSeed

def depFieldTreeNode : Expr :=
  Expr.mkApps (const0 "DepFieldTree.mk") [natZero, wrapAtDepFieldTreeSeedZero]

def depFieldTreeRecOnNode : Expr :=
  Expr.mkApps
    (recConst "DepFieldTree.rec")
    [
      depFieldTreeMotive,
      wrapAtDepFieldTreeMotive,
      depFieldTreeRootCase,
      depFieldTreeWrapCase,
      depFieldTreeNode
    ]

def demoReportLines : List String :=
  [
    "definition one : Nat checks",
    "opaque definitions type-check without unfolding",
    "polymorphic definitions instantiate at data and type universes",
    "polymorphic inductives instantiate at data and type universes",
    "basic Prop constants, proof irrelevance, and proposition-valued functions check",
    "Prop inductive recursors enforce large-elimination rules",
    "recursor constants type-check and support partial application",
    "Nat.rec on one normalizes to Bool.false",
    "List Bool constructor application checks",
    "Eq.refl checks as an indexed constructor",
    "Eq.rec eliminates into data and reduces on refl",
    "Quot.lift computes on Quot.mk and Quot.sound checks",
    "core and indexed projections type-check, reduce, and support structure eta",
    "theorem declarations store checked proof values without unfolding",
    "mutual inductive recursors compute across block members",
    "nested mutual recursors compute through positive containers",
    "Vec.rec computes through indexed constructor targets",
    "HeightTree.rec computes through recursive indexed targets",
    "NatListTree.rec uses a nested helper recursor through List",
    "WrapAt.rec respects inductive parameters",
    "let-bound field types are normalized before positivity analysis",
    "helper-recursion targets are deduplicated by canonical form",
    "nested inductive parameters reject local variables",
    "constructor fields may depend on earlier fields",
    "ill-scoped field dependencies are rejected",
    "constructor targets must use the declared parameters",
    "minor premises bind fields before induction hypotheses",
    "constructorless inductives may sit below parameter universes",
    "field universes are rejected when they exceed the result universe",
    "recursor reduction rejects targets whose constructor parameters disagree",
    "recursor reduction rejects targets whose constructor indices disagree",
    "non-positive nested uses of inductive parameters are rejected"
  ]

def projectionDemoChecks (env : Env) : Result Unit := do
  let pairTy ← infer env [] pairZeroTrue
  let _ ← checkDefEq env pairTy pairType
  let pairFstTy ← infer env [] (pairFst pairZeroTrue)
  let _ ← checkDefEq env pairFstTy natType
  let pairFstNf ← normalize env (pairFst pairZeroTrue)
  let _ ← checkDefEq env pairFstNf natZero
  let pairSndTy ← infer env [] (pairSnd pairZeroTrue)
  let _ ← checkDefEq env pairSndTy boolType
  let pairFstFnNf ← normalize env (pairFstFn pairZeroTrue)
  let _ ← checkDefEq env pairFstFnNf natZero
  let _ ← checkDefEq env pairEtaExpansion pairSeed
  let sigmaTypeNf ← normalize env (sigmaTypeProj sigmaBoolTrue)
  let _ ← checkDefEq env sigmaTypeNf boolType
  let sigmaValueTy ← infer env [] (sigmaValueProj sigmaBoolTrue)
  let _ ← checkDefEq env sigmaValueTy boolType
  let sigmaValueNf ← normalize env (sigmaValueProj sigmaBoolTrue)
  let _ ← checkDefEq env sigmaValueNf boolTrue
  let sigmaValueFnNf ← normalize env (sigmaValueFn sigmaBoolTrue)
  let _ ← checkDefEq env sigmaValueFnNf boolTrue
  let _ ← checkDefEq env sigmaEtaExpansion sigmaSeed
  let vec1ValueTy ← infer env [] (vec1ValueProj vec1BoolZeroTrue)
  let _ ← checkDefEq env vec1ValueTy boolType
  let vec1ValueNf ← normalize env (vec1ValueProj vec1BoolZeroTrue)
  let _ ← checkDefEq env vec1ValueNf boolTrue
  let vec1ValueFnNf ← normalize env (vec1ValueFn vec1BoolZeroTrue)
  let _ ← checkDefEq env vec1ValueFnNf boolTrue
  let _ ← checkDefEq env vec1EtaExpansion vec1Seed
  let shiftedPredTy ← infer env [] (shiftedPredProj shiftedBoolOneTrue)
  let _ ← checkDefEq env shiftedPredTy natType
  let shiftedPredNf ← normalize env (shiftedPredProj shiftedBoolOneTrue)
  let _ ← checkDefEq env shiftedPredNf natZero
  let shiftedValueTy ← infer env [] (shiftedValueProj shiftedBoolOneTrue)
  let _ ← checkDefEq env shiftedValueTy boolType
  let shiftedValueNf ← normalize env (shiftedValueProj shiftedBoolOneTrue)
  let _ ← checkDefEq env shiftedValueNf boolTrue
  let shiftedValueFnNf ← normalize env (shiftedValueFn shiftedBoolOneTrue)
  let _ ← checkDefEq env shiftedValueFnNf boolTrue
  match checkDefEq env shiftedEtaExpansion shiftedSeed with
  | .ok _ => .error "ShiftedStruct should not eta-reduce across a computed index"
  | .error _ => pure ()
  let proofBoxProjectionTy ← infer env [] proofBoxProjection
  let _ ← checkDefEq env proofBoxProjectionTy pProp
  let proofBoxProjectionNf ← normalize env proofBoxProjection
  let _ ← checkDefEq env proofBoxProjectionNf pProof
  let proofBoxProjectionFnNf ← normalize env proofBoxProjectionFn
  let _ ← checkDefEq env proofBoxProjectionFnNf pProof
  match infer env [] dataWitnessPropProjection with
  | .ok _ => .error "DataWitnessProp projection should reject extraction of data from Prop"
  | .error _ => pure ()

def demoCoreChecks (env : Env) : Result Unit := do
  let oneTy ← infer env [] (const0 "one")
  let _ ← checkDefEq env oneTy natType
  let opaqueTrueTy ← infer env [] opaqueTrue
  let _ ← checkDefEq env opaqueTrueTy boolType
  let opaqueTrueNf ← normalize env opaqueTrue
  let _ ← checkDefEq env opaqueTrueNf opaqueTrue
  let _ ← projectionDemoChecks env
  let polyIdBoolTy ← infer env [] polyIdBool
  let _ ← checkDefEq env polyIdBoolTy boolType
  let polyIdBoolNf ← normalize env polyIdBool
  let _ ← checkDefEq env polyIdBoolNf boolTrue
  let polyIdTypeTy ← infer env [] polyIdTypeArg
  let _ ← checkDefEq env polyIdTypeTy type0Sort
  let polyIdTypeNf ← normalize env polyIdTypeArg
  let _ ← checkDefEq env polyIdTypeNf boolType
  let polyBoxBoolTy ← infer env [] polyBoxBool
  let _ ← checkDefEq env polyBoxBoolTy (polyBoxType type0Param boolType)
  let polyBoxBoolRecTy ← infer env [] polyBoxRecOnTrue
  let _ ← checkDefEq env polyBoxBoolRecTy boolType
  let polyBoxBoolRecNf ← normalize env polyBoxRecOnTrue
  let _ ← checkDefEq env polyBoxBoolRecNf boolTrue
  let polyBoxTypeBoxTy ← infer env [] polyBoxTypeBox
  let _ ← checkDefEq env polyBoxTypeBoxTy (polyBoxType type1Param type0Sort)
  let polyBoxTypeRecTy ← infer env [] polyBoxRecOnBoolType
  let _ ← checkDefEq env polyBoxTypeRecTy type0Sort
  let polyBoxTypeRecNf ← normalize env polyBoxRecOnBoolType
  let _ ← checkDefEq env polyBoxTypeRecNf boolType
  let _ ← propDemoChecks env
  let _ ← infer env [] (recConst "Nat.rec")
  let natRecPartialTy ← infer env [] natRecPartial
  let _ ←
    checkDefEq
      env
      natRecPartialTy
      (.forallE "step" natRecStepType (.forallE "t" natType boolType))
  let _ ← infer env [] (recConst "LetTree.rec_1")
  let natRecTy ← infer env [] natIsZeroOnOne
  let _ ← checkDefEq env natRecTy boolType
  let natRecNf ← normalize env natIsZeroOnOne
  if natRecNf != boolFalse then
    .error s!"unexpected normal form for Nat.rec example: {repr natRecNf}"
  else
    pure ()
  let singletonTy ← infer env [] singletonTrue
  let _ ← checkDefEq env singletonTy (listType boolType)
  let reflTy ← infer env [] (eqRefl boolType boolTrue)
  let _ ← checkDefEq env reflTy (eqType boolType boolTrue boolTrue)
  let eqRecTy ← infer env [] eqRecOnRefl
  let _ ← checkDefEq env eqRecTy boolType
  let eqRecNf ← normalize env eqRecOnRefl
  let _ ← checkDefEq env eqRecNf boolFalse
  let boolQuotTy ← infer env [] boolQuotTrue
  let _ ← checkDefEq env boolQuotTy boolQuotType
  let boolQuotLiftTy ← infer env [] boolQuotLiftOnTrue
  let _ ← checkDefEq env boolQuotLiftTy boolType
  let boolQuotLiftNf ← normalize env boolQuotLiftOnTrue
  let _ ← checkDefEq env boolQuotLiftNf boolTrue
  let boolQuotSoundTy ← infer env [] boolQuotSoundRefl
  let _ ←
    checkDefEq
      env
      boolQuotSoundTy
      (eqTypeAt type0Level boolQuotType boolQuotTrue boolQuotTrue)
  let mutEvenTy ← infer env [] mutEvenTwo
  let _ ← checkDefEq env mutEvenTy mutEvenType
  let mutEvenRecTy ← infer env [] mutEvenRecOnTwo
  let _ ← checkDefEq env mutEvenRecTy natType
  let mutEvenRecNf ← normalize env mutEvenRecOnTwo
  let _ ← checkDefEq env mutEvenRecNf (natSucc (natSucc natZero))
  let mutOddHelperTy ← infer env [] mutEvenRecOnOddOne
  let _ ← checkDefEq env mutOddHelperTy natType
  let mutOddHelperNf ← normalize env mutEvenRecOnOddOne
  let _ ← checkDefEq env mutOddHelperNf (natSucc natZero)
  let mutNestTy ← infer env [] mutNestAOne
  let _ ← checkDefEq env mutNestTy mutNestAType
  let mutNestRecTy ← infer env [] mutNestARecOnOne
  let _ ← checkDefEq env mutNestRecTy natType
  let mutNestRecNf ← normalize env mutNestARecOnOne
  let _ ← checkDefEq env mutNestRecNf (natSucc (natSucc (natSucc natZero)))
  let vecRecTy ← infer env [] vecRecOnOne
  let _ ← checkDefEq env vecRecTy natType
  let vecRecNf ← normalize env vecRecOnOne
  let _ ← checkDefEq env vecRecNf (natSucc natZero)
  let heightTreeTy ← infer env [] heightTreeRecOnOne
  let _ ← checkDefEq env heightTreeTy natType
  let heightTreeNf ← normalize env heightTreeRecOnOne
  let _ ← checkDefEq env heightTreeNf (natSucc natZero)
  let treeRecTy ← infer env [] natListTreeRecOnNode
  let _ ← checkDefEq env treeRecTy natType
  let treeRecNf ← normalize env natListTreeRecOnNode
  let _ ← checkDefEq env treeRecNf (natSucc natZero)
  let listRecTy ← infer env [] natListTreeRecOnList
  let _ ← checkDefEq env listRecTy natType
  let listRecNf ← normalize env natListTreeRecOnList
  let _ ← checkDefEq env listRecNf (natSucc natZero)
  pure ()

def demoGeneratedInductiveChecks (env : Env) : Result Unit := do
  match addInductive env badSpuriousSpec with
  | .ok _ => .error "BadSpurious should fail the universe check"
  | .error _ => pure ()
  match addInductive env lowSortBoxSpec with
  | .ok _ => .error "LowSortBox should fail the universe check"
  | .error _ => pure ()
  match addInductive env badForwardFieldSpec with
  | .ok _ => .error "BadForwardField should fail field telescope checking"
  | .error _ => pure ()
  match addInductive env badParamTargetSpec with
  | .ok _ => .error "BadParamTarget should fail constructor target checking"
  | .error _ => pure ()
  match addInductive env badWrapSpec with
  | .ok _ => .error "BadWrap should fail the positivity check"
  | .error _ => pure ()
  match addInductiveBlock env badMutualBlock with
  | .ok _ => .error "BadMutualBlock should fail the positivity check"
  | .error _ => pure ()
  let env ← addInductive env harmlessWrapSpec
  match env.findInductive? "HarmlessWrap" with
  | some info =>
      if info.positiveParams != [true] then
        .error s!"HarmlessWrap should record its parameter as positive, got {repr info.positiveParams}"
      else
        pure ()
  | none => .error "HarmlessWrap should be present in the environment"
  let env ← addInductive env nestThroughHarmlessWrapSpec
  let env ← addInductive env harmlessBadParamSpec
  let env ← addInductive env dupHelperSpec
  let _ ← infer env [] (recConst "DupHelper.rec_1")
  match env.findRecursor? "DupHelper.rec" with
  | some (_, family) =>
      if family.targets.length != 2 then
        .error s!"DupHelper should have exactly two family targets, got {family.targets.length}"
      else
        pure ()
  | none => .error "DupHelper.rec should be present in the environment"
  match env.find? "DupHelper.rec_2" with
  | some _ => .error "DupHelper should not generate a duplicate helper recursor"
  | none => pure ()
  let env ← addInductive env wrapAtSpec
  let wrapAtRecTy ← infer env [] wrapAtRecOnTrueZero
  let _ ← checkDefEq env wrapAtRecTy natType
  let wrapAtRecNf ← normalize env wrapAtRecOnTrueZero
  let _ ← checkDefEq env wrapAtRecNf natZero
  match addInductive env depNestSpec with
  | .ok _ => .error "DepNest should reject local variables in nested inductive parameters"
  | .error _ => pure ()
  match addInductive env depNestPSpec with
  | .ok _ => .error "DepNestP should reject local variables in nested inductive parameters"
  | .error _ => pure ()
  let env ← addInductive env depAfterRecSpec
  let env ← addAxiom env depAfterRecSeedName depAfterRecType
  let depAfterRecTy ← infer env [] depAfterRecOnSeed
  let _ ← checkDefEq env depAfterRecTy natType
  match addInductive env depFieldTreeSpec with
  | .ok _ => .error "DepFieldTree should reject local variables in nested inductive parameters"
  | .error _ => pure ()
  pure ()

def demoMalformedEntryChecks (env : Env) : Result Unit := do
  match normalize env natRecMissingLevel with
  | .ok _ => .error "Nat.rec without a universe argument should not normalize"
  | .error _ => pure ()
  match normalize env natRecExtraLevels with
  | .ok _ => .error "Nat.rec with extra universe arguments should not normalize"
  | .error _ => pure ()
  match infer env [] listRecParamMismatch with
  | .ok _ => .error "List.rec with mismatched target parameters should not type-check"
  | .error _ => pure ()
  match normalize env listRecParamMismatch with
  | .ok _ => .error "List.rec with mismatched target parameters should not normalize"
  | .error _ => pure ()
  match infer env [] vecRecIndexMismatch with
  | .ok _ => .error "Vec.rec with mismatched target indices should not type-check"
  | .error _ => pure ()
  match normalize env vecRecIndexMismatch with
  | .ok _ => .error "Vec.rec with mismatched target indices should not normalize"
  | .error _ => pure ()
  match infer env [] (const0 "Nat.rec") with
  | .ok _ => .error "Nat.rec should require an explicit universe argument"
  | .error _ => pure ()
  match infer env [] (.const "Nat.rec" [.param "v"]) with
  | .ok _ => .error "Nat.rec should reject open universe arguments"
  | .error _ => pure ()
  match infer env [] (.sort (.param "u")) with
  | .ok _ => .error "Sort expressions should reject open universe levels"
  | .error _ => pure ()
  match infer env [] (.const "polyId" [.param "u"]) with
  | .ok _ => .error "raw constants should reject open universe arguments"
  | .error _ => pure ()
  match normalize env polyBoxRecCtorLevelMismatch with
  | .ok _ => .error "PolyBox.rec should reject mismatched constructor universe arguments"
  | .error _ => pure ()
  match normalize env boolQuotLiftRelationMismatch with
  | .ok _ => .error "Quot.lift should reject mismatched quotient relations during reduction"
  | .error _ => pure ()

def demoReport : Result (List String) := do
  let env ← sampleEnv
  let _ ← demoCoreChecks env
  let _ ← demoGeneratedInductiveChecks env
  let _ ← demoMalformedEntryChecks env
  pure demoReportLines

end LeanLean
