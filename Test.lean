import LeanLean

namespace LeanLean

def expect (label : String) (condition : Bool) : Result Unit :=
  if condition then
    pure ()
  else
    .error s!"{label}: expectation failed"

def expectExprEq (label : String) (actual expected : Expr) : Result Unit :=
  if actual.alphaEq expected then
    pure ()
  else
    .error s!"{label}: expected {repr expected}, got {repr actual}"

def expectError (label : String) (result : Result α) : Result Unit :=
  match result with
  | .ok _ => .error s!"{label}: expected failure"
  | .error _ => pure ()

def telescopeTests : Result Unit := do
  let a : Binder := { name := "A", type := type0Sort }
  let x : Binder := { name := "x", type := .bvar 0 }
  let y : Binder := { name := "y", type := .bvar 0 }
  let _ ← expect "telescope context order is innermost first" (Telescope.toContext [a, x] = [x, a])

  let dependentActual := Telescope.bindForall [a, x] (.bvar 0)
  let dependentExpected := .forallE "A" type0Sort (.forallE "x" (.bvar 0) (.bvar 0))
  let _ ← expectExprEq "dependent telescope binding preserves scoped binder types" dependentActual dependentExpected

  let independentActual := Telescope.bindIndependentForall [x, y] (.bvar 2)
  let independentExpected := .forallE "x" (.bvar 0) (.forallE "y" (.bvar 1) (.bvar 2))
  let _ ←
    expectExprEq
      "independent telescope binding lifts binder types but not the body"
      independentActual
      independentExpected

  match Telescope.instantiateTypes [boolType, natType] [{ name := "z", type := Expr.app (.bvar 1) (.bvar 0) }] with
  | [{ type := actual, .. }] =>
      expectExprEq "telescope type instantiation is simultaneous" actual (Expr.app boolType natType)
  | _ => .error "telescope type instantiation changed telescope length"

  match
    Telescope.instantiateTypes
      [boolType]
      [
        { name := "head", type := .bvar 0 },
        { name := "tail", type := Expr.app (.bvar 1) (.bvar 0) }
      ] with
  | [_, { type := actual, .. }] =>
      expectExprEq
        "telescope type instantiation preserves earlier binders"
        actual
        (Expr.app boolType (.bvar 0))
  | _ => .error "dependent telescope type instantiation changed telescope length"

def universeTests : Result Unit := do
  let _ ← expect "bound universe parameters are closed in their context" ((Level.param "u").closedIn ["u"])
  let _ ← expect "unbound universe parameters are open outside their context" (!((Level.param "u").closedIn []))
  let _ ←
    expect
      "symbolic universe ordering compares matching parameters"
      (Level.le (.param "u") (.max (.param "u") (.param "v")))
  let _ ←
    expect
      "symbolic universe ordering rejects unrelated parameters"
      (!(Level.le (.param "u") (.param "v")))
  let _ ←
    expect
      "imax into Prop reduces to Prop"
      (Level.defEq (Level.normalize (.imax (.param "u") propLevel)) propLevel)
  let _ ←
    expect
      "imax into a data universe reduces to max"
      (Level.defEq
        (Level.normalize (.imax (.param "u") (typeLevel (.param "v"))))
        (.max (.param "u") (typeLevel (.param "v"))))
  let _ ←
    expect
      "unresolved symbolic imax is not collapsed to max"
      (!(Level.defEq
        (Level.normalize (.imax (.param "u") (.param "v")))
        (.max (.param "u") (.param "v"))))
  let _ ← expect "Sort 0 is not a data universe" (!propLevel.definitelyPositive)
  let _ ← expect "Type 0 is a data universe" type0Level.definitelyPositive
  let _ ← expect "Type u is always above Prop" ((typeLevel (.param "u")).definitelyPositive)

  let env ← sampleEnv
  let propTy ← infer env [] (.sort propLevel)
  let _ ← expectExprEq "Prop has type Type 0" propTy type0Sort
  let boolSort ← infer env [] boolType
  let _ ← expectExprEq "Bool lives in Type 0" boolSort type0Sort
  let pTy ← infer env [] pProp
  let _ ← expectExprEq "proposition constants have type Prop" pTy propSort
  let _ ← checkDefEq env pProof qProof
  let _ ← expectError "data constructors remain proof-relevant" (checkDefEq env boolTrue boolFalse)
  let propSelfImpTy ← infer env [] propSelfImpType
  let _ ←
    expectExprEq
      "dependent functions into propositions live in Prop"
      propSelfImpTy
      propSort
  let pTrueTy ← infer env [] pTrueType
  let _ ← expectExprEq "Prop inductive types live in Prop" pTrueTy propSort
  let eqBoolTy ← infer env [] (eqType boolType boolTrue boolTrue)
  let _ ← expectExprEq "equality lives in Prop" eqBoolTy propSort
  let eqTypeTy ← infer env [] (eqReflAt type1Level type0Sort boolType)
  let _ ←
    expectExprEq
      "equality instantiates above Type 0"
      eqTypeTy
      (eqTypeAt type1Level type0Sort boolType boolType)
  let eqRecTy ← infer env [] eqRecOnRefl
  let _ ← checkDefEq env eqRecTy boolType
  let eqRecNf ← normalize env eqRecOnRefl
  let _ ← expectExprEq "Eq.rec reduces on refl" eqRecNf boolFalse
  let boolQuotTy ← infer env [] boolQuotTrue
  let _ ← checkDefEq env boolQuotTy boolQuotType
  let boolQuotLiftTy ← infer env [] boolQuotLiftOnTrue
  let _ ← checkDefEq env boolQuotLiftTy boolType
  let boolQuotLiftNf ← normalize env boolQuotLiftOnTrue
  let _ ← expectExprEq "Quot.lift reduces on Quot.mk" boolQuotLiftNf boolTrue
  let boolQuotSoundTy ← infer env [] boolQuotSoundRefl
  let _ ← checkDefEq env boolQuotSoundTy (eqTypeAt type0Level boolQuotType boolQuotTrue boolQuotTrue)
  let _ ←
    expectError
      "Quot.lift reduction checks quotient relation agreement"
      (normalize env boolQuotLiftRelationMismatch)
  match env.findRecursor? "MutEven.rec" with
  | some (_, family) =>
      let _ ←
        expect
          "mutual recursor families contain both block targets"
          (family.targets.length = 2)
      pure ()
  | none => .error "MutEven.rec should be present in the environment"
  let mutEvenRecTy ← infer env [] mutEvenRecOnTwo
  let _ ← checkDefEq env mutEvenRecTy natType
  let mutEvenRecNf ← normalize env mutEvenRecOnTwo
  let _ ← expectExprEq "mutual recursors reduce across block members" mutEvenRecNf (natSucc (natSucc natZero))
  match env.findRecursor? "MutNestA.rec" with
  | some (_, family) =>
      let _ ←
        expect
          "nested mutual recursor families include helper targets"
          (family.targets.length = 3)
      pure ()
  | none => .error "MutNestA.rec should be present in the environment"
  let mutNestRecNf ← normalize env mutNestARecOnOne
  let _ ←
    expectExprEq
      "nested mutual recursors reduce through positive containers"
      mutNestRecNf
      (natSucc (natSucc (natSucc natZero)))
  let _ ←
    expectError
      "negative mutual occurrences are rejected"
      (addInductiveBlock env badMutualBlock)
  let pTrueRecTy ← infer env [] pTrueRecOnIntro
  let _ ← checkDefEq env pTrueRecTy pProp
  let pTrueRecNf ← normalize env pTrueRecOnIntro
  let _ ← expectExprEq "Prop inductive recursors reduce in Prop" pTrueRecNf pProof
  let pTrueBoolTy ← infer env [] pTrueRecToBool
  let _ ← checkDefEq env pTrueBoolTy boolType
  let pTrueBoolNf ← normalize env pTrueRecToBool
  let _ ← expectExprEq "subsingleton Prop inductive data elimination reduces" pTrueBoolNf boolTrue
  let _ ←
    expectError
      "non-subsingleton Prop inductives reject data-valued motives"
      (infer env [] pOrRecToBool)
  let indexSingletonTy ← infer env [] indexSingletonRecOnZero
  let _ ← checkDefEq env indexSingletonTy natType
  let indexSingletonNf ← normalize env indexSingletonRecOnZero
  let _ ← expectExprEq "index-forced Prop recursors reduce" indexSingletonNf natZero
  let _ ←
    expectError
      "computed index fields do not allow data elimination"
      (infer env [] shiftedIndexPropRecToBool)
  let _ ←
    expectError
      "unindexed data witnesses do not allow data elimination"
      (infer env [] dataWitnessPropRecToBool)
  match env.find? "IndexSingleton.rec" with
  | some info =>
      let _ ←
        expect
          "index-forced Prop recursors carry a motive universe"
          (info.levelParams = ["u"])
      pure ()
  | none => .error "IndexSingleton.rec should be present in the environment"
  match env.find? "DataWitnessProp.rec" with
  | some info =>
      let _ ←
        expect
          "unindexed data-witness Prop recursors stay Prop-only"
          (info.levelParams = [])
      pure ()
  | none => .error "DataWitnessProp.rec should be present in the environment"
  let _ ←
    expectError
      "subsingleton Prop inductive recursors require motive universe arguments"
      (infer env [] (const0 "PTrue.rec"))
  let _ ←
    expectError
      "universe-polymorphic equality rejects open universe arguments"
      (infer env [] (.const "Eq" [.param "u"]))
  let polyIdBoolTy ← infer env [] polyIdBool
  let _ ← expectExprEq "polymorphic definition instantiates at Type 0" polyIdBoolTy boolType
  let polyIdTypeTy ← infer env [] polyIdTypeArg
  let _ ← expectExprEq "polymorphic definition instantiates at Type 1" polyIdTypeTy type0Sort
  let polyBoxBoolTy ← infer env [] polyBoxBool
  let _ ←
    expectExprEq
      "polymorphic inductive constructor instantiates at Type 0"
      polyBoxBoolTy
      (polyBoxType type0Param boolType)
  let polyBoxBoolNf ← normalize env polyBoxRecOnTrue
  let _ ←
    expectExprEq
      "polymorphic inductive recursor reduces at Type 0"
      polyBoxBoolNf
      boolTrue
  let polyBoxTypeBoxTy ← infer env [] polyBoxTypeBox
  let _ ←
    expectExprEq
      "polymorphic inductive constructor instantiates at Type 1"
      polyBoxTypeBoxTy
      (polyBoxType type1Param type0Sort)
  let polyBoxTypeNf ← normalize env polyBoxRecOnBoolType
  let _ ←
    expectExprEq
      "polymorphic inductive recursor reduces at Type 1"
      polyBoxTypeNf
      boolType
  match env.find? "PolyBox.rec" with
  | some info =>
      let _ ←
        expect
          "polymorphic recursor keeps inductive levels before the motive level"
          (info.levelParams = ["u", "u'"])
      pure ()
  | none => .error "PolyBox.rec should be present in the environment"
  let badOpenInductive : InductiveSpec :=
    {
      name := "BadOpenInductive"
      levelParams := ["u"]
      params := []
      level := .param "v"
      ctors := []
    }
  let badDuplicateInductive : InductiveSpec :=
    {
      name := "BadDuplicateInductive"
      levelParams := ["u", "u"]
      params := []
      level := .param "u"
      ctors := []
    }
  let badTargetLevelInductive : InductiveSpec :=
    {
      name := "BadTargetLevelInductive"
      levelParams := ["u"]
      params := [{ name := "α", type := .sort (typeLevel (.param "u")) }]
      level := typeLevel (.param "u")
      ctors :=
        [
          {
            name := "BadTargetLevelInductive.mk"
            fields := []
            target? := some (Expr.mkApps (.const "BadTargetLevelInductive" [0]) [.bvar 0])
          }
        ]
    }
  let badAmbiguousInductive : InductiveSpec :=
    {
      name := "BadAmbiguousInductive"
      levelParams := ["u"]
      params := []
      level := .param "u"
      ctors := []
    }
  let _ ←
    expectError
      "universe-polymorphic definitions reject unbound level parameters"
      (addDefinitionWithLevels [] "badPoly" ["u"] (.sort (.param "v")) (.sort (.param "v")))
  expectError
    "universe-polymorphic definitions reject duplicate level parameters"
    (addDefinitionWithLevels [] "badPolyDup" ["u", "u"] polyIdType polyIdValue)
  let _ ←
    expectError
      "universe-polymorphic inductives reject unbound result levels"
      (addInductive [] badOpenInductive)
  let _ ←
    expectError
      "universe-polymorphic inductives reject duplicate level parameters"
      (addInductive [] badDuplicateInductive)
  let _ ←
    expectError
      "constructor targets must use inductive universe parameters"
      (addInductive [] badTargetLevelInductive)
  let _ ←
    expectError
      "inductive result universe must be known as Prop or data"
      (addInductive [] badAmbiguousInductive)
  expectError
    "recursor reduction rejects mismatched constructor universe arguments"
    (normalize env polyBoxRecCtorLevelMismatch)

def substitutionTests : Result Unit := do
  let body := Expr.app (.bvar 1) (.bvar 0)
  let actual := Expr.instantiateMany [boolType, natType] body
  let expected := Expr.app boolType natType
  let _ ← expectExprEq "simultaneous substitution preserves sibling values" actual expected

  let cutoffBody := Expr.forallE "x" (.bvar 2) (Expr.app (.bvar 2) (.bvar 0))
  let cutoffActual := Expr.instantiateManyFrom 1 [boolType, natType] cutoffBody
  let cutoffExpected := Expr.forallE "x" boolType (Expr.app natType (.bvar 0))
  let _ ← expectExprEq "simultaneous substitution handles nonzero cutoff" cutoffActual cutoffExpected

  let openBody := Expr.forallE "x" (.bvar 1) (Expr.app (.bvar 3) (.bvar 0))
  let openActual := Expr.instantiateManyFrom 1 [boolType, .bvar 0] openBody
  let openExpected := Expr.forallE "x" (.bvar 1) (Expr.app boolType (.bvar 0))
  expectExprEq "simultaneous substitution lifts open inserted values" openActual openExpected

def generatedValidationTests : Result Unit := do
  let env ← sampleEnv
  let malformedType := Expr.forallE "x" natType (Expr.app natType natType)
  expectError
    "generated declaration validation rejects ill-typed generated types"
    (validateGeneratedType env "malformed generated type" [] malformedType)

def environmentTests : Result Unit := do
  let env ← sampleEnv
  match env.find? "one" with
  | some info =>
      let _ ← expect "definitions carry transparent values" info.valueExpr?.isSome
      match info.kind with
      | .defn .transparent => pure ()
      | _ => .error "one should be recorded as a definition"
  | none => .error "one should be present in the environment"
  match env.find? "opaqueTrue" with
  | some info =>
      let _ ← expect "opaque definitions keep stored values" info.valueExpr?.isSome
      match info.kind with
      | .defn .opaque => pure ()
      | _ => .error "opaqueTrue should be recorded as an opaque definition"
  | none => .error "opaqueTrue should be present in the environment"
  let opaqueTrueTy ← infer env [] opaqueTrue
  let _ ← checkDefEq env opaqueTrueTy boolType
  let opaqueTrueNf ← normalize env opaqueTrue
  let _ ← expectExprEq "opaque definitions do not unfold" opaqueTrueNf opaqueTrue
  let _ ← expectError "opaque definitions are not definitionally equal to their values" (checkDefEq env opaqueTrue boolTrue)
  match env.find? "Nat" with
  | some info =>
      match info.kind with
      | .inductive _ => pure ()
      | _ => .error "Nat should be recorded as an inductive type constructor"
  | none => .error "Nat should be present in the environment"
  match env.find? "Nat.rec" with
  | some info =>
      match info.kind with
      | .primitive (.recursor _ _) => pure ()
      | _ => .error "Nat.rec should be recorded as a primitive recursor"
  | none => .error "Nat.rec should be present in the environment"
  match env.find? "Quot.lift" with
  | some info =>
      match info.kind with
      | .primitive .quotLift => pure ()
      | _ => .error "Quot.lift should be recorded as a quotient primitive"
  | none => .error "Quot.lift should be present in the environment"
  match env.find? "Pair.fst" with
  | some info =>
      match info.kind with
      | .projection projection =>
          let _ ← expect "projection metadata records the structure" (projection.structName = "Pair")
          let _ ← expect "projection metadata records the constructor" (projection.ctorName = "Pair.mk")
          let _ ← expect "projection metadata records the field index" (projection.index = 0)
          pure ()
      | _ => .error "Pair.fst should be recorded as a projection"
  | none => .error "Pair.fst should be present in the environment"

def projectionTests : Result Unit := do
  let env ← sampleEnv
  let pairFstTy ← infer env [] (pairFst pairZeroTrue)
  let _ ← checkDefEq env pairFstTy natType
  let pairFstNf ← normalize env (pairFst pairZeroTrue)
  let _ ← expectExprEq "projection reduces on constructor targets" pairFstNf natZero
  let pairFstFnNf ← normalize env (pairFstFn pairZeroTrue)
  let _ ← expectExprEq "projection functions unfold to core projections" pairFstFnNf natZero
  let _ ← checkDefEq env pairEtaExpansion pairSeed
  let sigmaValueTy ← infer env [] (sigmaValueProj sigmaBoolTrue)
  let _ ← checkDefEq env sigmaValueTy boolType
  let sigmaValueNf ← normalize env (sigmaValueProj sigmaBoolTrue)
  let _ ← expectExprEq "dependent projection result types substitute earlier projections" sigmaValueNf boolTrue
  let _ ← checkDefEq env sigmaEtaExpansion sigmaSeed
  let proofProjectionTy ← infer env [] proofBoxProjection
  let _ ← checkDefEq env proofProjectionTy pProp
  let proofProjectionNf ← normalize env proofBoxProjection
  let _ ← checkDefEq env proofProjectionNf pProof
  let _ ←
    expectError
      "projection rejects extraction of data from Prop"
      (infer env [] dataWitnessPropProjection)
  let _ ←
    expectError
      "projection rejects invalid field indices"
      (infer env [] (.proj "Pair" 2 pairZeroTrue))
  let _ ←
    expectError
      "projection rejects mismatched major-premise types"
      (infer env [] (.proj "Pair" 0 boolTrue))
  let recStructSpec : InductiveSpec :=
    {
      name := "RecStruct"
      params := []
      level := type0Level
      ctors :=
        [
          { name := "RecStruct.mk", fields := [{ name := "child", type := const0 "RecStruct" }] }
        ]
    }
  let env ← addInductive env recStructSpec
  let env ← addProjection env "RecStruct.child" "RecStruct" 0
  let env ← addAxiom env "recStructSeed" (const0 "RecStruct")
  let recSeed := const0 "recStructSeed"
  let recEtaExpansion := Expr.mkApps (const0 "RecStruct.mk") [.proj "RecStruct" 0 recSeed]
  let recProjectionTy ← infer env [] (.proj "RecStruct" 0 recSeed)
  let _ ← checkDefEq env recProjectionTy (const0 "RecStruct")
  expectError
    "recursive single-constructor inductives do not use structure eta"
    (checkDefEq env recEtaExpansion recSeed)

def faithfulnessBridgeTests : Result Unit := do
  let env ← sampleEnv
  let polyIdBoolNf ← normalize env polyIdBool
  let _ ← expectExprEq "Lean accepts transparent universe-polymorphic computation" polyIdBoolNf boolTrue
  let polyIdTypeNf ← normalize env polyIdTypeArg
  let _ ← expectExprEq "Lean accepts universe-polymorphic computation at Type" polyIdTypeNf boolType
  let opaqueTrueTy ← infer env [] opaqueTrue
  let _ ← checkDefEq env opaqueTrueTy boolType
  let _ ← expectError "Lean rejects rfl through opaque definitions" (checkDefEq env opaqueTrue boolTrue)
  let natRecTy ← infer env [] natIsZeroOnOne
  let _ ← checkDefEq env natRecTy boolType
  let natRecNf ← normalize env natIsZeroOnOne
  let _ ← expectExprEq "Lean accepts primitive recursor computation" natRecNf boolFalse
  let eqRecTy ← infer env [] eqRecOnRefl
  let _ ← checkDefEq env eqRecTy boolType
  let eqRecNf ← normalize env eqRecOnRefl
  let _ ← expectExprEq "Lean accepts Eq.rec computation into data" eqRecNf boolFalse
  let quotientNf ← normalize env boolQuotLiftOnTrue
  let _ ← expectExprEq "Lean accepts Quot.lift computation on Quot.mk" quotientNf boolTrue
  let indexSingletonTy ← infer env [] indexSingletonRecOnZero
  let _ ← checkDefEq env indexSingletonTy natType
  let indexSingletonNf ← normalize env indexSingletonRecOnZero
  let _ ← expectExprEq "Lean accepts indexed singleton Prop elimination into data" indexSingletonNf natZero
  let mutEvenNf ← normalize env mutEvenRecOnTwo
  let _ ←
    expectExprEq
      "Lean accepts mutual inductive declarations"
      mutEvenNf
      (natSucc (natSucc natZero))
  let mutNestNf ← normalize env mutNestARecOnOne
  let _ ←
    expectExprEq
      "Lean accepts nested mutual inductive declarations"
      mutNestNf
      (natSucc (natSucc (natSucc natZero)))
  let badPositiveSpec : InductiveSpec :=
    {
      name := "BadPositive"
      params := []
      level := type0Level
      ctors :=
        [
          {
            name := "BadPositive.mk"
            fields := [{ name := "f", type := .forallE "x" (const0 "BadPositive") natType }]
          }
        ]
    }
  let badPolyBoxSpec : InductiveSpec :=
    {
      name := "BadPolyBox"
      levelParams := ["u"]
      params := [{ name := "α", type := .sort (.param "u") }]
      level := .param "u"
      ctors := []
    }
  let _ ←
    expectError
      "Lean rejects non-positive inductive occurrences"
      (addInductive env badPositiveSpec)
  let _ ←
    expectError
      "Lean rejects ambiguous Sort-valued inductive results"
      (addInductive [] badPolyBoxSpec)
  let _ ←
    expectError
      "Lean rejects multi-constructor Prop elimination into data"
      (infer env [] pOrRecToBool)
  let _ ←
    expectError
      "Lean rejects data-witness Prop elimination into data"
      (infer env [] dataWitnessPropRecToBool)
  let _ ←
    expectError
      "Lean rejects computed-index Prop elimination into data"
      (infer env [] shiftedIndexPropRecToBool)
  expectError
    "Lean rejects quotient relation mismatches"
    (normalize env boolQuotLiftRelationMismatch)

def rawEntryTests : Result Unit := do
  let env ← sampleEnv
  let _ ← expectError "normalization rejects recursor missing universe argument" (normalize env natRecMissingLevel)
  let _ ← expectError "normalization rejects recursor with extra universe arguments" (normalize env natRecExtraLevels)
  let _ ← expectError "inference rejects open universe arguments" (infer env [] (.const "Nat.rec" [.param "v"]))
  expectError "inference rejects open sort levels" (infer env [] (.sort (.param "u")))

def kernelRegressionTests : Result Unit := do
  let _ ← telescopeTests
  let _ ← universeTests
  let _ ← substitutionTests
  let _ ← generatedValidationTests
  let _ ← environmentTests
  let _ ← projectionTests
  let _ ← faithfulnessBridgeTests
  let _ ← rawEntryTests
  let _ ← demoReport
  pure ()

def testReport : Result (List String) := do
  let _ ← telescopeTests
  let _ ← universeTests
  let _ ← substitutionTests
  let _ ← generatedValidationTests
  let _ ← environmentTests
  let _ ← projectionTests
  let _ ← faithfulnessBridgeTests
  let _ ← rawEntryTests
  let _ ← demoReport
  pure
    [
      "telescope invariants check",
      "universe-polymorphism invariants check",
      "substitution invariants check",
      "generated declaration validation rejects malformed generated types",
      "environment declaration metadata checks",
      "projection typing, reduction, and eta checks",
      "faithfulness bridge checks local expressions against the Lean corpus",
      "raw inference and normalization entry points reject malformed primitives",
      "kernel example regressions check"
    ]

end LeanLean

def main : IO Unit := do
  match LeanLean.testReport with
  | .error err => throw <| IO.userError err
  | .ok lines =>
      for line in lines do
        IO.println line
