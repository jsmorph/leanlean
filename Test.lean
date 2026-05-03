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
  let _ ←
    expectError
      "subsingleton Prop inductive recursors require motive universe arguments"
      (infer env [] (const0 "PTrue.rec"))
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
  let _ ← rawEntryTests
  let _ ← demoReport
  pure ()

def testReport : Result (List String) := do
  let _ ← telescopeTests
  let _ ← universeTests
  let _ ← substitutionTests
  let _ ← generatedValidationTests
  let _ ← rawEntryTests
  let _ ← demoReport
  pure
    [
      "telescope invariants check",
      "universe-polymorphism invariants check",
      "substitution invariants check",
      "generated declaration validation rejects malformed generated types",
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
