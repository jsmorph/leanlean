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
  let a : Binder := { name := "A", type := .sort 0 }
  let x : Binder := { name := "x", type := .bvar 0 }
  let y : Binder := { name := "y", type := .bvar 0 }
  let _ ← expect "telescope context order is innermost first" (Telescope.toContext [a, x] = [x, a])

  let dependentActual := Telescope.bindForall [a, x] (.bvar 0)
  let dependentExpected := .forallE "A" (.sort 0) (.forallE "x" (.bvar 0) (.bvar 0))
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
  let _ ← substitutionTests
  let _ ← generatedValidationTests
  let _ ← rawEntryTests
  let _ ← demoReport
  pure ()

def testReport : Result (List String) := do
  let _ ← telescopeTests
  let _ ← substitutionTests
  let _ ← generatedValidationTests
  let _ ← rawEntryTests
  let _ ← demoReport
  pure
    [
      "telescope invariants check",
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
