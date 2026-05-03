import Lean

namespace LeanLeanFaithfulness.Runner

inductive Expectation where
  | accepts
  | rejects : List String → Expectation

structure Case where
  label : String
  path : String
  expectation : Expectation

def cases : List Case :=
  [
    {
      label := "accepted core Lean fragment"
      path := "Faithfulness/Accepted.lean"
      expectation := .accepts
    },
    {
      label := "strict positivity rejection"
      path := "Faithfulness/Rejected/BadPositive.lean"
      expectation := .rejects ["non positive occurrence"]
    },
    {
      label := "ambiguous Sort-valued inductive rejection"
      path := "Faithfulness/Rejected/BadSortUniverse.lean"
      expectation := .rejects ["Invalid universe polymorphic resulting type", "Sort u"]
    },
    {
      label := "data-witness Prop elimination rejection"
      path := "Faithfulness/Rejected/DataWitnessPropElim.lean"
      expectation := .rejects ["expected to have type", "Prop"]
    },
    {
      label := "computed-index eta rejection"
      path := "Faithfulness/Rejected/ComputedIndexEta.lean"
      expectation := .rejects ["has type", "is expected to have type"]
    },
    {
      label := "theorem type rejection"
      path := "Faithfulness/Rejected/TheoremTypeNotProp.lean"
      expectation := .rejects ["type of theorem", "is not a proposition"]
    },
    {
      label := "opaque rfl rejection"
      path := "Faithfulness/Rejected/OpaqueRfl.lean"
      expectation := .rejects ["opaqueTrue = true"]
    },
    {
      label := "invalid projection index rejection"
      path := "Faithfulness/Rejected/InvalidProjectionIndex.lean"
      expectation := .rejects ["Invalid projection", "Index `3` is invalid"]
    },
    {
      label := "multi-constructor Prop data elimination rejection"
      path := "Faithfulness/Rejected/POrDataElim.lean"
      expectation := .rejects ["expected to have type", "Prop"]
    },
    {
      label := "Prop data projection rejection"
      path := "Faithfulness/Rejected/PropDataProjection.lean"
      expectation := .rejects ["Invalid projection", "Cannot project a value of non-propositional type"]
    },
    {
      label := "quotient relation mismatch rejection"
      path := "Faithfulness/Rejected/QuotRelationMismatch.lean"
      expectation := .rejects ["Quot relEq", "Quot relTrue"]
    },
    {
      label := "computed-index Prop elimination rejection"
      path := "Faithfulness/Rejected/ShiftedIndexPropElim.lean"
      expectation := .rejects ["expected to have type", "ShiftedIndexProp", "Prop"]
    }
  ]

def getLeanCommand : IO String := do
  match ← IO.getEnv "LEANLEAN_LEAN" with
  | some lean => pure lean
  | none => pure "lean"

def outputText (output : IO.Process.Output) : String :=
  output.stdout ++ output.stderr

def runCase (lean : String) (c : Case) : IO Unit := do
  let output ← IO.Process.output { cmd := lean, args := #[c.path] }
  match c.expectation with
  | .accepts =>
      if output.exitCode == 0 then
        IO.println s!"accept: {c.label}"
      else
        throw <| IO.userError s!"{c.label}: expected Lean to accept {c.path}\n{outputText output}"
  | .rejects needles =>
      if output.exitCode == 0 then
        throw <| IO.userError s!"{c.label}: expected Lean to reject {c.path}"
      else
        let text := outputText output
        let missingNeedles := needles.filter (fun needle => !text.contains needle)
        match missingNeedles with
        | [] => IO.println s!"reject: {c.label}"
        | _ =>
            throw <| IO.userError
              s!"{c.label}: Lean rejected {c.path}, but the output did not contain {repr missingNeedles}\n{text}"

def run : IO Unit := do
  let lean ← getLeanCommand
  for c in cases do
    runCase lean c

end LeanLeanFaithfulness.Runner

def main : IO Unit :=
  LeanLeanFaithfulness.Runner.run
