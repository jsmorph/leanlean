# MPC Nested Positivity Plan

## Purpose

The Omega stress fixture reaches the inductive `Lean.Syntax` and rejects its `node` constructor field `args : Array Syntax`.  That is a rule-package boundary in inductive admission.  Lean 4.29.1 defines `Array α` in `Init/Prelude.lean` as a structure whose proof-facing field is `toList : List α`, and `Lean.Syntax` in `Lean/Syntax.lean` uses `Array Syntax` in the recursive `node` constructor.

The first slice should add nested positivity through specified covariant containers.  It should not add a general higher-kinded positivity prover.  It should also not add tactic, syntax, or Omega-specific rules.

## Rule

A recursive occurrence of the inductive being admitted is strictly positive when it appears under a container constructor selected by the manifest, provided all recursive occurrences in the container's covariant argument positions are strictly positive and all other expression arguments contain no recursive occurrence.  The first supported container set is the Lean 4.29 `Array` and `List` unary type constructors.

This rule is source-backed but static.  `Array` is admitted because Lean's prelude specifies it as a proof-facing wrapper around `List`; `List` is admitted because its ordinary inductive declaration is positive in its element parameter.  The checker should require the container constant to exist in the environment before using the rule.  This keeps a misspelled or unavailable container from silently widening positivity.

The rule remains structural inside the container argument.  `Array Syntax` is positive.  `Array (Syntax -> Nat)` is rejected because the recursive occurrence is in a function domain inside the covariant argument.  `Array (Box Syntax)` is accepted only when the checker can prove the relevant `Box` parameter covariant from the admitted inductive declaration.

## Implementation

The manifest should name nested-container support separately from ordinary indexed inductives.  `MPC.Configs.LeanCore429` should enable the first Lean 4.29 container set, while `MPC.Configs.Poc` should keep the older direct-only behavior.

The positivity check should take the manifest and environment.  It should recognize applications headed by `Array` or `List` only when the manifest enables the package and the environment contains the corresponding container constant.  The existing direct occurrence and dependent-function rules should remain unchanged.

This first slice should not generate nested induction hypotheses.  The current generated-recursor audit checks that the recursor constant exists, not that its full stored artifact record matches.  If later exported declarations use a nested recursor with Lean's richer induction hypotheses, that failure should become the next recursor-generation task rather than being hidden inside positivity admission.

## Tests

Native tests should cover four cases.  First, a direct recursive field still works.  Second, `Array Good` is accepted only under the Lean 4.29 manifest with an admitted `Array` constant.  Third, the same declaration is rejected under the PoC manifest.  Fourth, `Array (Bad -> Nat)` is rejected even when nested-container support is enabled.

The Omega stress script should be rerun after the implementation.  Passing `Lean.Syntax` would not mean arbitrary nested inductives are complete; it would mean this first container-positivity boundary has moved to the next checked declaration or recursor-use boundary.
