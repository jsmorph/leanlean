# MPC Function Eta Plan

## Purpose

Function eta should enter MPC as a named conversion package.  Lean conversion identifies a function with a lambda that applies that function to the newly bound variable, provided the compared term has a dependent-function type with the same domain.  The rule matters for exported proofs because elaboration and compiler output can choose either representation while relying on the kernel to compare them.

## Boundary

The package is selected by the manifest and affects only definitional equality.  It does not add an expression form, a declaration form, or a reduction rule to weak-head normalization.  The checker should try eta after ordinary structural conversion fails and before proof irrelevance, because eta requires type inference for the non-lambda side and recursive conversion for the lambda body.

The rule compares `λ x : A, body` with a term `f` by inferring the type of `f`, reducing that type to a function type, comparing `A` with the inferred domain, and comparing `body` with `f` lifted under the binder and applied to `x`.  The rule should run in both directions, since either side of a failed structural comparison can be the eta-expanded lambda.  It should use the existing context and universe parameter context, so interactions with primitive reductions, projections, equality, and proof irrelevance remain ordinary conversion calls rather than special cases.

## Tests

The first fixture should compare an axiom `f : Nat -> Nat` with `fun x : Nat => f x`, while showing that the base PoC rejects the same equality.  A second fixture should combine function eta with the natural primitive package by comparing `fun x : Nat => Nat.add x 1` with `Nat.succ`.  That second case confirms that eta delegates body comparison to the configured conversion relation instead of doing a syntactic application check.
