# Minimal Kernel Subset

This document specifies the first kernel subset for the project.  The goal is to define a small fragment that can be implemented cleanly in Lean 4 and that still exercises the central machinery around inductive types.  The subset is intentionally narrower than full Lean 4, because a serious proof of concept depends more on a precise boundary than on premature coverage claims.

The subset follows the shape of Lean's core language described in the Lean reference manual: a dependently typed lambda calculus whose basic terms include universes, function types, variables, constants, applications, and `let` bindings.  It also follows the reference manual's account of inductive declarations: user input provides a type constructor and constructors, while the kernel derives a recursor and the corresponding computation rules.  The implementation in this repository uses that model as guidance, but the specification below is authoritative for the project.

## Scope

The first subset covers transparent definitions, axioms, and single inductive declarations.  It supports parameters on inductive types, direct recursive constructor fields, generated recursors, and the reduction rules required to compute through those recursors.  It excludes the parts of Lean 4 that would force a larger theory before the inductive fragment is stable, such as quotient types, mutual inductives, nested inductives, structure projections, proof irrelevance, and universe polymorphism.

The subset is a data fragment.  Universes are predicative and closed: terms may mention `Sort u` for concrete natural-number levels `u`, and the first implementation does not quantify over universe levels.  This restriction leaves the type checker small enough to inspect while preserving the main questions about constructor formation, recursor generation, and iota reduction.

## Terms and Declarations

Expressions have seven forms: bound variables, sorts, constants, application, lambda abstraction, dependent function types, and `let` bindings.  Bound variables use de Bruijn indices.  Constants refer to entries in a global environment, and the environment contains only closed declarations.

The environment admits three user-facing declarations.  An axiom adds a closed constant with a closed type.  A definition adds a closed constant with a closed type and a closed value whose inferred type is definitionally equal to the declared type.  An inductive declaration adds a type constructor, one constant for each constructor, and one primitive recursor.

## Inductive Fragment

An inductive declaration introduces exactly one inductive type in the first subset.  The declaration may bind parameters, but it may not bind indices.  Each constructor field type is checked in the parameter context, which means field types may depend on parameters but not on earlier constructor fields.

Recursive occurrences are restricted to direct fields whose normalized type is the inductive type applied to the current parameters.  This rule enforces a simple strict-positivity discipline by construction: the inductive type may appear as a field, but it may not appear to the left of an arrow or under another type former.  The first subset therefore supports declarations such as `Nat`, `Bool`, `List α`, and first-order trees, while rejecting nested or indexed families.

The kernel derives one recursor from the inductive type and its constructors.  The recursor is primitive, not a defined constant.  Each constructor contributes one minor premise, and each recursive constructor field contributes one induction-hypothesis argument to that minor premise.  A saturated recursor application reduces by iota when its target reduces to a constructor application of the same inductive type.

## Conversion and Typing

Typing follows the ordinary rules for a dependently typed lambda calculus.  `Sort u` has type `Sort (u + 1)`, and a dependent function type `∀ x : A, B` lives in `Sort (max u v)` when `A : Sort u` and `B : Sort v`.  Conversion uses normalization-based definitional equality in the first implementation.

The conversion relation includes beta, delta, zeta, and iota reduction.  Beta reduction substitutes an argument into a lambda body.  Delta reduction unfolds transparent definitions.  Zeta reduction substitutes the bound value of a `let`.  Iota reduction applies a recursor case to a constructor target and recursively computes the induction hypotheses for recursive fields.

The first implementation uses saturated recursor applications as the primitive interface for elimination.  That choice keeps the typing and reduction rules explicit, because the result type comes directly from the motive and target.  Constructor constants remain ordinary curried constants, so parameterized data still behaves like a small dependently typed core language rather than a custom evaluator for a handful of examples.

## Deliberate Omissions

| Feature | Status in first subset | Reason |
| --- | --- | --- |
| Universe polymorphism | Omitted | It requires a separate level language and comparison procedure. |
| `Prop`, proof irrelevance, and large elimination | Omitted | They change both conversion and recursor formation. |
| Quotients | Omitted | They add a primitive type former and an additional reduction rule. |
| Mutual and nested inductives | Omitted | They enlarge the positivity and recursor-generation rules immediately. |
| Constructor field dependencies and indices | Omitted | They require a more general inductive-family specification. |

These omissions are not placeholders for undocumented behavior.  The kernel either implements a feature or rejects it.  Later versions can enlarge the specification once the current fragment has stable examples, tests, and a clearer path toward universes and propositions.
