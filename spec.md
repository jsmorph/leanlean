# Minimal Kernel Subset

This document specifies the first kernel subset for the project.  The goal is to define a small fragment that can be implemented cleanly in Lean 4 and that still exercises the central machinery around inductive types.  The subset is intentionally narrower than full Lean 4, because a serious proof of concept depends more on a precise boundary than on premature coverage claims.

The subset follows the shape of Lean's core language described in the Lean reference manual: a dependently typed lambda calculus whose basic terms include universes, function types, variables, constants, applications, and `let` bindings.  It also follows the reference manual's account of inductive declarations: user input provides a type constructor and constructors, while the kernel derives a recursor and the corresponding computation rules.  The implementation in this repository uses that model as guidance, but the specification below is authoritative for the project.

## Scope

The first subset covers transparent definitions, axioms, and single inductive declarations.  It supports parameters on inductive types, strictly positive constructor fields, generated recursor families, and the reduction rules required to compute through those recursors.  It excludes the parts of Lean 4 that would force a larger theory before the inductive fragment is stable, such as quotient types, mutual inductives, structure projections, proof irrelevance, indices, and general user-declared universe polymorphism.

The subset remains a data fragment.  Inductive result universes are predicative and closed, and the implementation still omits `Prop`.  The term language nevertheless carries explicit universe arguments on constants, because generated recursors need a motive universe parameter in order to exist as ordinary primitive constants rather than as a typing special case.

## Terms and Declarations

Expressions have seven forms: bound variables, sorts, constants, application, lambda abstraction, dependent function types, and `let` bindings.  Bound variables use de Bruijn indices.  Constants carry explicit universe instantiations, and the environment stores the corresponding level-parameterized primitive types.  A constant application is well formed only when its universe instantiation has the arity prescribed by the declaration and each supplied level is closed.  User-facing declarations in the first subset remain closed and monomorphic, but generated recursors introduce a controlled use of level parameters inside the kernel.

The environment admits three user-facing declarations.  An axiom adds a closed constant with a closed type.  A definition adds a closed constant with a closed type and a closed value whose inferred type is definitionally equal to the declared type.  An inductive declaration adds a type constructor, one constant for each constructor, and a family of primitive recursors.

## Inductive Fragment

An inductive declaration introduces exactly one inductive type in the first subset.  The declaration may bind parameters, but it may not bind indices.  Each constructor field type is checked in the parameter context, which means field types may depend on parameters but not on earlier constructor fields.

The result universe of an inductive type remains explicit in the first subset, but the kernel checks it instead of trusting it.  When an inductive declaration has constructors, the universe of each parameter type and each constructor field type must be no larger than the declared result universe.  Constructorless inductives remain exempt from that bound, matching the fact that they introduce no constructor arguments whose types must live inside the resulting sort.

Recursive occurrences must be strictly positive.  A recursive occurrence may not appear to the left of an arrow.  It may appear in the codomain of an arrow, producing function-valued induction hypotheses, and it may appear as an argument to another inductive type constructor only when the corresponding parameter of that inductive has already been established as positive.  This makes the positivity check compositional across earlier inductive declarations: `List Tree` is accepted because `List` is positive in its element parameter, while a type such as `BadParam Tree`, where the parameter occurs negatively inside `BadParam`, is rejected.  The kernel analyzes constructor field types after beta, delta, and zeta normalization to a canonical term, so local `let` bindings and reducible abbreviations do not change whether a field is accepted.  Nested helper targets in the current subset must depend only on the inductive parameters.  Shapes such as `(n : Nat) → WrapAt n Tree`, whose nested target carries a local binder, remain outside the subset.

The kernel derives a family of primitive recursors from the inductive type and the strictly positive types reachable from its constructor fields.  The primary recursor eliminates the inductive type itself.  Helper recursors eliminate nested positive types such as `List Tree`, sharing the same parameters, motives, and minor premises as the primary recursor.  The family builder canonicalizes those reachable target types before comparing them, so definitionally equal nested targets yield one helper recursor rather than parallel duplicates.  Each recursor carries one explicit universe parameter for the common motive sort.  Each constructor contributes one minor premise, and each strictly positive recursive field contributes an induction-hypothesis argument whose shape follows the field: direct recursive fields contribute a direct hypothesis, function-valued fields contribute a function of hypotheses, and nested inductive fields contribute a hypothesis through the corresponding helper recursor.  A saturated recursor application reduces by iota when its target reduces to a constructor application of the corresponding target type and the constructor's parameter arguments are definitionally equal to the recursor's explicit parameters.

## Conversion and Typing

Typing follows the ordinary rules for a dependently typed lambda calculus.  `Sort u` has type `Sort (u + 1)`, and a dependent function type `∀ x : A, B` lives in `Sort (max u v)` when `A : Sort u` and `B : Sort v`.  Primitive recursors type-check through those same ordinary rules once their explicit universe argument is supplied, because the kernel now stores them as ordinary constants with ordinary dependent function types.  Conversion uses normalization-based definitional equality in the first implementation.

The conversion relation includes beta, delta, zeta, and iota reduction.  Beta reduction substitutes an argument into a lambda body.  Delta reduction unfolds transparent definitions.  Zeta reduction substitutes the bound value of a `let`.  Iota reduction applies a saturated recursor case to a constructor target and recursively computes the induction hypotheses for recursive fields.  Unsaturated recursor constants do not reduce, but they still type-check as ordinary constants.

## Deliberate Omissions

| Feature | Status in first subset | Reason |
| --- | --- | --- |
| General user-declared universe polymorphism | Omitted | The subset admits only closed inductive universes and a single generated motive level parameter on primitive recursors. |
| Binder-dependent nested helper targets | Omitted | They require helper recursors whose target family carries a local telescope rather than only the inductive parameters. |
| `Prop`, proof irrelevance, and large elimination | Omitted | They change both conversion and recursor formation. |
| Quotients | Omitted | They add a primitive type former and an additional reduction rule. |
| Mutual inductives | Omitted | They enlarge the positivity and recursor-generation rules immediately. |
| Constructor field dependencies and indices | Omitted | They require a more general inductive-family specification. |

These omissions are not placeholders for undocumented behavior.  The kernel either implements a feature or rejects it.  Later versions can enlarge the specification once the current fragment has stable examples, tests, and a clearer path toward universes and propositions.
