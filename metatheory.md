# Metatheoretic Account

This document states the mathematical account that the current checker is meant to implement.  It is not a mechanized proof.  Its purpose is to name the judgments, invariants, and proof obligations that a later paper or formalization must discharge.

## Core Judgments

The core typing judgment has the form `E; U; Γ ⊢ e : A`, where `E` is a checked environment, `U` is the active universe-parameter context, and `Γ` is an innermost-first term context.  The well-formedness judgment for environments says that every admitted declaration has a closed type under its declared universe parameters, every stored value checks against its declared type, and every generated or primitive declaration has passed the same checking boundary as user declarations.  The conversion judgment `E; U; Γ ⊢ e ≡ e' : A` is implemented by normalization plus proof irrelevance, and every reduction rule must preserve typing under the same environment, universe context, and term context.

The level judgment has the form `U ⊢ ℓ`, meaning that every level parameter in `ℓ` belongs to `U`.  Level equality is equality after normalization of `max`, `imax`, and successor expressions.  The intended universe soundness theorem says that if `E; U; Γ ⊢ e : Sort ℓ`, then `U ⊢ ℓ` and every universe level appearing in `e` is closed under `U`.

The substitution judgment follows the context convention in the specification.  If `Γ` is innermost first and a source telescope is outermost first, then binding and instantiation must be mutual inverses up to de Bruijn shifting.  The key lemma is simultaneous-substitution preservation: substituting a well-typed list of values for a telescope preserves typing and avoids capture under every binder.

## Typing And Conversion

Type preservation for reduction is the first central theorem.  If `E; U; Γ ⊢ e : A` and `e` reduces by beta, delta, zeta, iota, projection, natural-literal, quotient, or eta reduction to `e'`, then `E; U; Γ ⊢ e' : A`.  The theorem depends on declaration soundness for delta reduction, recursor soundness for iota reduction, projection soundness for projection reduction, and quotient primitive soundness for `Quot.lift`.

Conversion soundness follows preservation.  If the checker accepts `e ≡ e'` at type `A`, then both expressions must have type `A`, and replacing one by the other in any well-typed expression preserves typing.  Proof irrelevance adds one extra premise: the two compared proof terms must infer the same normalized proposition type before the conversion rule applies.

The implementation uses normalization-based conversion.  A paper proof can state confluence and decidability only for the specified fragment, because the implementation does not attempt to cover arbitrary Lean 4 environment data.  For the implemented fragment, the required argument is that every reduction rule either structurally decreases the expression, unfolds a previously checked transparent definition, or applies a primitive computation rule with checked side conditions.

## Universes

Universe checking has two parts: closure and level ordering.  Closure ensures that constants, declaration bodies, inductive result levels, and generated declarations mention only declared universe parameters.  Level ordering ensures that a data-valued inductive constructor field after the shared parameters does not live above the inductive result universe.

`Prop` requires a separate argument.  The function-sort rule uses `imax`, so dependent functions into `Prop` remain propositions while functions into data remain in a data universe.  Proposition-valued inductives do not use the data-field universe bound, because their constructor fields affect eliminator admissibility rather than the sort of constructed data.

Sort-polymorphic subsingletons form a narrow exception.  Empty sort-polymorphic inductives and one-constructor no-field sort-polymorphic inductives can live at `Sort u` without permitting data extraction from `Prop`.  The metatheoretic obligation is to prove that this exception cannot encode a computational witness when `u = 0`.

## Inductives And Positivity

The positivity theorem says that every accepted inductive block has strictly positive recursive occurrences under the declared parameter discipline.  Direct recursive occurrences may appear only in positive positions, and nested recursive occurrences may pass through an earlier inductive parameter only when that parameter has been proved positive.  The joint fixed point for mutual blocks must be monotone, and the accepted block must be a post-fixed point of the positivity operator.

Dependent constructor fields add a substitution obligation.  Later field types and constructor targets may mention earlier fields, so positivity and universe checking operate over the same field telescope used by typing.  Normalizing field types before positivity analysis must preserve the positivity result, because reducible syntax must not change whether a declaration is accepted.

Large elimination from `Prop` has its own soundness condition.  A proposition-valued inductive may eliminate into data only when it has no constructors, or when it has one constructor whose fields are propositions or values forced by whole target indices.  The proof obligation is that every permitted data result is determined without inspecting an arbitrary proof-relevant field.

## Generated Recursors

For each accepted inductive block, the recursor-generation theorem states that every generated recursor type is well formed in the environment extended by the block's type formers and constructors.  The generated family includes one target for each block member and one target for each canonical nested helper schema.  The helper-target construction must preserve levels, parameters, local telescopes, and constructor target indices.

The minor-premise theorem states that each constructor contributes one minor premise for each reachable target, binding helper locals first, constructor fields in telescope order second, and induction hypotheses in field order third.  The type of each induction hypothesis follows the shape of the corresponding recursive field.  Recursive fields at root targets, function-valued recursive fields, and nested inductive fields therefore need separate cases in the proof.

The iota theorem states that a saturated recursor application computes only when the eliminated target reduces to a constructor application whose universe arguments, parameters, and target indices match the instantiated recursor target.  After the side conditions hold, the reduced term is the selected minor premise applied to constructor fields and recursively computed induction hypotheses.  Preservation for iota reduction follows from the generated recursor type theorem and the simultaneous-substitution theorem.

## Projections And Quotients

Projection soundness states that projecting field `i` from a one-constructor inductive value returns a term whose type is the selected constructor field type after substituting parameters, target indices, and earlier projections.  Fields forced by whole target indices are not projectable, and computed-index fields remain projectable because their values are not recoverable from a whole target index.  Projection reduction preserves typing because constructor fields occupy fixed positions after the shared parameters.

Structure eta is intentionally narrow.  The eta theorem applies only to non-recursive, data-valued, one-constructor inductives in the supported projection fragment, and only when the constructor target matches the inferred structure type.  The proof obligation is to show that rebuilding the constructor from projections preserves every projectable field and every index-forced field.

Quotient soundness is limited to the low-level primitive API.  `Quot.lift` may reduce on `Quot.mk` only after checking that the eliminator and constructor use the same quotient universe, underlying type, and relation.  `Quot.sound` supplies equality in the quotient, while `Quot.ind` eliminates only into propositions in this subset.

## Environment Replay

Environment soundness says that replaying a declaration script preserves well-formedness.  Ordered replay follows directly from the admission theorem for each declaration form.  Dependency-aware replay adds the obligation that a declaration is admitted only after every external dependency has already entered the environment, while names defined by the same mutual inductive block may be used inside that block.

Generated-declaration replay is a comparison theorem.  A generated constructor or recursor entry from Lean does not add a new constant; it must match the declaration regenerated by the local checker, up to alpha-equivalence of binders and universe parameter names.  Recursor metadata comparison also checks block members, parameter counts, index counts, motive counts, minor-premise counts, constructor rule headers, and rule right-hand sides.

Lean import soundness has a narrower statement than full Lean 4 kernel equivalence.  The importer translates safe Lean declaration data, finite `ConstantInfo` snapshots, root-name closures, and kernel-relevant structure metadata into local declaration scripts, then uses ordinary replay.  Recursive-definition artifacts, unsafe declarations, unsupported sort-polymorphic inductives, incomplete snapshots, malformed structure metadata, and unknown names are rejected before admission, so they do not enter the trusted theorem.

## Proof Obligations

| Obligation | Current evidence | Missing proof work |
| --- | --- | --- |
| Substitution preservation | `substitutionTests`, `telescopeTests`, generated recursor regressions. | Induction over expressions with simultaneous substitution under binders. |
| Subject reduction for conversion | `kernelRegressionTests`, `projectionTests`, `literalTests`, quotient regressions. | Case proof for every reduction rule, including proof irrelevance and eta. |
| Universe soundness | `universeTests`, inductive universe regressions, broad replay over core roots. | Lemmas for `imax`, data-field bounds, and sort-polymorphic subsingletons. |
| Positivity soundness | Rejected positivity corpus, nested-parameter rejection, mutual and nested mutual tests. | Monotonicity proof for the positive-parameter fixed point and a strict-positivity theorem for accepted blocks. |
| Recursor correctness | Generated-declaration validation, recursor metadata replay, differential recursor terms. | Derivation of generated recursor types and iota preservation for every reachable target shape. |
| Projection and structure soundness | Projection regressions, structure metadata replay, inherited-field smoke tests. | Preservation proof for dependent projections, parent projections, and the current eta rule. |
| Quotient primitive soundness | Quotient regression tests and rejected relation mismatch. | Axiomatized quotient model and proof that the single computation rule respects the relation side condition. |
| Environment replay soundness | Declaration replay tests, importer bridge tests, importer smoke, broad differential replay. | Induction over dependency-aware replay and a theorem connecting Lean import translation to local declaration scripts. |
| Lean faithfulness for named fragments | Source corpus, importer smoke, term differentials, broad fragment differentials. | A precise theorem stating the named fragment, the translation relation, and the conditions under which Lean and the local checker agree. |
