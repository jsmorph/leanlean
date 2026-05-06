# MPC Metatheory

## Purpose

This document states the proof obligations for MPC.  It is a mathematical account of the checker described by [MPC Specification](spec.md), not a mechanized proof.  It also records which obligations belong to MPC and which belong to adapters such as the `lean4export` NDJSON checker.

MPC checks canonical declarations under a manifest.  The central theorem is therefore a preservation theorem for checked environments: replaying a declaration script with a valid manifest preserves environment well-formedness.  Artifact claims require an additional adapter theorem showing that the artifact was translated into the canonical declaration script that MPC checked.

## Judgments

The typing judgment has the form `E; U; Γ ⊢ e : A`.  `E` is a checked environment, `U` is the active universe-parameter context, and `Γ` is an innermost-first term context.  Environment well-formedness says that every constant has a closed type under its declared universe parameters, every stored value checks against that type, and every generated or primitive constant satisfies the rule that introduced it.

The conversion judgment has the form `E; U; Γ ⊢ e ≡ e'`.  MPC implements it by alpha-equivalence, weak-head reduction, structural comparison with recursive conversion, and the enabled fallback rules for structure eta, proof irrelevance, and function eta.  Every conversion rule must preserve typing under the same environment, universe context, and term context.

The level judgment has the form `U ⊢ ℓ`.  It means that every level parameter in `ℓ` belongs to `U`.  Level comparison must be sound for the symbolic `max` and `imax` equations used by sort inference, constant instantiation, and inductive universe checks.

## Environment Soundness

The environment theorem says that `addDecl m E d = E'` preserves well-formedness when `m` is a valid manifest and `E` is well formed.  Each declaration form has its own case: axioms require a type whose type is a sort, definitions and opaque declarations require a checked value, theorems require a proposition type and proof, inductives generate checked constants, and primitive packages install only their specified constants.  Ordered replay follows by induction over the declaration list.

Generated inductive constants are not assumptions.  Constructor and recursor constants enter the environment because inductive admission derives their types and metadata from the accepted declaration.  A generated record in an external artifact is redundant audit data, so it can support an adapter theorem but not an environment-growth theorem.

Duplicate names are rejected.  The environment stores chronological entries and a name index, and the metatheory treats lookup as a functional map from names to checked constants.  The index is a performance representation, so the representation invariant is that indexed lookup returns the same constant as a search through the chronological entries.

## Substitution

The substitution theorem states that simultaneous substitution preserves typing.  Source telescopes are outermost first, runtime contexts are innermost first, and `Expr.instantiateMany` substitutes source-order values into the corresponding exposed binders without capture.  This theorem is used by beta reduction, zeta reduction, lambda checking against expected function types, constructor-field instantiation, projection typing, recursor type generation, and recursor iota reduction.

Context lookup has its own preservation lemma.  If binder `i` is present in an innermost-first context, lookup returns its stored type lifted by `i + 1` into the current context.  Without that lift, generated dependent recursor binders and projection field types can appear well scoped in the source telescope while becoming ill scoped during checking.

## Reduction and Conversion

Subject reduction is the core conversion theorem.  If `E; U; Γ ⊢ e : A` and `e` takes one weak-head reduction step to `e'`, then `E; U; Γ ⊢ e' : A`.  The reduction cases are beta, zeta, delta for transparent definitions, projection reduction, inductive iota reduction, equality-rec reduction, quotient-lift reduction, natural-literal recursor reduction, and the selected primitive Nat reductions.

Conversion soundness follows from subject reduction and the soundness of the fallback rules.  If conversion accepts `e` and `e'`, then replacing one by the other in a well-typed expression preserves typing.  Proof irrelevance requires both terms to have definitionally equal proposition types, function eta requires an inferred dependent-function type for the non-lambda side, and structure eta requires the supported one-constructor projection fragment.

Termination and decidability are fragment obligations, not current theorems.  Transparent delta reduction can unfold only checked definitions, and primitive reductions have checked side conditions, but broad Lean-generated proof terms can still expose performance and resource questions.  A complete account must either prove termination for the manifest fragment or specify classified resource failures that preserve soundness by rejecting rather than accepting.

## Universes and Prop

Universe soundness says that if `E; U; Γ ⊢ e : Sort ℓ`, then `U ⊢ ℓ`, and every universe level appearing in `e` is closed under `U`.  The level comparison proof must cover `max` summand normalization, partial `imax` reduction, symbolic `imax` equalities, and the ordering facts used by inductive universe bounds.  Declaration admission depends on the same theorem for closed types, values, generated constructors, generated recursors, and primitive declarations.

`Prop` adds separate obligations because it changes both sorts and conversion.  The function-sort rule sends dependent functions into `Prop` back to `Prop`, theorem admission requires proposition types, and proof irrelevance adds a conversion rule.  Proposition-valued inductives also depend on `Prop`, because their recursors may be restricted to proposition motives unless the large-elimination rule applies.

Large elimination from `Prop` needs a subsingleton argument.  MPC currently admits data elimination only for conservative shapes whose constructor fields are propositions or fields forced by whole target indices.  The proof obligation is that an eliminated proof cannot reveal computational information beyond what the target indices already determine.

## Inductives

Inductive soundness starts with strict positivity.  A recursive occurrence may appear only in positive positions, and a nested recursive occurrence may pass through a container only when the relevant container argument is covariant.  The covariance fixed point for admitted containers must be monotone, and index arguments of indexed families must remain non-positive.

Constructor checking and recursor generation share the same telescope discipline.  Constructor field types and constructor targets may mention earlier fields, so the positivity, universe, target-shape, and recursor-generation proofs must operate under the same dependent field telescope.  Normalizing field types for analysis must preserve typing and must not change the accepted positivity class.

For every accepted inductive declaration or mutual block, generated recursor types must be well formed in the environment extended by the type formers and constructors.  The recursor family has one target for each block member and one target for each discovered nested helper schema.  Helper targets must preserve universe levels, parameters, local telescopes, target indices, and covariance assumptions.

Iota preservation says that a saturated recursor application reduces only after the major premise reduces to a constructor application for the selected target.  The reducer must check the recursor prefix, constructor field counts, parameters, indices, and metadata before selecting a minor premise.  The resulting term is well typed because the minor-premise type was generated from the same constructor telescope and recursive-field analysis.

## Projections, Equality, and Quotients

Projection soundness says that `proj S i target` has the selected constructor field type after substituting structure parameters and earlier projections from `target`.  Projection reduction preserves typing because a constructor-headed target contains fields in the same order used by the projection type.  Prop projection restrictions and structure eta belong to the same proof fragment, since both rely on the supported one-constructor structure shape.

Equality primitives require a preservation theorem for `Eq.rec`.  A redex whose proof reduces to `Eq.refl` returns the minor premise at the reflexive endpoint, and the K-style endpoint case requires the endpoints to be definitionally equal before the same reduction applies during conversion.  The proof obligation is to show that the motive instantiation after reduction matches the declared result type.  Endpoint conversion may use proof irrelevance, which matters for structures such as `Fin` whose equality can depend on proof fields.  `Eq.ndrec` is an ordinary transparent definition over `Eq.rec`, so its metatheoretic obligation belongs to definition checking and delta reduction rather than a second primitive eliminator.

Quotient soundness is limited to the low-level primitive API.  The `Quot.lift` reduction rule may fire only when the quotient type, relation, target type, representative function, respectfulness proof, and constructor arguments have the specified shape.  `Quot.sound` supplies equality in the quotient, and `Quot.ind` eliminates only into propositions in the current package.

## Adapter Theorems

An adapter theorem has the form: if an external artifact accepts, then the adapter produced a canonical MPC declaration script, MPC replay accepted that script under the chosen manifest, and every artifact-specific audit passed.  For NDJSON exports, the audit checks generated constructor and recursor records against the environment produced by replay.  The translation theorem must also cover primitive export records and name encoding, because those records determine which canonical declarations MPC receives.

Name translation must be injective.  Lean names with quoted components, numeric components, private structure, or dotted string components cannot rely on `Name.toString` as a unique key.  The export adapter therefore uses an encoded representation for names outside the ordinary subset, and the metatheoretic obligation is that distinct Lean names lower to distinct MPC names.

Checked-layer reuse needs a replay-refinement theorem.  If a layer reuses a declaration, the reused environment entry must be the same declaration content up to alpha-equivalence, or the same lowered content key that was previously checked.  A cache hit may skip work, but it must reconstruct the same environment that cold replay would have produced for the reused prefix.

## Evidence and Missing Proofs

| Obligation | Current evidence | Missing proof work |
| --- | --- | --- |
| Environment preservation | `MPCTest.lean` declaration, replay, package, and checked-layer tests; export fixture acceptance. | Induction over `addDecl` cases and generated environment entries. |
| Substitution preservation | Native substitution, telescope, projection, and recursor fixtures in `MPCTest.lean`. | Induction over expressions with simultaneous substitution and binder lifting. |
| Subject reduction | Native reduction tests for beta, zeta, delta, literals, projections, equality, quotients, primitive Nat, and inductive recursors. | Case proof for every enabled weak-head reduction. |
| Conversion soundness | Native tests for alpha equality, proof irrelevance, function eta, structure eta, and proof-heavy export replay. | Proof that fallback conversion rules preserve typing and compose with weak-head structural comparison. |
| Universe soundness | Native universe-comparison tests and export self-check of `MPC.Level`. | Lemmas for symbolic `imax`, inductive universe bounds, and sort-polymorphic subsingletons. |
| Positivity soundness | Native accepted and rejected inductive fixtures, nested-container fixtures, and mutual block fixtures. | Monotonicity proof for covariance inference and strict-positivity theorem for accepted blocks. |
| Recursor correctness | Native simple, indexed, nested, Prop, large-elimination, and mutual recursor tests; generated export audits. | Derivation of generated recursor types and iota preservation for each target shape. |
| Projection soundness | Native dependent projection, Prop projection, and structure-eta tests; export replay through projection-heavy dependencies. | Preservation proof for dependent projections and the current structure eta rule. |
| Equality and quotient soundness | Native equality and quotient primitive tests plus generated export replay. | Primitive model for equality and quotients, including motive substitution for equality recursors and the `Quot.lift` side conditions. |
| Adapter faithfulness | `tools/mpc-export-tests.sh`, `tools/mpc-export-gcd.sh`, self-check exports, name-encoding tests, and generated-record audits. | Formal translation theorem from accepted artifact records to canonical MPC declarations and audit obligations. |
| Cache refinement | Native checked-layer alpha-reuse tests and SQLite cache self-check workflow. | Proof that cache replay reconstructs the same accepted environment as cold replay for reused declarations. |
| Resource behavior | Profiling and timeout drivers in `perf.md` and `tools/mpc-omega-stress.sh`. | Classified resource-failure theorem that rejects on exhaustion instead of accepting unchecked results. |
