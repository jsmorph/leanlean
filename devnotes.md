# Development Notes

This file records sources, rationale, and small plans for the project.  The references below came from the user on 2026-05-02.  They now inform the first specification draft and the initial implementation boundary.  The project remains spec-driven, so the references guide scope and terminology without substituting for the local specification.

## Scope and Rationale

This effort is spec-driven.  It does not derive a Lean kernel in Lean from the Lean 4 sources, and it does not treat the current Lean 4 implementation as a substitute for a specification.  Drafting the specification is therefore a major part of the work, not a preliminary formality.

The first implementation target is a small data fragment.  It includes closed universes, dependent functions, axioms, transparent definitions, and single inductive declarations with strict positivity checking and primitive recursor families.  It excludes the parts of Lean 4 that would force immediate commitments on universe polymorphism, propositions, or richer inductive families before the base recursor story is stable.

## References

| Reference | Status |
| --- | --- |
| <https://arxiv.org/abs/2403.14064> | Reviewed for project contrast.  It describes Lean4Lean as an external checker for Lean written in Lean, and it reports partial kernel correctness work. |
| <https://ammkrn.github.io/type_checking_in_lean4/declarations/inductive.html> | Reviewed for inductive structure.  It treats an inductive declaration as a type, constructors, derived recursors, and recursor rules. |
| <https://github.com/digama0/lean4lean> | Reviewed for contrast in implementation strategy.  The repository describes itself as a Lean 4 kernel or external checker written in Lean 4. |
| <https://lean-lang.org/doc/reference/latest/The-Type-System/> | Reviewed for the core language boundary.  The reference manual describes Lean's core terms and the reduction rules used by definitional equality. |
| <https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/> | Reviewed for recursors, iota reduction, and the well-formedness conditions on inductive declarations. |
| <https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/> | Reviewed for the universe hierarchy and the scope of the omitted universe-polymorphic fragment. |
| <https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/> | Reviewed for the low-level `Quot` primitives and the `Quot.lift` reduction rule. |
| <https://github.com/nomeata/lean-mini-kernel/tree/master> | Reviewed for comparison.  The repository is a compact Lean-written checker for a Lean export fragment, and its README names deliberate omissions around mutual inductives, nested inductives, proof irrelevance checks, and projection checks. |
| Local Lean 4.27.0 sources, `Lean/Expr.lean`, `Lean/ProjFns.lean`, and `Lean/Meta/Structure.lean` | Reviewed for projection representation.  Lean has core projection expressions and separately records projection-function metadata for auxiliary declarations. |
| Local Lean 4.27.0 source, `Lean/Declaration.lean` | Reviewed for theorem representation.  Lean records theorem declarations with a stored proof value, and the installed compiler rejects a theorem whose declared type is not a proposition. |
| Local Lean 4.27.0 sources, `Lean/Declaration.lean`, `Lean/Environment.lean`, and `Lean/Replay.lean` | Reviewed for exported declaration shape.  Lean replays axioms, definitions, theorems, opaque definitions, quotient declarations, and inductive declarations into the kernel, while checking generated constructors and recursors against the replay result.  `ReducibilityHints` are kernel metadata on definitions, while opaque declarations remain a separate declaration class. |
| Local Lean 4.27.0 sources, `Lean/Expr.lean`, `Lean/Level.lean`, and `Lean/Declaration.lean` | Reviewed for importer translation.  Lean expressions include binder annotations, metadata, literals, free variables, and metavariables; the local importer erases the semantics-free fields and rejects the forms absent from the local kernel syntax. |

## Small Plan

- [x] Define the minimal scope for the first specification.
- [x] Review the recorded references and the relevant Lean reference sections.
- [x] Draft the initial minimal Lean 4 specification, including inductive types.
- [x] Implement the first running kernel model in Lean 4 for that specification.
- [x] Check that the resulting specification and kernel together constitute a serious proof of concept.

## Next Plan

- [x] Draft [Helper-Target Design](helper-target-design.md) for telescope-aware nested helper targets.
- [x] Replace closed helper-target expressions with contextual target schemas and indexed field shapes.
- [x] Rewrite family construction, motive formation, minor-premise generation, and iota reduction around target schemas.
- [x] Re-admit binder-dependent nested positive examples.
- [x] Add focused tests for simultaneous substitution and raw malformed-entry rejection.
- [x] Add generated-declaration validation coverage.
- [x] Record the de Bruijn context and simultaneous-substitution invariants in the specification.
- [x] Introduce shared telescope operations for source-order binding, context conversion, and simultaneous type instantiation.
- [x] Route parameter, helper-local, and field binding through the shared telescope operations.
- [x] Add regression coverage for telescope context order, dependent binding, independent binding, and simultaneous type instantiation.
- [x] Add constructor field dependencies on top of the target-schema representation.
- [x] Add indexed inductive families on top of the target-schema representation.
- [x] Add universe contexts for inference, conversion, axioms, and definitions.
- [x] Extend universe polymorphism to inductive declarations and generated recursors.
- [x] Rebase the data fragment so `Sort 0` is reserved for `Prop` and data inductives live above it.
- [x] Add the known-Prop function-sort rule.
- [x] Add proof irrelevance for terms with the same normalized proposition type.
- [x] Add proposition-valued inductives with Prop-only elimination.
- [x] Add a symbolic `imax` level former.
- [x] Add large elimination for a conservative syntactic subsingleton class.
- [x] Specify the full indexed subsingleton-elimination criterion.
- [x] Make inductive-block admission the primitive path.
- [x] Add mutual and nested mutual recursor regressions.
- [x] Replace variant constants with declaration records and primitive metadata.
- [x] Add opaque definitions as checked, non-unfolding declarations.
- [x] Add low-level quotient primitives and the `Quot.lift` reduction rule.
- [x] Add a first Lean 4 faithfulness corpus with accepted and rejected source examples.
- [x] Add core projection expressions and projection declarations for non-indexed one-constructor inductives.
- [x] Add checked theorem declarations that store proof values without unfolding them.
- [x] Add an ordered declaration-script admission path over the checked declaration APIs.
- [x] Add a kernel-style inductive declaration adapter over type-former and constructor types.
- [x] Record reducibility hints on transparent definitions without changing the opaque-declaration rule.
- [x] Add structure metadata for direct fields, parent subobjects, and flattened inherited fields.
- [x] Add exported generated-constructor and generated-recursor replay checks.
- [x] Add dependency-aware replay for declaration collections that are not already ordered.
- [x] Add a first importer from Lean declaration data into local declaration entries.
- [x] Reconstruct declaration entries from finite Lean `ConstantInfo` snapshots.

## Current Decisions

The first specification draft lives in `spec.md`.  It now covers the data fragment with universe-polymorphic axioms, transparent and opaque definitions, checked theorem declarations, inductive blocks, parameters, indices, dependent constructor-field telescopes, strictly positive recursive fields, generated recursor families, low-level quotient primitives, core projections, and beta, delta, zeta, iota, projection, and quotient reduction.  It includes `Prop`, proof irrelevance, indexed subsingleton elimination, mutual inductive blocks with shared parameters, structure metadata, reducibility hints, checked declaration replay, a first Lean declaration importer, and reconstruction from finite `ConstantInfo` snapshots.  It still omits the higher-level `Quotient` API, direct recursive definition import, literal expressions, unsafe declarations, and extraction of arbitrary dependency closures from Lean environments.

Universe levels are represented by a small level language rather than by raw natural numbers.  `Sort 0` is now reserved for `Prop`, and the data examples use `Sort 1` as `Type 0`.  Axioms, definitions, and inductive declarations may declare universe parameters, and the inferencer, normalizer, and conversion checker carry an explicit universe context.  Inductive result universes remain explicit, but they may mention the inductive declaration's universe parameters and must stay above `Prop` in the data fragment.  The kernel checks that constructor arguments do not force a larger universe, that constructor targets use the inductive universe parameters, and that generated recursors place the inductive universe parameters before the fresh motive universe parameter.  The term language carries explicit universe arguments on constants, because primitive recursors need a motive universe parameter in order to exist as ordinary constants with ordinary types.  The kernel enforces that these universe arguments are arity-correct and closed under the active universe context in both inference and normalization, rather than trusting normalization to see only well-formed constants.

The positivity check is compositional across earlier inductive declarations.  The kernel computes which parameters of each inductive are positive, and it uses that information when another inductive nests a recursive occurrence under that type constructor.  The recursor generator follows the same structure, producing helper recursors for nested positive targets such as `List T` in addition to the primary recursor for `T`.  Recursor constants now type-check through the ordinary spine rule, and iota reduction is confined to saturated applications.

The inductive checker now analyzes canonicalized field types rather than surface syntax.  It normalizes constructor field types and specialized nested targets before testing parameter positivity, before classifying recursive field shapes, and before deduplicating helper-recursion targets.  That change removes three integrity problems from the earlier draft: local `let` bindings no longer change whether a parameter counts as positive, nested arguments no longer fail positivity because of reducible syntax inside a non-positive parameter, and definitionally equal nested targets no longer generate duplicate helper recursors.

The helper-target redesign is now in place.  Nested helper targets are represented by canonical target schemas with local telescopes, then interned into indexed family targets before motive formation or reduction.  That representation re-admits binder-dependent positive fields such as `(n : Nat) → WrapAt n T`, and it removes the last dependence on lowering nested targets into closed expressions.

Primitive recursor reduction now checks that the constructor universe arguments and target arguments are definitionally equal to the instantiated schema before applying an iota step.  That side condition matters because normalization is available on raw expressions, not only on terms that have already passed inference.  Helper-recursion targets store their own target universe levels, so a nested helper recursor through a polymorphic inductive can construct minor-premise targets at the same levels that appeared in the nested field.

The target-schema rewrite required one further correction in the term language itself.  Open substitution across a schema context cannot be implemented as repeated one-variable substitution, because later substitutions then rewrite variables inside earlier inserted terms.  The kernel now uses simultaneous instantiation for `Expr.instantiateMany`, which restores the intended behavior for parameterized recursors such as `WrapAt.rec` and for helper targets that depend on both a parameter and a local binder.

Generated declarations now undergo kernel-side validation before admission to the environment.  The earlier draft built constructor and recursor types, then trusted them.  The kernel now rechecks generated constructor types against the extended environment and rechecks generated recursor types against the inductive and constructor declarations they mention.  That validation step exposed a second structural bug in the inferencer: context lookup must lift a stored binder type back into the current context before returning it.  The kernel now does that, which restores dependent typing for generated recursor binders.

The regression suite now has a separate `leanleantest` executable.  It covers simultaneous substitution directly, including nonzero cutoff and lifting of open inserted values.  It also checks that generated-declaration validation rejects an ill-typed generated type, and that raw inference and normalization entry points reject malformed primitive uses.  The demonstration executable remains available as `leanlean`.

The kernel now has a shared telescope core.  Source-level telescopes remain outermost first, runtime contexts remain innermost first, and the checked code routes conversion between those orders through one API.  The API separates dependent binding, independent binding, and simultaneous type instantiation, because later constructor-field dependencies must not inherit the independent-field assumptions used by the current constructor type generator.  The current `Telescope` type is an abbreviation for `List Binder`, so code review still has to reject direct list operations that recreate binder arithmetic; a wrapper remains an option if that discipline proves too weak.

Constructor fields now form dependent telescopes.  The checker validates each field under the parameters and earlier fields, constructor types bind fields dependently, and recursor minor premises insert an induction hypothesis immediately after each recursive field.  Helper-target construction trims unused trailing locals before interning a target schema; without that rule, a target such as `List Tree` encountered after a previous field would generate an infinite sequence of helper targets with irrelevant field locals.

Indexed inductive families now use explicit constructor result targets.  The primary recursor's motive quantifies over the indices before the target term, while constructor minor premises compute their motive arguments from each constructor's declared result target.  Root indices are target locals for the final recursor application but not uniform minor-premise locals; helper targets still bind their schema locals uniformly.  The examples now cover Type-valued equality, vectors, a recursive height-indexed tree, and rejection of a recursor call whose target index disagrees with the constructor result.

Universe-polymorphic definitions and inductives now have checked paths through the kernel.  `addDefinitionWithLevels` and `addAxiomWithLevels` reject duplicate universe parameters and reject level variables outside the declared universe context, while `addInductive` applies the same discipline to inductive result universes, constructor types, and generated recursor types.  The raw public entry points still reject open universe levels.  The examples `polyId.{u}`, `PolyBox.{u}`, and `Eq.{u}` instantiate above `Type 0`, with `PolyBox` using Lean's `Type u` convention as `Sort (u + 1)` and `Eq` ranging over arbitrary `Sort u`.  The focused regression tests cover symbolic level ordering, universe-context closure, generated recursor level ordering, rejection of proposition-valued data inductives, the known-Prop function-sort rule, and iota rejection for constructor targets at mismatched universe levels.

The Prop work now covers the basic sort, conversion, and inductive boundaries.  Axioms may introduce propositions and proofs, and `∀ x : A, B` lives in `Sort (imax u v)` when the domain has sort `u` and the codomain has sort `v`.  The `imax` normalizer reduces known-Prop codomains to `Prop`, reduces known-data codomains to `max`, and preserves unresolved symbolic `imax` terms instead of approximating them.  Conversion is context-aware internally, and proof irrelevance treats two terms as equal when they infer the same normalized proposition type.  Proposition-valued inductives do not use the data-constructor universe bound, and equality now lives in `Prop` with Lean's parameter/index split: the left side is a recursor parameter and the right side is the index.  Proposition-valued inductives generate large-eliminating recursors exactly when they have no constructors, or one constructor whose fields are propositions or values forced by whole target indices.  The previous approximation accepted a data field whose type was an inductive parameter even when the field value was not forced by the target; the `DataWitnessProp` regression now rejects that unsound extraction pattern.  The `IndexSingleton` regression accepts the exact indexed case, and `ShiftedIndexProp` rejects a field that appears only inside a computed index.

Inductive admission is now block-first.  `addInductiveBlock` creates the provisional environment for every block member before target checking, data-universe checks, positivity, recursor construction, and generated-declaration validation; `addInductive` is a singleton wrapper.  The current block rule requires all members to share the block universe parameters and parameter telescope.  Positive-parameter facts are computed as a joint fixed point over the block, and recursive-shape analysis treats every block member as an open recursive target.  The regressions cover ordinary mutual recursion, nested mutual recursion through `List`, and rejection of a negative mutual occurrence.

Environment entries now use one declaration record with explicit kind metadata.  A declaration records its name, universe parameters, type, optional checked value, kind, and reducibility hint for transparent definitions; primitive recursors are represented as primitive metadata instead of a separate constant variant.  Transparent definitions unfold through `ConstantInfo.value?`, while opaque declarations and theorem declarations keep their checked values but return no reduction value.  Reducibility hints are stored as definition metadata, matching Lean's exported declaration shape, and the current normalizer still unfolds every transparent definition.  Theorem admission checks that the declared type lives in `Prop` and that the supplied proof has that type.  Ordered declaration scripts now fold over the same checked APIs used by direct admission, so a later export parser can construct a script without becoming part of the trusted typing boundary.  Kernel-style inductive declarations can now enter as level parameters, a parameter count, type-former types, and constructor types; the adapter reconstructs the local source-shaped block and then uses the same inductive checker.  This separates declaration admission from primitive reduction behavior, which is the representation needed for theorem, projection, quotient, and future exported declarations.

Export replay now has checks for generated constructors and recursors.  These checks do not add declarations; they compare exported constructor and recursor entries against the declarations generated by the earlier inductive admission.  The comparison uses alpha-equivalence for types, because the local generator may choose binder names that differ from an exported artifact while preserving the typed declaration.

Dependency-aware replay now computes the constants mentioned by declaration entries and admits entries once their external dependencies are present.  The rule allows a declaration to refer to names it defines itself, which covers mutual inductive blocks and constructor targets.  It rejects a collection when a pass makes no progress, rather than trying to repair missing dependencies with axioms or placeholders.

The first importer from Lean kernel data now translates Lean `Declaration` values into local declaration entries.  Safe axioms, safe definitions, theorem declarations, safe opaque definitions, quotient declarations, and inductive declarations become ordinary script entries, while generated constructor and recursor `ConstantInfo` values become replay checks against regenerated local declarations.  The importer erases binder annotations, expression metadata, and the `let` nondependence flag, following the Lean source comments that those fields do not affect kernel typing or conversion.  It rejects level metavariables, free variables, term metavariables, literals, unsafe declarations, partial definitions, and mutual-definition declarations because the local kernel has no rule for admitting those objects.

The importer can now translate finite `ConstantInfo` snapshots.  It groups inductive type formers by their `all` field, requires every group member and every listed constructor record to be present, checks that the grouped members share universe parameters and parameter counts, and then emits a kernel-style inductive declaration plus generated constructor and recursor replay checks.  The snapshot path rejects incomplete groups instead of inventing missing constructor declarations from names alone.

The quotient primitive subset follows the Lean reference's low-level `Quot` API rather than the derived setoid-based `Quotient` interface.  The local syntax makes the underlying type and relation explicit in `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, and `Quot.sound`.  Primitive declaration validation checks all five types before admission.  Reduction contains one quotient rule: a saturated `Quot.lift` whose target reduces to `Quot.mk` computes to the representative function applied to the representative, after the reducer checks universe, type, and relation agreement.

The first faithfulness harness now lives under `Faithfulness`.  It runs small Lean source files through the installed Lean compiler and separates examples that Lean must accept from examples that Lean must reject.  The ordinary kernel regression suite contains matching local bridge tests for the same behavior classes, because the project does not yet translate Lean source or exported declarations into the local syntax.

Projection work follows Lean's representation split.  The core term language now has `proj S i s`, because treating projections as ordinary constants would hide a kernel reduction rule behind declaration names.  Projection functions are represented in the environment, with metadata recording the structure name, constructor name, number of parameters, projection index, and constructor-field index.  The implementation covers one-constructor inductives, dependent field types through earlier projections, projection functions as checked declarations, Prop projection rejection for computational fields, indexed projection maps that skip whole-index fields, and eta for non-recursive data structures whose constructor target matches the major premise type.

Structure metadata follows Lean's split between kernel declarations and elaborator structure information.  A structure record in the local environment records direct fields, projection names, direct parents, and subobject fields, while parent projections remain ordinary checked projection declarations.  Flattened inherited-field lookup is metadata over those declarations; it does not add a reduction rule beyond the existing projection and delta rules.
