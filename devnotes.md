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
- [ ] Revisit constructor field dependencies and indexed inductive families on top of the target-schema representation.

## Current Decisions

The first specification draft lives in `spec.md`.  It now covers the data fragment with single inductive declarations, strictly positive recursive fields, generated recursor families, and beta, delta, zeta, and iota reduction.  It still omits `Prop`, proof irrelevance, quotient types, mutual inductives, indices, and general user-declared universe polymorphism.

Universe levels are represented by a small level language rather than by raw natural numbers.  Inductive result universes remain explicit and closed, and the kernel checks that constructor arguments do not force a larger universe.  The term language now also carries explicit universe arguments on constants, because primitive recursors need a motive universe parameter in order to exist as ordinary constants with ordinary types.  The kernel now enforces that these universe arguments are arity-correct and closed in both inference and normalization, rather than trusting normalization to see only well-formed constants.

The positivity check is compositional across earlier inductive declarations.  The kernel computes which parameters of each inductive are positive, and it uses that information when another inductive nests a recursive occurrence under that type constructor.  The recursor generator follows the same structure, producing helper recursors for nested positive targets such as `List T` in addition to the primary recursor for `T`.  Recursor constants now type-check through the ordinary spine rule, and iota reduction is confined to saturated applications.

The inductive checker now analyzes canonicalized field types rather than surface syntax.  It normalizes constructor field types and specialized nested targets before testing parameter positivity, before classifying recursive field shapes, and before deduplicating helper-recursion targets.  That change removes three integrity problems from the earlier draft: local `let` bindings no longer change whether a parameter counts as positive, nested arguments no longer fail positivity because of reducible syntax inside a non-positive parameter, and definitionally equal nested targets no longer generate duplicate helper recursors.

The helper-target redesign is now in place.  Nested helper targets are represented by canonical target schemas with local telescopes, then interned into indexed family targets before motive formation or reduction.  That representation re-admits binder-dependent positive fields such as `(n : Nat) → WrapAt n T`, and it removes the last dependence on lowering nested targets into closed expressions.

Primitive recursor reduction now checks that the constructor target arguments are definitionally equal to the instantiated schema arguments before applying an iota step.  That side condition matters because normalization is available on raw expressions, not only on terms that have already passed inference.  The remaining large omission in the inductive fragment is no longer binder-dependent helper targets.  It is the move from parameter-only inductive families to constructor field dependencies and indexed inductive families built on top of the new target-schema representation.

The target-schema rewrite required one further correction in the term language itself.  Open substitution across a schema context cannot be implemented as repeated one-variable substitution, because later substitutions then rewrite variables inside earlier inserted terms.  The kernel now uses simultaneous instantiation for `Expr.instantiateMany`, which restores the intended behavior for parameterized recursors such as `WrapAt.rec` and for helper targets that depend on both a parameter and a local binder.

Generated declarations now undergo kernel-side validation before admission to the environment.  The earlier draft built constructor and recursor types, then trusted them.  The kernel now rechecks generated constructor types against the extended environment and rechecks generated recursor types against the inductive and constructor declarations they mention.  That validation step exposed a second structural bug in the inferencer: context lookup must lift a stored binder type back into the current context before returning it.  The kernel now does that, which restores dependent typing for generated recursor binders.

The regression suite now has a separate `leanleantest` executable.  It covers simultaneous substitution directly, including nonzero cutoff and lifting of open inserted values.  It also checks that generated-declaration validation rejects an ill-typed generated type, and that raw inference and normalization entry points reject malformed primitive uses.  The demonstration executable remains available as `leanlean`.

The kernel now has a shared telescope core.  Source-level telescopes remain outermost first, runtime contexts remain innermost first, and the checked code routes conversion between those orders through one API.  The API separates dependent binding, independent binding, and simultaneous type instantiation, because later constructor-field dependencies must not inherit the independent-field assumptions used by the current constructor type generator.  The current `Telescope` type is an abbreviation for `List Binder`, so code review still has to reject direct list operations that recreate binder arithmetic; a wrapper remains an option if that discipline proves too weak.
