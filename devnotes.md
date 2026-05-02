# Development Notes

This file records sources, rationale, and small plans for the project.  The references below came from the user on 2026-05-02.  They now inform the first specification draft and the initial implementation boundary.  The project remains spec-driven, so the references guide scope and terminology without substituting for the local specification.

## Scope and Rationale

This effort is spec-driven.  It does not derive a Lean kernel in Lean from the Lean 4 sources, and it does not treat the current Lean 4 implementation as a substitute for a specification.  Drafting the specification is therefore a major part of the work, not a preliminary formality.

The first implementation target is a small data fragment.  It includes closed universes, dependent functions, axioms, transparent definitions, and single inductive declarations with direct recursive fields.  It excludes the parts of Lean 4 that would force immediate commitments on universes, propositions, or richer inductive families before the base recursor story is stable.

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
- [ ] Implement the first running kernel model in Lean 4 for that specification.
- [ ] Check that the resulting specification and kernel together constitute a serious proof of concept.

## Current Decisions

The first specification draft lives in `spec.md`.  It covers the data fragment only, with single inductive declarations, direct recursive fields, generated recursors, and beta, delta, zeta, and iota reduction.  It omits `Prop`, proof irrelevance, quotient types, mutual or nested inductives, indices, and universe polymorphism.
