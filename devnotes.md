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

## Current Decisions

The first specification draft lives in `spec.md`.  It now covers the data fragment with single inductive declarations, strictly positive recursive fields, generated recursor families, and beta, delta, zeta, and iota reduction.  It still omits `Prop`, proof irrelevance, quotient types, mutual inductives, indices, and general user-declared universe polymorphism.

Universe levels are represented by a small level language rather than by raw natural numbers.  Inductive result universes remain explicit and closed, and the kernel checks that constructor arguments do not force a larger universe.  The term language now also carries explicit universe arguments on constants, because primitive recursors need a motive universe parameter in order to exist as ordinary constants with ordinary types.

The positivity check is compositional across earlier inductive declarations.  The kernel computes which parameters of each inductive are positive, and it uses that information when another inductive nests a recursive occurrence under that type constructor.  The recursor generator follows the same structure, producing helper recursors for nested positive targets such as `List T` in addition to the primary recursor for `T`.  Recursor constants now type-check through the ordinary spine rule, and iota reduction is confined to saturated applications.
