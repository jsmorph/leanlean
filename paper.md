# Paper Claim Structure

This document sketches the paper claims supported by the current repository.  It separates specification, implementation, and Lean 4 faithfulness because each claim needs different evidence.  The intended paper presents the project as a specification-driven kernel fragment with executable validation, not as a derivation from Lean 4 source code.

## Main Claims

| Claim | Statement | Repository evidence |
| --- | --- | --- |
| Specification | The repository defines a precise Lean-like kernel fragment with universes, `Prop`, proof irrelevance, inductive blocks, generated recursors, low-level quotients, projections, structure metadata, literals, and declaration replay. | [Minimal Kernel Subset](spec.md), [Metatheoretic Account](metatheory.md), [Traceability Map](traceability.md). |
| Implementation | The Lean implementation realizes the trusted rules in the specification for the stated fragment, with checked admission paths for every environment entry. | [Kernel Implementation](LeanLean/Kernel.lean), [Import Implementation](LeanLean/Import.lean), [Regression Suite](Test.lean). |
| Faithfulness | On the named Lean 4 fragment, the local checker agrees with Lean on accepted source examples, rejected source examples, imported environment closures, selected inferred types, selected normal forms, imported constant types, and transparent-definition reductions. | [Faithfulness Harness](faithfulness.md), [Accepted Corpus](Faithfulness/Accepted.lean), [Rejected Corpus](Faithfulness/Rejected), [Importer Smoke](Faithfulness/ImportSmoke.lean), [Differential Harness](Faithfulness/Differential.lean). |

The specification claim comes first.  The implementation claim depends on it, because the checker is meaningful only relative to the rules it purports to implement.  The faithfulness claim then compares those rules and that implementation against Lean 4 on a named fragment rather than treating Lean 4 as the specification.

## Paper Outline

| Section | Function |
| --- | --- |
| Problem and contribution | Explain the absence of an official Lean 4 kernel specification and state the goal: a local specification plus a checker for a serious fragment. |
| Core syntax and typing | Present the abstract syntax, contexts, substitution convention, universe rules, typing judgment, and conversion relation. |
| Inductive declarations | State the block admission rule, positivity rule, constructor target rule, generated recursor construction, iota side conditions, and large-elimination criterion. |
| Environment semantics | Present checked declaration records, transparent and opaque conversion behavior, theorem opacity, quotient primitives, projections, structure metadata, and declaration replay. |
| Lean 4 import and faithfulness | Describe translation from Lean declaration data, closure extraction, generated-declaration replay, structure-extension import, source corpus testing, and differential comparison. |
| Metatheory | State preservation, substitution, universe, positivity, recursor, projection, quotient, and replay obligations.  Identify which obligations are mechanized as executable tests and which remain paper proofs. |
| Evaluation | Report the regression suite, source corpus, importer smoke roots, broad differential fragments, and every fixed divergence that became a regression. |
| Boundaries | State unsupported Lean 4 behavior in paper-ready terms, with reasons and required work. |

## Evaluation Claims

The evaluation reports commands rather than anecdotes.  The core implementation is checked by `lake build`, `lake exe leanleantest`, and `lake exe leanlean`.  Lean faithfulness is checked by `lake exe leanleanfaith`, `lake exe leanleanimport`, and `lake exe leanleandiff`.

The source corpus establishes agreement with Lean's frontend and kernel on small accepted and rejected files.  The importer smoke test establishes that selected Lean environment closures translate into local declaration scripts and replay through checked admission.  The differential harness establishes term-level agreement for selected inferred types and normal forms, then fragment-level agreement for imported constant types and transparent-definition reductions.

The evaluation describes the named fragments exactly.  The current broad fragments are the accepted corpus plus module-boundary roots, a core logic fragment, a core data fragment, and their combined replay fragment.  The claim remains limited to these fragments.

## Boundaries

| Boundary | Paper statement | Work needed to remove it |
| --- | --- | --- |
| Source-level recursive definitions | The importer rejects Lean declarations marked as recursive-definition artifacts and does not reconstruct structural or well-founded recursion from source-level metadata. | Specify recursive-definition compilation as a kernel-facing rule, including equation metadata, structural recursion, well-founded recursion, and partial-recursion rejection. |
| Unsafe declarations | Trusted replay rejects Lean declaration data marked unsafe. | State a separate unsafe semantics, or keep unsafe declarations outside the trusted theorem. |
| Full string computation | String literals type-check, but local normalization treats them as neutral literals. | Specify and implement the string, character-list, byte-array, and recursive support needed for Lean's string reduction path. |
| Higher-level quotient API | The trusted primitive quotient fragment is limited to `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, and `Quot.sound`. | Define or import the setoid-based `Quotient` API on top of the low-level primitives and test its generated terms. |
| Arbitrary Lean modules | The faithfulness claim covers named finite fragments, not arbitrary Lean modules. | Add rules for every dependency class encountered by larger modules, then expand closure replay and differential tests. |
| Structure elaboration metadata | The importer reads only structure metadata needed for kernel-facing projection and inherited-field checks. | Specify any additional elaborator metadata that affects trusted typing or conversion, or keep it outside the kernel boundary. |
| Sort-polymorphic inductive results | The checker admits `Prop`, data-valued results, empty sort-polymorphic inductives, and one-constructor no-field sort-polymorphic inductives. | Characterize Lean's full rule for sort-polymorphic inductives and prove that each admitted shape preserves soundness at `Sort 0`. |
| Structure eta outside the current fragment | Eta conversion is restricted to non-recursive, data-valued, one-constructor inductives whose constructor target matches the inferred structure type. | Specify recursive and more indexed structure eta, then prove preservation and add Lean comparison cases. |

## Submission Bar

The repository is ready for a paper only when every trusted rule in [Minimal Kernel Subset](spec.md) has a traceability row, every traceability row has a stated metatheoretic obligation, and every fixed bug has a regression.  The paper states which metatheoretic obligations remain proof sketches rather than mechanized theorems.  It reports unsupported Lean 4 behavior as a boundary of the theorem, not as incidental missing engineering work.
