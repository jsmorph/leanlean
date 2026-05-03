# Plan for a Principled Lean Kernel

## Status

- [x] Phase 1: Stabilize the current core.
- [x] Phase 2: Shared telescope core.
- [x] Phase 3: Constructor field dependencies.
- [x] Phase 4: Indexed inductive families.
- [x] Phase 5: Universe polymorphism.
- [x] Phase 6: `Prop`, proof irrelevance, and elimination restrictions.
- [x] Phase 7: Mutual and nested mutual inductives.
- [x] Phase 8: Low-level quotients and primitive equality support.
- [ ] Phase 9: Definitions, opacity, and environment semantics.  Declaration records, opacity, theorems, projections, structure metadata, dependency-aware replay, closure extraction, and generated-declaration replay are implemented, but literal expressions, recursive-definition artifacts, unsafe declarations policy, and full exported environment behavior remain.
- [ ] Phase 10: Faithfulness against Lean 4.  The source corpus, negative examples, importer smoke test, and selected real-environment closure import exist, but broad differential testing and documented full-fragment agreement remain.
- [ ] Phase 11: Metatheory and paper-grade artifacts.  The repository has a growing specification, implementation, and faithfulness corpus, but it still needs a traceability map from specification clauses to implementation functions and tests.

This plan describes a path from the current specification-driven proof of concept to a complete Lean 4 kernel.  The project has two operating standards.  Every trusted feature needs a written local specification before implementation work builds around it.  Every object admitted to the environment needs the same well-formedness discipline, whether the object came from user input or from kernel generation.

The current kernel has a useful base.  It implements a small dependent type theory with universe-polymorphic axioms, transparent and opaque definitions, theorem declarations, inductive blocks, predicative inductive result universes, indices, dependent constructor-field telescopes, strict positivity, first-class recursor constants, nested helper recursors, telescope-aware helper targets, low-level quotient primitives, core projections, beta, delta, zeta, iota, projection, quotient, eta, and proof-irrelevance conversion, simultaneous substitution, and validation of generated constructor, recursor, projection, and primitive types.  The examples now use Lean's universe numbering: `Sort 0` is reserved for `Prop`, while ordinary data begins at `Sort 1`.  Lean 4 contains substantially more theory.  Recursive definition compilation, literals, unsafe declarations, structure-extension records, and broad faithfulness testing still affect the path to a complete kernel.

## Principles

The project remains spec-driven.  The Lean 4 implementation, the Lean reference manual, Ammar Kahn's notes, and Lean4Lean provide comparison points.  This repository still needs its own specification for each trusted rule.  A complete local kernel cannot depend on informal expectations about current Lean behavior.

The implementation maintains a narrow trusted boundary.  Any declaration added to the environment must have a type that the kernel can recheck.  Generated recursors, constructors, projections, and quotient primitives go through the same gate.  Conversion computes through primitive applications only when the primitive head and its arguments satisfy the rule being applied.

The roadmap prioritizes architectural completeness before feature breadth.  The next hard changes strengthen representations that later features will reuse.  A smaller fragment with exact rules gives better evidence than a wider fragment whose behavior lives in special cases.  Each phase therefore ends with rejection tests as well as accepted examples.

## Phase 1: Stabilize the Current Core

This phase closes the remaining integrity gaps in the current proof of concept before the fragment grows.  The target is a subset whose behavior is uneventful under review.  The work is small, but it protects the core machinery that later phases will reuse.

| Task | Reason | Exit condition |
| --- | --- | --- |
| Add focused tests for simultaneous substitution, including nonzero cutoff. | The target-schema rewrite depends on simultaneous open substitution. | The suite contains direct substitution examples independent of recursors. |
| Add a negative generated-declaration validation test. | Generated types are now rechecked, but the regression suite does not prove that the check can fail. | A deliberately malformed generated declaration path fails before environment admission. |
| Audit all raw-expression kernel entry points. | `infer`, `normalize`, and declaration checking should agree about malformed constants, open universes, and primitive heads. | Each public checker or reducer has documented preconditions and matching negative tests. |
| Separate examples from tests. | `lake exe leanlean` currently acts as both demonstration and regression suite. | A test module reports specific failures, while the executable remains a readable demonstration. |
| Record substitution and context invariants in the spec. | De Bruijn code is a recurring source of kernel bugs. | The spec states the context ordering, lifting rule for context lookup, and simultaneous-substitution convention. |

## Phase 2: Shared Telescope Core

The next major change should be a shared telescope abstraction.  Parameters, indices, helper-target locals, constructor fields, motives, and minor premises all need the same operations: extension, lifting, simultaneous instantiation, closure checking, and conversion under a context.  The recent target-schema work already showed that open substitution and context lookup are high-risk parts of the kernel.

This phase should move binder arithmetic out of scattered call sites and into a small set of audited telescope operations.  The implementation should make context order explicit and keep bvar shifting rules local to those operations.  Later phases should consume the telescope API rather than constructing binder lists and substitutions by hand.

Acceptance criteria:

- Parameter, helper-local, and field contexts use one telescope representation.
- The regression suite covers extension, lifting, simultaneous instantiation, and nonzero cutoff substitution.
- The specification states the context order and substitution convention.
- Existing recursor examples continue to type-check and normalize through the telescope API.

## Phase 3: Constructor Field Dependencies

The earlier subset checked every constructor field type in the parameter context.  Lean constructors allow later fields and constructor results to depend on earlier fields.  This phase adds constructor-field telescopes on top of the shared telescope core.  It comes before indexed inductive families because many indexed examples require constructor results whose indices depend on constructor fields.

Field types need sequential checking, with each later field seeing earlier fields.  Recursor minor premises must bind fields in that same order.  Induction hypotheses should be inserted at the points determined by recursive fields, with their types computed in the full field context.  Reduction then substitutes field arguments into later field types and induction hypotheses.

This phase also gives the positivity checker its first dependent field context.  Recursive occurrences in later field types and constructor results must be classified with the same context operations used by typing and reduction.  That forces the binder machinery to prove itself before indices and mutual recursion multiply the number of moving parts.

Acceptance criteria:

- Constructors whose later fields depend on earlier fields type-check.
- Minor-premise generation preserves the field dependency order.
- Recursor reduction substitutes field arguments into later field types and induction hypotheses correctly.
- The regression suite includes cases where dependency bugs would produce a wrong de Bruijn index.

## Phase 4: Indexed Inductive Families

Indexed inductive families are the next structural milestone after dependent constructor fields.  They exercise the target-schema representation that now handles nested helper targets and the telescope abstraction introduced in the previous phases.  They also cover many examples that a Lean-like kernel must handle, including equality and vectors.

This phase extends inductive declarations from parameter-only types to parameters plus indices.  Constructor targets become full applications of the inductive type to parameters and index terms.  Those index terms may depend on constructor fields.  The recursor motive quantifies over indices before the target term, and each minor premise returns the motive instantiated at the constructor target indices.

The positivity checker needs to operate over parameters, indices, helper locals, and constructor fields without conflating them.  The current target-schema machinery should generalize to indexed target schemas.  Iota reduction should compare the constructor target, including indices, against the instantiated recursor target before reducing.

Acceptance criteria:

- The kernel accepts equality, vectors, and length-indexed trees in the local syntax.
- The kernel rejects recursive occurrences in negative positions under indices or fields.
- Generated recursor types for indexed examples are rechecked before environment admission.
- Iota reduction for indexed examples refuses constructor targets whose indices disagree with the recursor target.

## Phase 5: Universe Polymorphism

The current level language has closed levels plus one generated recursor motive parameter.  Full Lean needs universe parameters on declarations, level expressions, level substitution, universe constraints, and `Prop`-specific universe behavior.  This phase first adds ordinary user-declared universe parameters while keeping `Prop` outside the fragment.

Declarations should carry explicit level parameters.  Constants should be instantiated only by levels whose free variables are bound by the current universe context.  Definitional equality should compare normalized level expressions.  Inductive universe checking should derive or validate result levels against parameter, index, field, and constructor target universes.

`Prop` and `imax` belong after ordinary universe polymorphism.  `Prop` changes the typing rule for dependent functions and the elimination rules for inductives.  Adding both at once would mix two independent sources of complexity.  The staged order gives the universe checker a simpler first target.

Acceptance criteria:

- Monomorphic examples continue to work unchanged.
- Polymorphic definitions and inductives instantiate at multiple universe levels.
- The kernel rejects open universe variables outside a declared universe context.
- Inductive universe validation covers parameters, indices, fields, and recursive targets.

## Phase 6: `Prop`, Proof Irrelevance, and Elimination Restrictions

`Prop` affects the sort of function types, proof irrelevance, and the legality of eliminating propositions into computational sorts.  The specification must state those rules before implementation starts.  This phase should add the universe arithmetic for `Prop`, including `imax` where Lean requires it.  It should also classify inductive declarations by whether they live in `Prop` or in data universes.

Recursor generation must enforce small- and large-elimination restrictions.  Proof irrelevance should enter conversion through a written rule whose scope is explicit.  The implementation should keep proof irrelevance separate from ordinary beta, delta, zeta, and iota reduction, because the rule has a different justification.  Tests should include accepted proof terms and rejected eliminations.

Acceptance criteria:

- Propositions, predicates, and simple proof terms type-check.
- The kernel rejects forbidden eliminations from propositions into data.
- Proof irrelevance is tested as a conversion rule.
- Existing data-recursion examples keep their previous normal forms.

## Phase 7: Mutual and Nested Mutual Inductives

Mutual inductives require positivity, recursor generation, and iota reduction to work over a group of inductive types.  The current family machinery should become a graph over root targets rather than a family rooted at one inductive.  The specification should distinguish mutual recursion, nested recursion through earlier inductives, and combinations of the two.

Positivity should compute a joint fixed point over the mutual block.  Constructor and recursor generation should validate every generated type in an environment that contains the whole block.  The generated environment should avoid accidental dependence on declaration order inside the block.  Any required ordering should appear in the specification.

Status: implemented for blocks whose members share universe parameters and a parameter telescope.  Recursor metadata now uses one shared family per block, names block-member recursors by their own inductive names, and names nested helper recursors under the first block member, matching Lean's exported nested-mutual declarations.  Minor premises bind all constructor fields before induction hypotheses.  The positivity checker rejects nested inductive parameters that contain local variables, matching Lean's kernel rejection for examples such as `(n : Nat) → WrapAt n T`.  The regression suite covers ordinary mutual recursion, nested mutual recursion through `List`, correct helper names, local-variable rejection in nested parameters, and rejection of a negative mutual occurrence.  The singleton inductive API now routes through block admission.

Acceptance criteria:

- Standard mutual examples type-check and compute.
- Negative mutual occurrences are rejected.
- Nested recursion inside a mutual block produces the expected helper recursors.
- Generated declarations are validated against the whole mutual block before admission.

## Phase 8: Quotients and Primitive Equality Support

Lean's quotient types are kernel primitives.  A complete kernel needs their type former, constructors, eliminator, and reduction behavior.  This phase should follow `Prop`, because quotients depend on propositions and proof irrelevance.

The local specification should state the quotient constants and their trusted computation rules.  The implementation should add them as primitive declarations whose types are checked in the same validation framework used for generated recursors where possible.  Reduction should compute only at the primitive redexes allowed by the specification.  The tests should target malformed eliminations as well as successful quotient computations.

Status: implemented for the low-level `Quot` API.  The kernel validates primitive declarations for `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, and `Quot.sound`, and reduction computes `Quot.lift` on `Quot.mk` after checking universe, type, and relation agreement.  The higher-level setoid-based `Quotient` API remains outside the current subset.

Acceptance criteria:

- Quotient formation, abstraction, lifting, and induction examples type-check.
- The quotient computation rule reduces the intended redexes.
- The kernel rejects malformed quotient eliminations.
- Quotient support preserves proof irrelevance and universe checks.

## Phase 9: Definitions, Opacity, and Environment Semantics

The current kernel has axioms and transparent definitions.  Lean needs opaque constants, reducibility information relevant to conversion, theorem declarations, projections, and a larger environment model.  Name resolution and elaboration can stay outside the kernel boundary, but the kernel must specify the declarations it accepts after elaboration.

The environment should record exactly the data the checker trusts: universe parameters, type, optional value, opacity, primitive kind, and reduction metadata.  Transparent and opaque constants should behave differently under conversion.  Structures and projections should either compile to existing primitives or enter as specified kernel primitives.  No reduction rule should depend on source-level syntax that elaboration should have removed.

Status: partially implemented.  Environment entries now use a single declaration record with kind metadata, optional checked values, primitive recursor metadata, projection metadata, theorem metadata, reducibility hints for transparent definitions, structure metadata, and transparent versus opaque declaration behavior.  Ordered declaration scripts fold over the checked admission APIs, while dependency-aware replay can process finite declaration collections whose entries are not already topologically ordered.  Kernel-style inductive declarations can enter as type-former and constructor types with a parameter count, and the adapter reconstructs the local inductive block before running the ordinary inductive checker.  Exported generated constructors and recursors can then be checked against the regenerated declarations, with Lean-imported recursors also checking `RecursorVal` metadata and rule right-hand sides.  The Lean importer translates safe Lean `Declaration` values, generated constructor or recursor `ConstantInfo` values, finite `ConstantInfo` snapshots, and root-name environment closures into those same script entries.  Projection support is implemented for one-constructor inductives, including indexed projection maps, dependent projection result types, parent subobject projections, flattened inherited-field metadata, and eta for non-recursive data structures whose constructor target matches the major premise type.  Theorem declarations are checked proof declarations whose types must live in `Prop`, whose proof values are stored, and whose constants do not unfold during conversion.

Acceptance criteria:

- Transparent and opaque constants behave differently under conversion.
- The environment can represent declarations exported from realistic Lean modules after elaboration.
- Projection and structure support have a written kernel account.
- Reduction depends only on trusted environment entries and core expressions.

## Phase 10: Faithfulness Against Lean 4

Once the local kernel covers the major primitives, the project should compare behavior against Lean 4 systematically.  The comparison should be differential testing against small exported terms and declarations.  The local kernel remains specification-driven, so differences should become written divergences or fixed bugs.

The comparison suite should include accepted and rejected examples.  Accepted examples should compare inferred types and normal forms where the local syntax can express them.  Rejected examples should target universe errors, forbidden eliminations, positivity failures, quotient misuse, malformed recursor applications, and opacity.  Each fixed divergence should become a regression test.

Status: started with a source-level Lean corpus under `Faithfulness` and an executable runner named `leanleanfaith`.  The first corpus covers accepted universe-polymorphic definitions, theorem declarations, recursor computation, proposition eliminators, equality, quotients, mutual inductives, nested mutual inductives, and projections.  It also covers rejected positivity, theorem types outside `Prop`, ambiguous universe, forbidden proposition elimination, opacity, invalid projections, eta across computed indices, quotient relation examples, and nested inductive parameters containing local variables, with matching local bridge tests in the kernel regression suite.

Acceptance criteria:

- A corpus of small Lean declarations translates into the local syntax and checks.
- The local kernel agrees with Lean 4 on a documented class of negative examples.
- Known divergences are listed in the spec with reasons.
- Every fixed divergence gets a regression test.

## Phase 11: Metatheory and Paper-Grade Artifacts

A complete kernel implementation needs a stable written specification, an executable checker, a test corpus, and a metatheoretic account of the trusted rules.  The paper path should separate three claims.  The first claim is specification: the repository states a precise kernel theory for a Lean-like system.  The second claim is implementation: the Lean implementation realizes that specification.  The third claim is faithfulness: the specified system matches a documented fragment, and later a broad portion, of Lean 4 kernel behavior.

The repository should contain a traceable map from specification clauses to implementation functions and tests.  Historical bug classes should remain visible through regression tests, because they show where the trusted boundary was tightened.  The paper should state remaining divergences from Lean 4 directly.  It should rely on local rules, tests, and comparison results rather than implementation folklore.

Acceptance criteria:

- The specification is complete enough that an independent implementer could write a checker from it.
- The implementation has tests for every trusted rule and every historical bug class.
- The repository maps specification clauses to implementation functions and tests.
- The paper states the remaining divergences from Lean 4.

## Immediate Next Work

Ordinary universe polymorphism now covers inference, conversion, axioms, transparent and opaque definitions, theorem declarations, inductive blocks, generated constructors, generated recursors, low-level quotient primitives, and core projections for one-constructor inductives.  The kernel reserves `Sort 0` for `Prop`, uses symbolic `imax` for dependent function sorts, applies proof irrelevance to terms with the same normalized proposition type, supports proposition-valued inductives with the indexed syntactic subsingleton-elimination rule, admits mutual inductive blocks atomically, records primitive, theorem, projection, reducibility, and structure metadata in the environment, and has ordered and dependency-aware declaration replay paths plus a first executable faithfulness corpus.  The Lean importer now feeds safe declaration data, finite `ConstantInfo` snapshots, and root-name environment closures into that replay path, with a smoke executable over selected accepted-corpus roots including nested mutual inductives, indexed inductives, projections, quotients, and theorems.  The next deep implementation work should move to literal expressions or full structure-extension metadata.
