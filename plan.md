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
- [x] Phase 9: Definitions, opacity, and environment semantics.
  - [x] Add a unified declaration record with kind metadata, universe parameters, checked values, primitive metadata, projection metadata, theorem metadata, structure metadata, and reducibility hints.
  - [x] Implement transparent definitions, opaque declarations, and theorem declarations with the intended conversion behavior.
  - [x] Add ordered and dependency-aware declaration replay through the checked admission APIs.
  - [x] Add a kernel-style inductive adapter and replay checks for exported generated constructors and recursors, including recursor metadata and rule right-hand sides.
  - [x] Add core projections and local structure metadata for one-constructor inductives, including inherited-field metadata and eta where the current rule permits it.
  - [x] Add finite `ConstantInfo` snapshot reconstruction and root-name environment closure extraction for selected Lean roots.
  - [x] Specify and implement the unsafe-declaration policy for trusted replay.
  - [x] Add literal expressions to the core syntax, importer, type checker, normalizer, specification, and regression suite.
  - [x] Import Lean's kernel-relevant structure-extension records, including the metadata needed to check inherited projections against exported environments.
  - [x] Replay Lean recursive-definition compilation artifacts by a written kernel-facing rule.
  - [x] Expand exported environment behavior beyond the current smoke roots.
- [x] Phase 10: Faithfulness against Lean 4.
  - [x] Add a source-level accepted and rejected Lean corpus under `Faithfulness`.
  - [x] Add local bridge tests for the same behavior classes covered by the first corpus.
  - [x] Add importer smoke tests over selected real Lean environment closures.
  - [x] Preserve fixed Lean-divergence cases as regression tests.
  - [x] Compare inferred types and normal forms for translated declarations where the local syntax can express them.
  - [x] Expand the accepted and rejected corpus to cover literals, safe compiled recursive definitions, partial or unsafe recursive artifacts, structure-extension metadata, larger universe examples, module boundaries, and additional primitive edge cases.
  - [x] Document every known divergence from Lean 4 in the specification with a reason.
  - [x] Run broad differential replay over larger Lean environment fragments instead of only selected roots.
- [x] Phase 11: Metatheory and paper-grade artifacts.
  - [x] Maintain a written specification for the implemented trusted rules.
  - [x] Maintain `devnotes.md` with references, rationale, and historical bug classes.
  - [x] Keep regression tests for the main historical soundness and faithfulness bugs found so far.
  - [x] Build a traceability map from specification clauses to implementation functions and tests.
  - [x] Write a metatheoretic account of typing, conversion, universe checking, positivity, generated recursors, and environment replay.
  - [x] Review the specification to the level needed for an independent implementation.
  - [x] Draft the paper claim structure around specification, implementation, and Lean 4 faithfulness.
  - [x] State remaining Lean 4 divergences and unsupported features in paper-ready form.
- [x] Phase 12: External checker interfaces.
  - [x] Add typed checker outcomes for acceptance, supported-fragment rejection, unsupported input, and internal checker failure.
  - [x] Add `leanlean-check-module`, which loads compiled Lean modules with `Lean.importModules`, takes explicit root declarations, and replays the root-name closure through the local checker.
  - [x] Specify the first accepted `lean4export` NDJSON fragment.
  - [x] Add `leanlean-check-export`, which reads the Arena input, translates exported declarations into local replay scripts, and reports Arena outcomes.
  - [x] Add a first export-checker smoke test generated from a small Lean source file through `lean4export`.
  - [x] Expand accepted export-checker tests generated from small Lean source files through `lean4export`.
  - [x] Turn the gcd/parity arithmetic export into a regular generated stress test after replay returns an accepted, rejected, or unsupported outcome without an internal abort.
  - [x] Add generated export-checker rejection tests adapted from Lean Kernel Arena source fixtures.
  - [x] Add hand-edited export-checker tests for supported-fragment rejection.
  - [x] Add `leanlean-self-check` for a named kernel-only slice of this repository's compiled declarations.
  - [x] Add export-backed self-check for the same named source-facing roots through `lean4export` and `leanlean-check-export`.
  - [x] Add full export-backed self-check for the source-facing module boundary plus recursive aux support, using explicit trusted-base roots rather than Lean's module loader.
  - [x] Add export-checker tests for unsupported input.
  - [x] Inventory Lean's kernel-overridden primitive reductions from the Lean 4.29.1 source tree.
  - [x] Add specified table entries, source citations, implementation rules, and export tests for each newly admitted primitive.
  - [x] Extend self-check coverage to local declarations compiled through Lean's `brecOn` and `below` artifacts by replaying the recursive aux support needed by source-facing roots.
  - [x] Specify the remaining generated-support boundary for no-confusion helpers, constructor eliminators, match helpers, sparse-case helpers, derived instances, and representation declarations.
  - [x] Add local Arena smoke tests and a sample checker configuration.
  - [x] Add module-checker tests for accepted declarations, unsupported declarations, and rejected declarations inside the supported fragment.
  - [x] Record the checker interfaces in `spec.md`, `faithfulness.md`, and `devnotes.md`.
- [ ] Phase 13: Generated-support self-check.
  - [x] Add an inventory mode that classifies every self-check skipped declaration by generated-support class, module, declaration kind, dependency shape, and current replay outcome.
  - [x] Add a separate generated-support self-check mode that reports accepted, rejected, unsupported, and assumed declarations without changing the source-facing self-check claim.
  - [ ] Specify and check generated match helpers whose values are ordinary dependent eliminator applications.
  - [ ] Specify and check generated no-confusion helpers and constructor eliminators.
  - [ ] Specify and check sparse-case helpers, including the library and primitive dependencies they require.
  - [ ] Specify and check derived instance support and generated representation support only after their trusted role is separated from display and debugging code.
  - [x] Add tests that prevent generated-support mode from silently treating a newly admitted generated class as a typed assumption.
- [ ] Phase 14: Complete replay checker boundary.
  - [ ] Make whole-artifact replay, not rooted replay with trusted non-root definitions, the main checker claim.
  - [x] Add a replay gap report over parsed `lean4export` artifacts.
  - [x] Add a replay gap report over loaded `ConstantInfo` maps.
  - [x] Report unsupported export entries as diagnostic gap rows instead of bare parser failures.
  - [x] Add rooted export gap reports for full self-check assumption burn-down.
  - [ ] Check every safe ordinary declaration in the supplied replay set, while postponing generated constructors and recursors for comparison.
  - [ ] Match Lean's `Environment.replay` policy for unsafe and partial constants, or state the stricter policy as a deliberate external-checker rule.
  - [x] Specify and test an injective accepted-name encoding for the current string-name boundary.
  - [ ] Replace string names with structured names.
  - [ ] Burn down trusted-base assumptions until only named axioms and explicit imported bases remain.

## Top Priorities

The target is the kernel checker boundary.  The core kernel checks expressions, universes, conversion, declaration admission, inductive admission, generated recursor construction, quotient primitives, projections, and primitive reductions.  The replay checker reconstructs kernel-facing declarations from `ConstantInfo` maps or `lean4export` artifacts, orders dependencies, applies the unsafe and partial policy, reconstructs inductive groups, and compares generated constructors and recursors.  The paper-grade claim should name this combined checker boundary, because a checker that reads Lean artifacts must justify both layers.

The external-checker path now centers on `leanlean-check-export`.  The module checker gives immediate feedback on compiled Lean modules, but it still relies on Lean's module loader and environment data.  The export checker is the independent artifact checker: it reads a `lean4export` NDJSON file, translates the records into declaration scripts, and replays those scripts through the local kernel without asking Lean to interpret the artifact.

Whole-artifact replay is the target behavior.  Lean's `Environment.replay` takes a finite `ConstantInfo` map, skips unsafe and partial constants, sends ordinary declarations to the kernel, reconstructs inductive blocks from type-former and constructor data, and checks generated constructors and recursors against the generated environment records.  A local replay-equivalent checker should check every safe, non-partial declaration in the supplied set, except for generated constructors and recursors that it postpones for comparison.  Rooted replay with trusted non-root definitions remains diagnostic evidence, not the final checker claim.

Full export-backed self-check now uses `leanlean-export-roots --self-check` to select source-facing roots plus recursive `below` and `brecOn` support.  `tools/export-full-self-check.sh` exports those roots with `lean4export` and checks them with `leanlean-check-export --self-check-roots`.  The rooted checker treats non-root definitions and theorems as an explicit trusted base, except for named transparent wrappers whose values are needed for conversion and recursive aux support whose values must reduce while checking selected roots.  This boundary matches the module-loader self-check claim while replacing Lean's in-process environment data with an NDJSON artifact.

The export checker should be developed test-first.  Each accepted test should start as a small Lean source file, pass through `lean4export`, and then pass through `leanlean-check-export`; the test therefore checks the exact artifact path we claim to support.  Rejected and unsupported tests should include hand-edited NDJSON fixtures only when the fixture has a written purpose and a readable source companion, because malformed export files can otherwise become opaque test folklore.

The next expressiveness priority inside export replay is to reduce the gap between rooted checking and whole-map replay.  Generated support is first because Lean stores match helpers, no-confusion helpers, constructor eliminators, sparse-case helpers, derived instances, representation support, and auxiliary recursors as ordinary constants.  Primitive computation is second because exported proofs can rely on kernel-overridden definitional equalities even when the theorem statement does not mention the primitive.  Exact generated constructor and recursor comparison is third because Lean replay treats generated records as evidence to compare against kernel output, not as declarations to admit directly.

The primitive rule remains conservative.  The gcd/parity export exposed `Nat.add`, `Nat.mul`, `Nat.pow`, `Nat.beq`, and `Nat.ble`: Lean's prelude declares logical models for these constants, but also marks them with kernel or compiler override behavior, and exported proofs can rely on the resulting definitional equalities.  Closed subtraction added `Nat.sub` through the same admission rule.  The continuing rule is to keep the primitive inventory explicit, then admit each primitive only after `spec.md` states the reduction rule, the implementation checks the declaration shape before reducing, and a generated export test forces that rule through `leanlean-check-export`.

The next self-check priority is generated support.  The current `leanlean-self-check --module-closure` checks the source-facing kernel declarations and the recursive `below` and `brecOn` support needed by those declarations, while treating other generated support as typed dependencies.  That boundary is sounder than pretending generated helpers have been checked, but it leaves many ordinary Lean environment constants outside the self-check claim.  The next step is to add a separate generated-support mode that inventories the skipped declarations and admits each generator class only after the specification states its kernel-facing rule.

The current `lean4export` binary for local runs is `/tmp/lean4export/.lake/build/bin/lean4export`.  The generated export pipeline accepts with `LEANLEAN_LEAN4EXPORT` set to that path.  It includes the gcd/parity arithmetic theorem, whose export checks 572 declaration entries, and two generated rejection fixtures adapted from Lean Kernel Arena: a bogus theorem proof and an ill-typed projection from a proposition.  It also checks static Arena copies for the `imax` normalization bug and bad constant-level unfolding.  The earlier `omega`-generated proof of the same arithmetic shape remains a separate performance stress case, because its closure reaches broad `Lean.Omega` certificate machinery and slow replay points outside the regular fixture's purpose.

This plan describes a path from the current specification-driven proof of concept to a complete Lean 4 kernel.  The project has two operating standards.  Every trusted feature needs a written local specification before implementation work builds around it.  Every object admitted to the environment needs the same well-formedness discipline, whether the object came from user input or from kernel generation.

The current kernel has a useful base.  It implements a small dependent type theory with universe-polymorphic axioms, transparent and opaque definitions, theorem declarations, inductive blocks, predicative inductive result universes, indices, dependent constructor-field telescopes, strict positivity, first-class recursor constants, nested helper recursors, telescope-aware helper targets, low-level quotient primitives, core projections, raw literals, beta, delta, zeta, iota, projection, natural-literal, quotient, eta, and proof-irrelevance conversion, simultaneous substitution, and validation of generated constructor, recursor, projection, and primitive types.  The examples now use Lean's universe numbering: `Sort 0` is reserved for `Prop`, while ordinary data begins at `Sort 1`.  Lean 4 contains substantially more theory.  Recursive definition compilation, full string-literal computation, unsafe declarations, elaborator-only structure data, and broad faithfulness testing still affect the path to a complete kernel.

## Principles

The project remains spec-driven.  The Lean 4 implementation, the Lean reference manual, Ammar Kahn's notes, and Lean4Lean provide comparison points.  This repository still needs its own specification for each trusted rule.  A complete local kernel cannot depend on informal expectations about current Lean behavior.

The implementation maintains a narrow trusted boundary.  Any declaration added to the environment must have a type that the kernel can recheck.  Generated recursors, constructors, projections, and quotient primitives go through the same gate.  Conversion computes through primitive applications only when the primitive head and its arguments satisfy the rule being applied.

The roadmap prioritizes architectural completeness before feature breadth.  The next hard changes strengthen representations that later features will reuse.  A smaller fragment with exact rules gives better evidence than a wider fragment whose behavior lives in special cases.  Each phase therefore ends with rejection tests as well as accepted examples.

## Phase 1: Stabilize the Current Core

This phase closes the remaining integrity gaps in the current proof of concept before the fragment grows.  The target is a subset whose behavior is uneventful under review.  The work is small, but it protects the core machinery that later phases will reuse.

Status: implemented.  The regression suite now contains focused simultaneous-substitution coverage, generated-declaration rejection, and malformed raw-entry rejection.  The specification records the de Bruijn context order, context lookup convention, and simultaneous-substitution rule.  The examples and tests now serve separate roles, with `Test.lean` carrying regression checks and the executable remaining a demonstration path.

| Task | Reason | Exit condition |
| --- | --- | --- |
| Add focused tests for simultaneous substitution, including nonzero cutoff. | The target-schema rewrite depends on simultaneous open substitution. | The suite contains direct substitution examples independent of recursors. |
| Add a negative generated-declaration validation test. | Generated types are now rechecked, but the regression suite does not prove that the check can fail. | A deliberately malformed generated declaration path fails before environment admission. |
| Audit all raw-expression kernel entry points. | `infer`, `normalize`, and declaration checking should agree about malformed constants, open universes, and primitive heads. | Each public checker or reducer has documented preconditions and matching negative tests. |
| Separate examples from tests. | `lake exe leanlean` currently acts as both demonstration and regression suite. | A test module reports specific failures, while the executable remains a readable demonstration. |
| Record substitution and context invariants in the spec. | De Bruijn code is a recurring source of kernel bugs. | The spec states the context ordering, lifting rule for context lookup, and simultaneous-substitution convention. |

## Phase 2: Shared Telescope Core

This phase introduced the shared telescope abstraction.  Parameters, indices, helper-target locals, constructor fields, motives, and minor premises all need the same operations: extension, lifting, simultaneous instantiation, closure checking, and conversion under a context.  The target-schema work showed that open substitution and context lookup are high-risk parts of the kernel.

Status: implemented.  Binder arithmetic now lives in shared telescope operations rather than scattered recursor and inductive call sites.  The implementation makes context order explicit and keeps bvar shifting rules local to those operations.  Later phases should keep using the telescope API rather than constructing binder lists and substitutions by hand.

Acceptance criteria:

- Parameter, helper-local, and field contexts use one telescope representation.
- The regression suite covers extension, lifting, simultaneous instantiation, and nonzero cutoff substitution.
- The specification states the context order and substitution convention.
- Existing recursor examples continue to type-check and normalize through the telescope API.

## Phase 3: Constructor Field Dependencies

The earlier subset checked every constructor field type in the parameter context.  Lean constructors allow later fields and constructor results to depend on earlier fields.  This phase added constructor-field telescopes on top of the shared telescope core.  It came before indexed inductive families because many indexed examples require constructor results whose indices depend on constructor fields.

Status: implemented.  Field types are checked sequentially, with each later field seeing earlier fields.  Recursor minor premises bind fields in the same order, and induction hypotheses are computed from recursive fields in the full field context.  Reduction substitutes field arguments into later field types and induction hypotheses.

This phase also gave the positivity checker its first dependent field context.  Recursive occurrences in later field types and constructor results are classified with the same context operations used by typing and reduction.  That forced the binder machinery through dependent examples before indices and mutual recursion multiplied the number of moving parts.

Acceptance criteria:

- Constructors whose later fields depend on earlier fields type-check.
- Minor-premise generation preserves the field dependency order.
- Recursor reduction substitutes field arguments into later field types and induction hypotheses correctly.
- The regression suite includes cases where dependency bugs would produce a wrong de Bruijn index.

## Phase 4: Indexed Inductive Families

Indexed inductive families were the next structural milestone after dependent constructor fields.  They exercised the target-schema representation that now handles nested helper targets and the telescope abstraction introduced in the previous phases.  They also cover many examples that a Lean-like kernel must handle, including equality and vectors.

Status: implemented.  Inductive declarations now support parameters plus indices, and constructor targets are full applications of the inductive type to parameters and index terms.  Those index terms may depend on constructor fields.  The recursor motive quantifies over indices before the target term, and each minor premise returns the motive instantiated at the constructor target indices.

The positivity checker operates over parameters, indices, helper locals, and constructor fields without conflating them.  The target-schema machinery now covers indexed target schemas.  Iota reduction compares the constructor target, including indices, against the instantiated recursor target before reducing.

Acceptance criteria:

- The kernel accepts equality, vectors, and length-indexed trees in the local syntax.
- The kernel rejects recursive occurrences in negative positions under indices or fields.
- Generated recursor types for indexed examples are rechecked before environment admission.
- Iota reduction for indexed examples refuses constructor targets whose indices disagree with the recursor target.

## Phase 5: Universe Polymorphism

The earlier level language had closed levels plus one generated recursor motive parameter.  Full Lean needs universe parameters on declarations, level expressions, level substitution, universe constraints, and `Prop`-specific universe behavior.  This phase first added ordinary user-declared universe parameters while keeping `Prop` outside the fragment.

Status: implemented.  Declarations carry explicit level parameters, and constants may be instantiated only by levels whose free variables are bound by the current universe context.  Definitional equality compares normalized level expressions.  Inductive universe checking validates result levels against parameter, index, field, and constructor target universes.

The phase intentionally separated ordinary universe polymorphism from `Prop` and `imax`.  `Prop` changes the typing rule for dependent functions and the elimination rules for inductives.  Keeping those rules separate gave the universe checker a smaller first target.

Acceptance criteria:

- Monomorphic examples continue to work unchanged.
- Polymorphic definitions and inductives instantiate at multiple universe levels.
- The kernel rejects open universe variables outside a declared universe context.
- Inductive universe validation covers parameters, indices, fields, and recursive targets.

## Phase 6: `Prop`, Proof Irrelevance, and Elimination Restrictions

`Prop` affects the sort of function types, proof irrelevance, and the legality of eliminating propositions into computational sorts.  The specification stated those rules before implementation work relied on them.  This phase added the universe arithmetic for `Prop`, including symbolic `imax`, and classifies inductive declarations by whether they live in `Prop` or in data universes.

Status: implemented.  Recursor generation enforces small- and large-elimination restrictions for proposition-valued inductives.  Proof irrelevance enters conversion through a written rule whose scope is explicit, separate from ordinary beta, delta, zeta, and iota reduction.  The regression suite includes accepted proof terms and rejected eliminations.

Acceptance criteria:

- Propositions, predicates, and simple proof terms type-check.
- The kernel rejects forbidden eliminations from propositions into data.
- Proof irrelevance is tested as a conversion rule.
- Existing data-recursion examples keep their previous normal forms.

## Phase 7: Mutual and Nested Mutual Inductives

Mutual inductives require positivity, recursor generation, and iota reduction to work over a group of inductive types.  This phase made recursor-family generation operate over an inductive block rather than a single root.  The specification distinguishes mutual recursion, nested recursion through earlier inductives, and combinations of the two.

Positivity computes a joint fixed point over the mutual block.  Constructor and recursor generation validate every generated type in an environment that contains the whole block.  The generated environment avoids accidental dependence on declaration order inside the block.  Any required ordering belongs in the specification.

Status: implemented for blocks whose members share universe parameters and a parameter telescope.  Recursor metadata now uses one shared family per block, names block-member recursors by their own inductive names, and names nested helper recursors under the first block member, matching Lean's exported nested-mutual declarations.  Minor premises bind all constructor fields before induction hypotheses.  The positivity checker rejects nested inductive parameters that contain local variables, matching Lean's kernel rejection for examples such as `(n : Nat) → WrapAt n T`.  The regression suite covers ordinary mutual recursion, nested mutual recursion through `List`, correct helper names, local-variable rejection in nested parameters, and rejection of a negative mutual occurrence.  The singleton inductive API now routes through block admission.

Acceptance criteria:

- Standard mutual examples type-check and compute.
- Negative mutual occurrences are rejected.
- Nested recursion inside a mutual block produces the expected helper recursors.
- Generated declarations are validated against the whole mutual block before admission.

## Phase 8: Quotients and Primitive Equality Support

Lean's quotient types are kernel primitives.  A complete kernel needs their type former, constructors, eliminator, and reduction behavior.  This phase followed `Prop`, because quotients depend on propositions and proof irrelevance.

The local specification states the quotient constants and their trusted computation rules.  The implementation adds them as primitive declarations whose types are checked in the same validation framework used for generated recursors.  Reduction computes only at the primitive redexes allowed by the specification.  The tests target malformed eliminations as well as successful quotient computations.

Status: implemented for the low-level `Quot` API.  The kernel validates primitive declarations for `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, and `Quot.sound`, and reduction computes `Quot.lift` on `Quot.mk` after checking universe, type, and relation agreement.  The higher-level setoid-based `Quotient` API remains outside the current subset.

Acceptance criteria:

- Quotient formation, abstraction, lifting, and induction examples type-check.
- The quotient computation rule reduces the intended redexes.
- The kernel rejects malformed quotient eliminations.
- Quotient support preserves proof irrelevance and universe checks.

## Phase 9: Definitions, Opacity, and Environment Semantics

The current kernel has axioms and transparent definitions.  Lean needs opaque constants, reducibility information relevant to conversion, theorem declarations, projections, and a larger environment model.  Name resolution and elaboration can stay outside the kernel boundary, but the kernel must specify the declarations it accepts after elaboration.

The environment should record exactly the data the checker trusts: universe parameters, type, optional value, opacity, primitive kind, and reduction metadata.  Transparent and opaque constants should behave differently under conversion.  Structures and projections should either compile to existing primitives or enter as specified kernel primitives.  No reduction rule should depend on source-level syntax that elaboration should have removed.

Status: implemented for the current environment fragment.  Environment entries now use a single declaration record with kind metadata, optional checked values, primitive recursor metadata, projection metadata, theorem metadata, reducibility hints for transparent definitions, structure metadata, and transparent versus opaque declaration behavior.  Ordered declaration scripts fold over the checked admission APIs, while dependency-aware replay can process finite declaration collections whose entries are not already topologically ordered and now waits for parent structure metadata before admitting child structure metadata.  Kernel-style inductive declarations can enter as type-former and constructor types with a parameter count, and the adapter reconstructs the local inductive block before running the ordinary inductive checker.  Exported generated constructors and recursors can then be checked against the regenerated declarations, with Lean-imported recursors also checking `RecursorVal` metadata and rule right-hand sides.  The Lean importer translates safe Lean `Declaration` values, generated constructor or recursor `ConstantInfo` values, finite `ConstantInfo` snapshots, root-name environment closures, safe compiled recursive definitions, and Lean's kernel-relevant structure-extension metadata into those same script entries.  It rejects partial definitions, `mutualDefnDecl` records, unsafe declarations, and unsupported sort-polymorphic inductive results, because the local kernel has no rule for partial recursion, unsafe code, or uncharacterized sort-polymorphic data.  Projection support is implemented for one-constructor inductives, including indexed projection maps, dependent projection result types, parent subobject projections, flattened inherited-field metadata, and eta for non-recursive data structures whose constructor target matches the major premise type.  Theorem declarations are checked proof declarations whose types must live in `Prop`, whose proof values are stored, and whose constants do not unfold during conversion.

Broad environment import now covers a named core set beyond the accepted-corpus roots: `True`, `False`, `And`, `Or`, `Exists`, `Subtype`, `Sigma`, `Prod`, `PEmpty`, `PUnit`, `Unit`, `Empty`, `Option`, `ULift`, `PLift`, `PSigma`, and `Decidable`.  The same smoke test now replays safe compiled recursive definitions from the local corpus and core roots.  Broader structure elaboration data such as defaults, resolution order, class-instance metadata, and notation stays outside the kernel unless a later feature gives those fields a trusted role.

Acceptance criteria:

- Transparent and opaque constants behave differently under conversion.
- Trusted replay rejects unsafe Lean declarations before they reach local declaration admission.
- The environment replays concrete Lean roots covering literals, simple inherited structures, core data declarations, quotient primitives, theorem declarations, and safe compiled recursive definitions, with a written rule for rejecting unsafe and partial artifacts.
- Projection and structure support have a written kernel account that covers imported structure-extension metadata.
- Reduction depends only on trusted environment entries and core expressions.

## Phase 10: Faithfulness Against Lean 4

Once the local kernel covers the major primitives, the project should compare behavior against Lean 4 systematically.  The comparison should be differential testing against small exported terms and declarations.  The local kernel remains specification-driven, so differences should become written divergences or fixed bugs.

The comparison suite should include accepted and rejected examples.  Accepted examples should compare inferred types and normal forms where the local syntax can express them.  Rejected examples should target universe errors, forbidden eliminations, positivity failures, quotient misuse, malformed recursor applications, and opacity.  Each fixed divergence should become a regression test.

Status: implemented for the current named fragments.  The source-level Lean corpus lives under `Faithfulness`, the executable runner is `leanleanfaith`, the importer smoke executable is `leanleanimport`, and the differential executable is `leanleandiff`.  The first corpus covers accepted universe-polymorphic definitions, theorem declarations, recursor computation, proposition eliminators, sort-polymorphic subsingletons, equality, quotients, mutual inductives, nested mutual inductives, recursive source definitions, literal declarations, module-boundary imports, primitive-adjacent core declarations, and projections.  It also covers rejected positivity, theorem types outside `Prop`, ambiguous universe, forbidden proposition elimination, opacity, invalid projections, eta across computed indices, quotient relation examples, and nested inductive parameters containing local variables, with matching local bridge tests in the kernel regression suite.  The differential executable elaborates selected Lean terms, asks Lean for inferred types and reduced values, translates those expressions, replays the required environment closures locally, and compares the local inferred types and normalized values against Lean's results.  It also replays named finite environment fragments and compares translated constant types for every imported constant and reduction behavior for imported transparent definitions.

Acceptance criteria:

- A corpus of small Lean declarations translates into the local syntax and checks, including declarations that use literals, safe compiled recursive definitions, partial or unsafe recursive artifacts, inherited structures, larger universe examples, module imports, and primitive edge cases.
- The local kernel compares inferred types and selected normal forms against Lean 4 for every declaration class whose terms the local syntax can express.
- The local kernel agrees with Lean 4 on documented negative examples for universe errors, positivity errors, forbidden proposition elimination, quotient misuse, malformed recursor applications, invalid projections, opacity, and nested-parameter rejection.
- Broad differential replay runs over a named set of Lean environment fragments rather than only selected smoke roots.
- Known divergences are listed in the spec with reasons.
- Every fixed divergence gets a regression test.

## Phase 11: Metatheory and Paper-Grade Artifacts

A complete kernel implementation needs a stable written specification, an executable checker, a test corpus, and a metatheoretic account of the trusted rules.  The paper path should separate three claims.  The first claim is specification: the repository states a precise kernel theory for a Lean-like system.  The second claim is implementation: the Lean implementation realizes that specification.  The third claim is faithfulness: the specified system matches a documented fragment, and later a broad portion, of Lean 4 kernel behavior.

This phase should start before broad faithfulness work finishes.  The repository should contain a traceable map from specification clauses to implementation functions and tests, and that map should grow with each trusted rule.  Historical bug classes should remain visible through regression tests, because they show where the trusted boundary was tightened.  The paper should state remaining divergences from Lean 4 directly and rely on local rules, tests, and comparison results rather than implementation folklore.

Acceptance criteria:

- The specification is complete enough that an independent implementer could write a checker from it.
- The implementation has tests for every trusted rule and every historical bug class.
- The repository maps specification clauses to implementation functions, accepted tests, rejected tests, and Lean comparison cases.
- The paper states the remaining divergences from Lean 4.

## Kernel Expressiveness Gap Register

This register separates checker expressiveness from interface work.  NDJSON parsing, table reconstruction, file handling, and Arena exit codes are necessary for an external checker, but they do not enlarge the trusted theory.  The gaps below name the places where the local kernel still accepts less than Lean 4 or has less evidence than a full Lean 4 replacement would need.

| Gap | Current rule | Why it matters | Work needed |
| --- | --- | --- | --- |
| Unsafe and partial declarations | Trusted replay rejects `unsafe`, `partial`, and `mutualDefnDecl` records.  Safe compiled recursive definitions are accepted as ordinary checked definitions when their closures replay. | Broad exports can contain unsafe or partial constants, and Lean has rules governing which safe declarations may depend on them.  Treating these objects as ordinary definitions would be unsound, while rejecting them limits coverage. | Decide whether the trusted theorem excludes unsafe and partial declarations or specifies a separate layer for them.  If included, model Lean's safety propagation, partial-definition representation, opacity behavior, and dependency restrictions before admitting any such record. |
| Kernel-overridden primitive computation | The specification admits named primitive reductions for `Nat.add`, `Nat.mul`, `Nat.pow`, `Nat.sub`, `Nat.beq`, and `Nat.ble`.  Each rule checks the declaration shape before reducing. | Broad exports can rely on definitional equalities implemented by Lean's kernel even when the exported declaration also contains a logical model.  Missing such a rule causes false rejection; adding an uncited special case weakens the trusted boundary. | Keep the Lean 4.29.1 primitive inventory current.  For each additional admitted primitive, record the source evidence, state the reduction rule, add the declaration-shape check, add implementation tests and an export-checker test, and keep unlisted primitives outside the supported fragment. |
| Full string and byte-array computation | Raw string literals type-check as `String` and remain neutral under local normalization.  Natural literals compute through the `Nat` constructors. | Lean's string literals reduce through `String.ofList`, character-list data, byte-array support, and recursive library definitions.  Real exports can expose those dependencies even when a theorem statement does not mention strings. | Specify the kernel-facing string path, including the declarations and reduction behavior that Lean relies on.  Add accepted and rejected comparisons for `String`, `Char`, lists of characters, byte arrays, and definitions that compute over string literals. |
| Broader sort-polymorphic inductives | The checker admits `Prop`, definitely data-valued results, empty sort-polymorphic inductives, and one-constructor no-field sort-polymorphic inductives. | This covers the known `PEmpty` and `PUnit` shapes, but it is not a full Lean rule.  Larger prelude or library fragments may expose additional accepted shapes or universe interactions. | Characterize Lean's full admission rule for inductive results in `Sort u`.  Prove that each admitted shape preserves the `Prop` extraction boundary, then add corpus examples and differential replay roots for every new shape. |
| Broader structure eta | Eta conversion applies only to non-recursive, data-valued, one-constructor inductives whose constructor target matches the inferred structure type. | Lean's structure behavior is broader and tied to projection machinery, recursive structures, inherited fields, and indexed structures.  A narrow eta rule is safer, but it can reject equalities that Lean accepts. | Specify recursive and indexed structure eta exactly enough to prove preservation.  Add negative tests for computed-index cases, positive tests for each newly admitted shape, and export replay tests that exercise generated projection declarations. |
| Exact conversion equivalence | Conversion uses weak-head reduction followed by syntax-directed comparison, eta, natural-literal numeric comparison, quotient computation, listed primitive computation, and proof irrelevance for the specified fragment. | Broad Lean exports stress transparency, reducibility metadata, universe arithmetic, proof irrelevance, nested recursor computation, quotient computation, and eta in combinations that named tests do not cover. | Expand adversarial conversion tests before adding new features.  State and then discharge preservation obligations for every reduction rule, and compare local conversion against Lean over larger exported fragments. |
| Export replay termination and resource bounds | The generated export pipeline replays small fixtures and the gcd/parity arithmetic fixture to accepted outcomes.  The earlier `omega`-generated proof reaches deep `Lean.Omega` dependencies and exposes slow replay points. | A checker must classify artifacts; unbounded resource use gives neither a kernel rejection nor an unsupported-feature boundary.  Arena use also requires predictable resource behavior on large dependency closures. | Profile the `Lean.Omega` stress artifact and isolate the first declarations with unacceptable replay cost.  Replace structurally recursive normalization, conversion, or replay paths that consume host stack or time on large terms with explicit fuel, iterative traversal, caching, or a written unsupported boundary. |
| Generated support self-check | Source-facing self-check excludes generated match helpers, no-confusion helpers, constructor eliminators, sparse-case helpers, derived instance support, representation declarations, and non-recursive aux recursors as roots.  Recursive `below` and `brecOn` support is replayed when needed. | Lean stores much generated support as ordinary constants.  Some of those constants are kernel-facing values, while others are support for display, derived instances, or compiler-generated case splitting.  A complete self-check needs to separate those roles instead of treating all generated names as one class. | Add an inventory mode, classify every skipped generated declaration, and introduce a separate generated-support self-check mode.  Admit one class at a time only after the specification states its generated form, dependencies, and replay rule. |
| Full prelude and library closure | The checker replays named fragments of `Init`, core data declarations, quotient primitives, theorem declarations, projections, and safe compiled recursive definitions. | Arena and real external checking rely on whole exported dependency closures.  Missing a dependency class causes a decline even when the theorem itself uses only ordinary logic. | Grow the replay roots in layers: tutorial exports, selected `Init` roots, all official `Init.Prelude` policy cases, then `Std` and mathlib fragments.  Each decline must become either a written boundary or a new trusted rule with tests. |
| Structured name fidelity | Internal names are strings.  Lean names with ordinary unquoted components keep their Lean spelling unless that spelling uses the reserved local prefix.  All other Lean names use a reserved structural string encoding that records `anonymous`, `str`, and `num` constructors with length-delimited string components. | Export files carry structured `Name` records.  The structural encoding protects the current checker from known `toString` collisions while still accepting Lean hygienic names, but a complete kernel should store the structured names directly. | Preserve Lean-style structured names in the syntax.  Until then, keep collision tests for quoted components and do not change the reserved encoding without an injectivity argument. |
| Full recursor faithfulness | The generator covers the tested mutual, nested, indexed, proposition-valued, quotient-adjacent, and sort-polymorphic subsingleton cases, and generated recursor metadata is checked against regenerated declarations. | Recursors are the highest-risk generated kernel objects.  Exports from broader libraries may reveal target ordering, helper naming, motive ordering, or rule RHS cases not yet covered. | Use export-checker tests to replay recursor-heavy declarations first.  Add each mismatch as either a Lean divergence with a reason or a generator correction with a regression test. |
| Mechanized metatheory | The repository has a written metatheoretic account and executable tests, but no mechanized proof of preservation, conversion soundness, positivity soundness, recursor correctness, or replay soundness. | A checker can find bugs and reject bad artifacts without a mechanized proof, but research-grade trust needs a precise theorem story.  The absence of proofs limits claims about soundness and completeness. | Turn each traceability row into explicit lemmas, then decide which proofs belong in Lean and which remain paper proofs.  Prioritize preservation for reduction, strict-positivity soundness, and generated recursor correctness. |

## Phase 12: External Checker Interfaces

This phase makes the checker usable on Lean artifacts.  The module-loader bridge already exists as `leanlean-check-module`; it remains useful for diagnosis because it can compare local replay against Lean's loaded environment.  The main implementation target is now `leanlean-check-export`, because that executable checks the kernel-level artifact used by external checkers.

`leanlean-check-export` reads the input form used by `lean-kernel-arena`, parses the accepted `lean4export` NDJSON fragment, translates declarations into the same replay script representation, and runs the local checker without Lean's environment loader.  The first accepted fragment covers `lean4export` format 3.1.0 records for names, universe levels, expressions, axioms, definitions, theorem declarations, opaque declarations, quotient primitives, inductive groups, generated constructors, generated recursors, and recursor rule right-hand sides.  The executable accepts either a file path for local use or the Arena `$IN` path.

Typed outcomes are part of the checker API.  Acceptance means the artifact replays in the local kernel.  Rejection means the artifact lies inside the specified fragment and violates a kernel rule.  Unsupported input means the artifact uses a Lean feature outside the specified fragment.  Internal failure means the checker failed to classify the input, and the executable behavior for that case must be documented separately from Arena's accepted, rejected, and declined outcomes.

The export checker should use test-first development.  The first accepted tests should be tiny Lean modules exported by `lean4export`: a universe-polymorphic identity, an ordinary theorem, a small inductive declaration, a recursive definition compiled to ordinary definitions, a projection example, and a quotient example.  The first negative tests should be static NDJSON files derived from those accepted files by one deliberate mutation at a time: a theorem proof with the wrong type, a generated recursor with a wrong rule RHS, an unresolved dependency, an unsupported unsafe declaration, and an unsupported partial declaration.  This workflow makes the export artifact the unit under test, rather than treating the parser as an isolated serialization exercise.

Acceptance criteria:

- The code has a typed result for accepted, rejected, unsupported, and internal-failure outcomes.
- `leanlean-check-module` checks explicit root declarations from compiled Lean modules through `replayEnvironmentClosure`.
- The specification states the accepted `lean4export` NDJSON fragment.
- The repository has accepted NDJSON tests generated from `Faithfulness.ExportSmoke` and `Faithfulness.Accepted` by `lean4export` and checked by `leanlean-check-export`.
- The accepted export tests cover a custom inductive recursor, a theorem declaration, an opaque declaration, a raw natural literal, closed natural subtraction, quotient primitives, a subtype value, a compiled recursive list definition, and the gcd/parity arithmetic theorem.
- Generated rejection tests cover a theorem proof with the wrong type and a projection whose structure argument is ill-typed.
- Static export-checker tests cover supported-fragment rejection for `imax` normalization and bad constant-level unfolding.
- Export-backed self-check exports the named source-facing `LeanLean.Syntax` and `LeanLean.Kernel` roots and accepts them with `leanlean-check-export`.
- Unsupported-input tests cover unsupported parser or replay boundaries with readable source companions.
- `leanlean-check-export` supports the Arena input convention, translates accepted export records into declaration replay scripts, and returns `0` for accepted inputs, `1` for supported-fragment rejections, and `2` for unsupported inputs.
- Local smoke tests include an accepted exported artifact, a rejected supported-fragment artifact, and an unsupported artifact.
- Module-checker tests cover accepted roots, unsupported roots, and roots rejected inside the supported fragment.
- The repository includes a sample `lean-kernel-arena` checker configuration.

## Phase 13: Generated-Support Self-Check

Lean stores generated support declarations as ordinary environment constants.  The current self-check deliberately keeps the source-facing claim narrow: it checks the kernel declarations that correspond to this repository's source code and replays recursive `below` and `brecOn` support when those declarations need it.  Other generated declarations enter as typed dependencies or are excluded as roots, which prevents the checker from claiming coverage for generator classes that do not yet have a local specification.

This phase turns the exclusion boundary into work.  The first task is an inventory mode that reports every skipped generated declaration with its module, declaration kind, generator class, dependencies, and current replay result.  The second task is a generated-support self-check mode whose output distinguishes checked values, typed assumptions, unsupported classes, and local rejections.  That mode should not change the default source-facing self-check claim.

The admission order should follow dependency and proof risk.  Match helpers that elaborate to ordinary eliminator applications are the first target, followed by no-confusion helpers and constructor eliminators.  Sparse-case helpers come later because they can reach compilation-specific wrappers and primitive operations.  Derived instances and representation support should come last, because much of that code serves display or debugging rather than kernel reasoning, and the trusted role of each generated value must be stated before replay uses it.

Acceptance criteria:

- `leanlean-self-check` has a mode that inventories skipped generated declarations without attempting to admit them.
- The inventory groups generated declarations by class rather than by name-pattern folklore alone.
- A separate generated-support mode checks at least match helpers, no-confusion helpers, and constructor eliminators by written rules.
- Sparse-case helpers, derived instances, and representation support either check by written rules or remain explicit unsupported classes with counts.
- The default and module-closure self-check modes keep their source-facing claims and do not silently widen their trusted base.
- Tests fail if a generated-support class moves from unsupported to assumed without a specification entry and a replay test.

## Phase 14: Complete Replay Checker Boundary

This phase makes the checker boundary the main implementation target.  Lean's `Environment.replay` is the correct model for this boundary: it consumes a finite `ConstantInfo` map, skips unsafe and partial constants, recursively replays used constants, sends ordinary declarations to the kernel, reconstructs inductive blocks from type-former and constructor records, and postpones generated constructor and recursor records until it can compare them with the kernel-generated environment.  The local checker should match that shape for safe artifacts, even when its public input is `lean4export` NDJSON rather than an in-process Lean environment.

The core kernel and the replay checker are separate layers with one trusted claim.  The core kernel implements typing, conversion, declaration admission, inductive admission, primitive reductions, projections, quotient primitives, and generated recursor construction.  The replay checker implements artifact reconstruction, dependency ordering, safety policy, inductive grouping, generated-record comparison, and trusted-base accounting.  A complete external checker must specify and test both layers, because a bad reconstruction rule can invalidate a good type checker.

The first implementation task is a replay gap report.  The report must classify every safe, non-partial artifact declaration as checked, generated-compared, rejected, unsupported, skipped by policy, or assumed.  Classification must be dependency-aware before it uses temporary assumptions, because source-order artifacts can otherwise report false failures for declarations whose dependencies appear later in the supplied set.  The report must group failures by declaration kind, generated-support class, dependency shape, primitive dependency, and name-encoding issue.  The report should run over both loaded `ConstantInfo` closures and exported NDJSON artifacts, because the two paths expose different errors: the module path exposes Lean's internal declaration shape, while the export path exposes the independent checker input.

The second task is assumption burn-down.  Whole-artifact replay should not admit non-root definitions and theorem proofs as trusted bases.  A remaining assumption must be a named axiom, an explicitly imported base outside the checked artifact, or a deliberately trusted primitive package with a written rule.  Every other assumed declaration should become a checked declaration, a generated comparison, a policy skip, or an unsupported artifact with a specific reason.

The third task is name fidelity.  The current local syntax represents names as strings produced by `Lean.Name.toString`.  That representation is acceptable only if the specification states an injective encoding for every accepted export name and tests adversarial collisions.  The stronger foundation is to store structured Lean-style names in the kernel syntax, then print them only at diagnostic boundaries.

Acceptance criteria:

- A command reports replay gaps for a supplied module closure and for a supplied `lean4export` artifact.
- The report separates checked declarations, generated comparisons, unsupported declarations, supported-fragment rejections, policy skips, and assumptions.
- Whole-artifact export replay checks every safe ordinary declaration in the artifact closure, rather than checking selected roots and assuming the rest.
- Generated constructors and recursors are postponed and compared against regenerated local environment records with the same fields Lean replay treats as kernel-generated evidence.
- Unsafe and partial constants either follow Lean replay's skip policy or remain outside the external checker with a documented stricter rule and tests.
- Trusted-base output contains only named axioms, explicit imported bases, and specified primitive packages.
- Name handling is either structured or backed by an injective accepted-name encoding with collision tests.
- The default self-check claim moves from rooted replay to whole-artifact replay after generated support and primitive gaps no longer require trusted non-root definitions.

## Immediate Next Work

Ordinary universe polymorphism now covers inference, conversion, axioms, transparent and opaque definitions, theorem declarations, inductive blocks, generated constructors, generated recursors, low-level quotient primitives, core projections for one-constructor inductives, raw literal expressions, and the `PEmpty`/`PUnit` sort-polymorphic subsingleton shapes.  The kernel reserves `Sort 0` for `Prop`, uses symbolic `imax` for dependent function sorts, applies proof irrelevance to terms with proposition types equal by conversion, supports proposition-valued inductives with the indexed syntactic subsingleton-elimination rule, admits mutual inductive blocks atomically, records primitive, theorem, projection, reducibility, and structure metadata in the environment, and has ordered and dependency-aware declaration replay paths plus executable module and export checkers.  The immediate work is to add replay gap reporting, use it to burn down trusted non-root assumptions, and then check the lowest-risk generated classes without weakening the current source-facing self-check claim.
