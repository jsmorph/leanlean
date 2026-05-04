# Minimal Principled Checker Design

## Boundary

MPC is a canonical kernel declaration checker.  It takes a checked environment and a declaration in a small kernel language, then either returns an extended checked environment or rejects the declaration.  It does not parse Lean source, elaborate terms, reconstruct source recursion, read `.olean` files, read NDJSON exports, compare redundant generated records, choose roots, apply unsafe policy, or produce gap reports.

The boundary follows the kernel-facing shape described in [Minimal Kernel Subset](spec.md).  Levels, expressions, contexts, substitution, inference, checking, conversion, and declaration admission belong to MPC.  Artifact representation, module loading, export parsing, root selection, and diagnostic continuation belong to adapters that call MPC.

Inductive blocks are inside MPC because they are primitive kernel declarations.  Admitting an inductive block creates the type constructors, constructors, recursors, and iota rules used by later terms.  Generated constructor and recursor records in an export artifact are outside MPC because they duplicate facts that should follow from the inductive block.

## Core API

The MPC API should expose a checked environment and a small set of operations.  The operations should accept canonical kernel syntax, return checked results, and report typed errors.  Higher-level tools may translate their own input forms into this syntax, but they should not add kernel behavior through the translation layer.

```text
emptyEnv  : Env

checkLevel : Env -> LevelContext -> Level -> Result Unit
infer      : Env -> LevelContext -> Context -> Expr -> Result Expr
check      : Env -> LevelContext -> Context -> Expr -> Expr -> Result Unit
defEq      : Env -> LevelContext -> Context -> Expr -> Expr -> Result Unit
normalize  : Env -> LevelContext -> Context -> Expr -> Result Expr

addDecl    : Env -> Declaration -> Result Env
replay     : Env -> List Declaration -> Result Env
```

`Declaration` is the only trusted input form for environment growth.  It contains axioms, transparent definitions, opaque definitions, theorem declarations, quotient primitive packages, projection declarations if projections remain primitive declarations, and inductive blocks.  An inductive block enters as one declaration; `addDecl` derives its generated constants and computation rules internally.

## Rule Packages

The word "extension" names design discipline, not a dynamic plugin system.  A rule package describes a coherent part of the kernel theory, with its expression forms, declaration forms, environment metadata, typing rules, and reduction rules stated together.  A checker configuration is a statically assembled set of rule packages whose interactions are specified before implementation.

| Rule package | MPC role |
| --- | --- |
| Base dependent type theory | Universes, bound variables, constants, application, lambda abstraction, dependent function types, `let`, contexts, substitution, inference, checking, and conversion. |
| Declaration admission | Axioms, transparent definitions, opaque definitions, and theorem declarations.  A theorem proof checks against a proposition, and a theorem constant does not unfold during conversion. |
| `Prop` | `Sort 0`, proof irrelevance, proposition-valued function behavior, proposition-valued inductives, and elimination restrictions. |
| Inductive blocks | Parameters, indices, mutual blocks, nested positive occurrences, positivity, universe rules, constructor generation, recursor generation, and iota reduction. |
| Quotients | Low-level `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, `Quot.sound`, and the quotient computation rule. |
| Core projections | Lean's projection expression, projection typing, projection reduction, projection declarations, and the specified structure eta fragment. |
| Literals | Raw natural and string literals, their types, and the reduction behavior that the selected kernel theory assigns to them. |
| Primitive reductions | Version-specific kernel-overridden reductions with source evidence, declaration-shape checks, implementation tests, and export tests. |
| Exact conversion | Beta, delta, zeta, iota, projection, quotient, eta, proof irrelevance, primitive reductions, universe equality, and their interactions. |
| Resource discipline | Termination, fuel, sharing, and bounded error reporting for large terms and large declaration sets. |

Rule packages are not independent in the informal sense.  Inductives interact with `Prop`, universe comparison, projections, eta, primitive literals, and proof irrelevance.  The rule-package model is useful because it forces each trusted addition to state the environment data it owns and the conversion rules it adds.

## Current Inventory

The current implementation already contains most of the rule packages needed for the first MPC, but they live inside the broader LeanLean checker rather than inside a standalone `MPC` library.  This inventory records package status, not extraction status.  A package marked implemented may still need cleanup before peer development starts, because the current code may share data types or entry points with import, replay, diagnostics, or export-checker concerns.

| Rule package | Current status | Current evidence | MPC extraction note |
| --- | --- | --- | --- |
| Base dependent type theory | Implemented for the current expression grammar. | `LeanLean/Syntax.lean` defines `Level`, `Literal`, and `Expr`; `LeanLean/Kernel.lean` implements `infer`, `inferApp`, `inferSpine`, `checkHasTypeIn`, `whnf`, and `normalize`.  The regression suite exercises raw terms, literals, malformed entries, and differential term comparisons. | Extract levels, expressions, contexts, substitution, inference, checking, weak-head reduction, and normalization into the base library before any adapter code depends on them. |
| Contexts and substitution | Implemented and historically tested. | `Expr.instantiateManyFrom`, `Expr.instantiateMany`, `Telescope.bindForall`, `Telescope.bindIndependentForall`, `Telescope.instantiateTypes`, and `lookupCtx` implement the current de Bruijn and telescope rules.  `substitutionTests`, `telescopeTests`, and generated-declaration validation cover the earlier failure modes. | Keep this package in base MPC rather than inside the inductive package, because every later rule uses the same context and simultaneous-substitution invariants. |
| Universe checking | Implemented for the current level language. | `Level.normalize`, `Level.defEq`, `Level.atMostOne`, `inferSortOfPi`, `inferSort`, `checkLevelParamsUnique`, and `checkLevelAtMost` cover `0`, parameters, successor, `max`, `imax`, sort inference, and level-parameter closure.  `universeTests` and the accepted faithfulness corpus cover polymorphic definitions and inductives. | Keep universe comparison in base MPC.  The current sort-polymorphic inductive restriction belongs to the inductive package because it governs declaration admission rather than general level equality. |
| Declaration admission | Implemented. | `ConstantInfo`, `ConstantKind`, `addAxiomWithLevels`, `addDefinitionWithHintWithLevels`, `addOpaqueDefinitionWithLevels`, `addTheoremWithLevels`, and `ConstantInfo.value?` implement checked environment growth for axioms, transparent definitions, opaque definitions, theorem declarations, and reducibility hints.  `declarationScriptTests`, `declarationReplayTests`, and opacity tests cover the behavior. | MPC should keep only canonical declaration admission here.  Generated constructor checks, generated recursor checks, dependency-aware replay, and export primitive checks should move to adapters or separate audit packages. |
| `Prop` | Implemented for the specified fragment. | `inferSortOfPi`, `inductiveIsProp`, `computeAllowsLargeElim`, `checkDefEqIn`, and `checkProofIrrelevantExprEq` implement `Sort 0`, proposition-valued functions, proof irrelevance, and proposition-elimination restrictions.  Accepted and rejected faithfulness examples cover theorem declarations, proposition recursors, forbidden data elimination, and proof irrelevance. | Keep `Prop` as a rule package that the inductive package can depend on.  Do not bury proof irrelevance inside generic conversion code without naming the package in the checker configuration. |
| Inductive blocks | Implemented for a broad specified subset. | `addInductiveBlock`, `addKernelInductive`, `checkInductiveHeader`, `checkDataUniverseBounds`, `checkConstructorTargets`, `positiveFlagsFor`, `buildRecursorFamily`, `buildRecursorType`, and `reduceRecursorApp` cover parameters, indices, dependent fields, mutual blocks, nested positive occurrences, recursor generation, and iota reduction.  `kernelInductiveDeclTests`, `recursorGenerationTests`, rejected positivity examples, and differential recursor comparisons exercise the package. | This is the largest MPC package.  Extraction should separate canonical inductive admission from artifact-only generated-constructor and generated-recursor comparison. |
| Sort-polymorphic inductive results | Partial by design. | The checker accepts `Prop`, definitely data-valued results, empty sort-polymorphic inductives, and one-constructor/no-field sort-polymorphic inductives.  This covers the current `PEmpty` and `PUnit` needs while preserving rejection for data-carrying ambiguous `Sort u` declarations. | Treat this as an open subpackage of inductive admission.  Full Lean parity needs a written rule for broader accepted shapes before implementation expands. |
| Quotients | Implemented for the low-level kernel primitives. | `addQuotPrimitives`, `addPrimitive`, `reduceQuotLiftApp`, and `reducePrimitiveApp` implement `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, `Quot.sound`, and the `Quot.lift` computation rule.  Quotient accepted examples and `QuotRelationMismatch` rejection cover the current rule. | Keep only the low-level quotient primitive package in MPC.  The higher-level `Quotient` API is library code or adapter input once the low-level constants exist. |
| Core projections | Implemented for the specified projection and eta fragment. | `projectionTarget`, `projectionInfo`, `projectionFieldTypeExpr`, `inferProjection`, `reduceProjection`, `addProjection`, `isStructureEtaExpansion`, and structure metadata checks implement projection typing, projection reduction, projection declarations, inherited-field metadata, and narrow structure eta.  Projection, structure metadata, and differential projection tests cover the package. | Split projection expressions and projection declarations from structure metadata during extraction.  Structure metadata can be an adapter-facing support package unless MPC keeps structure eta as a named conversion rule. |
| Literals | Partial. | Raw natural literals type-check as `Nat`, remain raw under normalization, compare with constructor spines by numeric value, and drive `Nat.rec` reduction.  String literals type-check as `String` but remain neutral under local reduction.  `literalTests`, primitive reduction tests, and accepted literal examples cover the current behavior. | Natural literals can enter MPC with the current rule.  Full string-literal computation remains open because it needs string, character-list, byte-array, recursive, and primitive support beyond the current specification. |
| Primitive reductions | Partial and intentionally conservative. | The admitted table covers `Nat.add`, `Nat.mul`, `Nat.pow`, `Nat.sub`, `Nat.beq`, and `Nat.ble`, with declaration-shape checks before reduction.  `primitive-inventory.md` lists source-backed candidates such as `Nat.decEq`, `Nat.decLe`, `Nat.decLt`, `Nat.blt`, and `Nat.gcd`. | MPC should take primitive reductions as versioned packages.  A primitive enters only after source evidence, a written rule, a declaration-shape check, implementation tests, and an artifact test. |
| Exact conversion | Implemented for the specified fragment, with remaining parity work. | `checkDefEqIn`, `checkStructuralDefEqIn`, `checkFunctionEtaExpansion`, `checkProofIrrelevantExprEq`, `whnf`, `normalize`, recursor reduction, quotient reduction, projection reduction, literal comparison, and primitive reduction implement the current conversion relation.  Regression tests and differential comparisons cover many combinations. | Treat this as the integration package for all reduction rules.  Peer development should add adversarial conversion tests before changing rules, because most serious bugs appear at package boundaries. |
| Resource discipline | Partial. | `replayDeclarationsWithFuel` bounds dependency-aware replay, and checker outcomes distinguish internal failures from rejection and unsupported input.  Development notes still record slow replay points in the earlier Omega stress artifact. | Standalone MPC needs explicit resource policy for normalization, conversion, and replay before it becomes an arbitrary-artifact checker.  Resource failure should produce a classified checker result rather than host nontermination or stack failure. |

Two current implementation areas should stay out of MPC even though they are important for the larger checker.  The Lean importer, export parser, rooted self-check policy, gap reports, generated-support inventory, generated-constructor comparison, and generated-recursor comparison are adapter or audit work.  They should consume MPC environments and declarations after extraction rather than becoming rule packages in the kernel checker.  This separation keeps the peer-development target small enough to review while preserving a path to `.olean` and NDJSON checking.

## Artifact Adapters

`.olean` checking and NDJSON export checking should be built as adapters over MPC.  An adapter parses artifact data, translates names, levels, expressions, and declarations into canonical MPC syntax, calls `MPC.replay`, and audits artifact-specific redundancy.  If an artifact contains an ordinary definition or theorem, MPC checks the value; if an artifact contains generated constructor or recursor records, the adapter compares them with what MPC generated from the inductive block.

| Adapter component | Role |
| --- | --- |
| Structured names | Preserve Lean names with string and numeric components, private-name components, quoted components, and macro scopes without relying on non-injective printing. |
| `.olean` or NDJSON reader | Parse artifact syntax into levels, expressions, declarations, and metadata records.  The reader adds no kernel rules. |
| `ConstantInfo` translation | Translate Lean declaration records into canonical MPC declarations when the record represents a kernel declaration. |
| Inductive grouping | Group artifact records for type formers and constructors into one inductive block before calling MPC. |
| Generated-record audit | Compare exported generated constructors and recursors against the constants and metadata generated by MPC.  This prevents redundant artifact records from becoming trusted declarations. |
| Dependency replay | Order declarations, separate checked declarations from imported bases, and reject unresolved dependencies. |
| Unsafe and partial policy | Reject, skip, or trust unsafe and partial declarations according to an explicit external-checker policy.  This policy is not a kernel typing rule. |
| Environment-extension extraction | Read metadata that affects translation or replay, such as structure and projection metadata.  Elaborator, notation, tactic, and display metadata stay outside MPC unless a rule package gives them a trusted role. |
| Diagnostics | Report unsupported input, kernel rejection, trusted-base assumptions, policy skips, and artifact redundancy errors without changing acceptance. |

Generated match helpers, no-confusion helpers, constructor eliminators, equation-compiler output, derived instances, and representation support are not MPC rule packages by name.  After elaboration, they should appear as ordinary definitions or theorems, except where the artifact stores redundant generated records.  If one of those declarations fails to check, the cause should be a missing MPC rule package, a missing documented primitive reduction, a missing dependency, or an adapter translation error.

## Higher-Level Use

An export checker should follow a narrow pipeline.  It parses the artifact, translates artifact syntax into canonical MPC declarations, groups inductives, calls `MPC.replay`, and then audits redundant generated records against the resulting environment.  Acceptance means the canonical declarations checked and the redundant artifact records agreed with the generated kernel data.

A `.olean` checker follows the same shape, but its parser and metadata reader differ.  It must decide how to handle imported module bases, unsafe declarations, partial declarations, and environment extensions before it calls MPC.  Those decisions determine checker policy; they do not alter the kernel language.

A source elaborator can also target MPC.  It elaborates source commands into canonical declarations, compiles source recursion into ordinary kernel definitions, emits inductive blocks for source inductives, and sends the resulting declarations to `addDecl` or `replay`.  MPC sees only the kernel declaration script, not the source command that produced it.

## Relation to Lean

Lean itself exposes a fixed kernel-facing declaration API rather than a user-extensible kernel rule system.  Its declaration type contains axioms, definitions, theorem declarations, opaque declarations, quotient initialization, mutual-definition artifacts for unsafe or partial code, and inductive declarations.  Its trusted environment entry point type-checks one such declaration and returns a new environment.

Lean's replay layer is separate from declaration admission.  Replay reconstructs kernel declarations from stored environment records, sends them to the kernel, postpones generated constructor and recursor records, and checks those postponed records against the constants generated by inductive admission.  That pattern matches the MPC split: canonical declaration checking belongs to the kernel, while exported or stored environment redundancy belongs to an adapter.

The rule-package organization proposed here is therefore an implementation and specification strategy for this project.  It should make the trusted theory explicit and keep adapters from becoming hidden kernel extensions.  A final checker claim should name both parts: the MPC rule-package configuration being trusted, and the adapter policy used to translate `.olean` or NDJSON artifacts into that configuration.
