# MPC Design

## Purpose

MPC is a checked-declaration engine for a canonical Lean-like kernel language.  Its job is to grow a checked environment by applying specified rules to declarations under a static manifest.  The detailed typing and conversion rules live in [MPC Specification](spec.md), while this document records the code architecture and boundary discipline that keep those rules reviewable.

The design separates the kernel checker from every external representation.  MPC accepts canonical names, levels, expressions, contexts, and declarations.  A tool that reads Lean exports, chooses roots, reuses checked declarations, emits telemetry, or reports diagnostics must translate into that canonical input before it can ask MPC to check anything.

## Boundary

MPC owns the trusted judgments: level closure and comparison, expression inference, expression checking, definitional equality, weak-head reduction, normalization, declaration admission, and ordered declaration replay.  It also owns the environment metadata required by enabled rule packages, such as inductive recursor metadata, primitive equality and quotient kinds, projection metadata, and primitive Nat declaration-shape checks.  A successful MPC operation returns an extended `Env` or a checked type; a failed operation returns a structured `Error`.

MPC does not own Lean source syntax, elaboration, `.olean` parsing, NDJSON parsing, root discovery, unsafe or partial policy, generated-record audit policy, telemetry, diagnostic continuation, or persistent caches.  Those jobs belong to adapters and drivers.  This boundary is the main engineering constraint: an adapter may reject, translate, order, reuse, or report, but it must not add a typing or conversion rule.

## Architecture

The root executable and library files are intentionally few.  `MPC.lean` imports the public MPC library, `MPCTest.lean` runs the native regression suite, `CheckMPCExport.lean` is the NDJSON export-checker executable, and `ExportRoots.lean` is the root-lister used by export-backed self-checks.  The Lake file builds one MPC library, four fixture libraries, and those three executables.  Package internals live under `MPC/`, while generated-export fixtures live under `MPCFixtures/`.

| Area | Files | Responsibility |
| --- | --- | --- |
| Core language | `MPC/Name.lean`, `MPC/Level.lean`, `MPC/Expr.lean`, `MPC/Context.lean` | Names, universe levels, expressions, contexts, lifting, and substitution. |
| Results and manifests | `MPC/Error.lean`, `MPC/Manifest.lean`, `MPC/Configs/**` | Typed errors and static rule-package selections. |
| Environment and declarations | `MPC/Env.lean`, `MPC/Declaration.lean`, `MPC/Replay.lean` | Constants, declaration data, environment indexing, admission dispatch, and ordered replay. |
| Checking and conversion | `MPC/Check.lean`, `MPC/Normalize.lean`, `MPC/DefEq.lean` | Inference, checking, weak-head normalization, full normalization, and conversion dispatch. |
| Rule packages | `MPC/Packages/**` | Package-owned declaration forms, metadata, side conditions, typing rules, and reduction rules. |
| Adapters | `MPC/Adapters/**` | Native script input, NDJSON lowering, generated-record audits, and checked-layer persistence. |
| Fixtures and scripts | `MPCFixtures/**`, `tools/**` | Generated-export fixtures, export regression scripts, self-check scripts, and stress profiling. |

The checker spine should stay small.  `Check.lean` and `Normalize.lean` coordinate recursive judgments and call package-owned functions when a manifest enables them.  Package-specific recognition should live with the package that introduces the behavior, because that location keeps the rule, required metadata, and rejection reasons together.

## Rule Packages

A rule package is a static part of the checker theory, not a runtime plugin.  A manifest selects a known combination of packages, and `Manifest.validate` rejects combinations that cannot make sense, such as theorem admission without `Prop`.  Package interactions should be explicit at the manifest and dispatch points, because most checker bugs arise where conversion, `Prop`, inductives, projections, and primitive reductions meet.

| Package | Current role |
| --- | --- |
| Declaration admission | Axioms, transparent definitions, opaque definitions, theorem declarations, and checked environment growth. |
| Literals | Raw natural literals, neutral string literals, Nat constructor-spine comparison, and literal typing requirements. |
| `Prop` | `Sort 0`, theorem admission, proposition-valued functions, proof irrelevance, and Prop-inductive prerequisites. |
| Equality | Primitive `Eq`, `Eq.refl`, `Eq.rec`, checked transparent `Eq.ndrec`, and reflexive equality-rec reduction. |
| Quotients | Low-level `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, `Quot.sound`, and quotient-lift reduction. |
| Projections | Core projection expressions, projection typing, projection reduction, Prop projection restriction, and structure eta for the supported fragment. |
| Primitive Nat reductions | Lean 4.29-backed reductions for the admitted Nat primitive table after declaration-shape checks. |
| Function eta | Conversion between a function and its eta expansion under the active context and manifest. |
| Inductives | Simple, indexed, nested, Prop-valued, large-elimination, and mutual inductive admission, recursor generation, positivity, and iota reduction. |

Rule packages may share helper APIs, but the ownership should remain clear.  Inductive positivity belongs to the inductive package, even when it depends on covariance inferred from earlier inductives.  Primitive Nat computation belongs to the primitive package, even though normalization calls it before ordinary delta unfolding.  A future package should state the metadata it owns before adding a new dispatch path.

## Adapters

The export adapter reads the accepted `lean4export` NDJSON fragment and lowers it to canonical MPC declarations.  It translates Lean names injectively, translates levels and expressions, groups inductive records into MPC inductive declarations, installs equality and quotient primitives when their export records require them, and sends the resulting script to replay.  Generated constructor and recursor records remain redundant artifact records, so the adapter audits them against the constants and metadata produced by MPC rather than admitting them as independent declarations.

The script and NDJSON adapters have different input syntax, but they share the same rule: they call MPC only with canonical declarations.  Parser failures and unsupported artifact forms produce adapter errors before declaration replay.  Replay failures after lowering are checker rejections, because at that point the adapter has already chosen an MPC declaration script.

`ExportRoots.lean` is a driver-side root selector.  It loads a compiled Lean module, filters source-facing or self-check declarations, and prints root names for `lean4export`.  Its classification affects which artifact gets generated for a self-check run, but it does not change the checker result for a produced artifact.

## Checked Layers

Checked layers are adapter-side reuse.  A layer stores accepted environment entries and declaration-content keys so a later replay can skip a declaration whose name and lowered content match a checked entry.  Reuse is valid only when the cached declaration is alpha-equivalent to the target declaration, or when a content key proves that the lowered declaration has already been checked.

SQLite cache mode uses the same principle while keeping the content table on disk.  `--cache-layer` mutates a SQLite DB, checks misses, runs the generated-record audit, and commits new rows only after the target artifact accepts.  A stale cache can reject when the same Lean name appears with different lowered content after source changes; this is an adapter-level conflict, and `MPC_CACHE_DB=` gives a cold self-check run.

## Drivers and Tests

`lake exe mpctest` is the native regression suite.  It exercises rule packages directly through MPC data, checks adapter behavior, and covers checked-layer alpha reuse.  A native test is the right place for a small rule-package invariant because it avoids export format noise.

`tools/mpc-export-tests.sh` is the maintained generated-export regression path.  It checks the GCD/parity arithmetic fixture, nested-indexed fixtures, and the mutual even/odd fixture through `lean4export` and `mpc-check-export`.  These tests exercise the adapter boundary and generated-record audits over artifacts that Lean produced.

`tools/mpc-export-self-check.sh` exports and checks MPC's own non-adapter modules with source-facing roots.  It uses `MPC_CACHE_DB` by default because self-check artifacts share large dependency closures, but it can run cold by setting `MPC_CACHE_DB=`.  `tools/mpc-omega-stress.sh` is a profiling driver for proof-heavy artifacts and generated-recursion boundaries; it records a reportable outcome rather than defining a required acceptance test.
