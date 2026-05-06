# MPC Design

## Boundary

MPC is a checked-declaration engine over a small kernel language.  It receives an `Env`, a `Manifest`, and canonical `Declaration` values, then returns an extended `Env` or an `Error`.  Its trusted behavior is exactly the rule packages enabled by the manifest and specified in [MPC Specification](spec.md).

Adapters translate external inputs into canonical MPC declarations before calling the checker.  The export adapter reads `lean4export` NDJSON, reconstructs names, levels, expressions, and declarations, groups inductive records, and audits generated records against the declarations MPC creates from inductive blocks.  The checked-layer adapter stores accepted declarations for reuse, but the replay decision still compares declaration names and alpha-equivalent content before treating a cached declaration as present.

## Code Organization

| Area | Files | Role |
| --- | --- | --- |
| Core syntax | `MPC/Name.lean`, `MPC/Level.lean`, `MPC/Expr.lean`, `MPC/Context.lean` | Names, universe levels, expressions, contexts, substitution, and context lookup. |
| Checked environment | `MPC/Env.lean`, `MPC/Declaration.lean`, `MPC/Replay.lean` | Constants, declarations, environment growth, and declaration replay. |
| Checking and conversion | `MPC/Check.lean`, `MPC/Normalize.lean`, `MPC/DefEq.lean` | Inference, checking, weak-head reduction, normalization, and definitional equality dispatch. |
| Rule packages | `MPC/Packages/**` | Declaration forms, metadata, typing rules, and reduction rules selected by manifests. |
| Manifests | `MPC/Manifest.lean`, `MPC/Configs/**` | Static package selection for PoC fragments and the current Lean 4.29-oriented configuration. |
| Adapters | `MPC/Adapters/**`, `CheckMPCExport.lean`, `ExportRoots.lean` | Script input, NDJSON export input, checked-layer persistence, command-line checking, and export-root selection. |
| Fixtures and tests | `MPCFixtures/**`, `MPCTest.lean`, `tools/**` | Native regression tests, generated-export fixtures, export self-checks, GCD replay, and Omega stress profiling. |

The rule-package files should own the environment metadata and reduction rules they introduce.  `Normalize.lean` and `Check.lean` may dispatch across packages, but package-specific recognition and side conditions should live with the package.  This organization keeps the checker spine small while making package interactions visible at the dispatch points.

## Drivers

`lake exe mpctest` runs the native regression suite.  `mpc-check-export` checks a `lean4export` NDJSON artifact through the export adapter, with optional telemetry and SQLite checked-layer reuse.  `mpc-export-roots` loads a compiled Lean module and prints source-facing roots for export-backed self-checks.

The maintained shell drivers live in `tools/`.  `tools/mpc-export-tests.sh` checks the generated arithmetic, nested-indexed, and mutual-inductive fixture exports.  `tools/mpc-export-self-check.sh` exports and checks the current MPC modules, using `MPC_CACHE_DB` when a persistent checked-layer cache should be shared across runs.  `tools/mpc-omega-stress.sh` remains a profiling target for proof-heavy and generated-recursion boundaries.
