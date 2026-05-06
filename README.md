# MPC

MPC is a specification-first Lean 4 kernel-checker experiment.  It checks a canonical kernel declaration language through explicit rule packages selected by manifests.  The main reference documents are [MPC Specification](spec.md), [MPC Design](design.md), [MPC Performance Notes](perf.md), and [Development Notes](devnotes.md).

## Goals

MPC aims to make the trusted checker boundary small, explicit, and reviewable.  The checker should accept or reject canonical declarations by applying specified kernel rules, while artifact parsing, root selection, generated-record audits, telemetry, and caching remain outside the kernel boundary.  The project also aims to check substantial Lean-generated artifacts, including its own compiled MPC modules, without turning adapter policy or performance machinery into hidden type-theory rules.

## Design

The core checker grows an `Env` by replaying `Declaration` values under a selected `Manifest`.  The trusted operations are inference, checking, definitional equality, normalization, declaration admission, and declaration replay over MPC's own names, levels, expressions, contexts, and constants.  Rule packages own the expression forms, declaration forms, metadata, side conditions, and reductions they introduce, while the checker spine dispatches among those packages.

| Area | Files | Responsibility |
| --- | --- | --- |
| Core language | `MPC/Name.lean`, `MPC/Level.lean`, `MPC/Expr.lean`, `MPC/Context.lean` | Names, universe levels, expressions, contexts, and substitution. |
| Environment and replay | `MPC/Env.lean`, `MPC/Declaration.lean`, `MPC/Replay.lean` | Checked constants, declaration records, environment growth, and ordered replay. |
| Checking and conversion | `MPC/Check.lean`, `MPC/Normalize.lean`, `MPC/DefEq.lean` | Inference, checking, weak-head reduction, normalization, and definitional equality. |
| Rule packages | `MPC/Packages/**` | Declaration admission, literals, `Prop`, equality, quotients, projections, primitive Nat reductions, function eta, and inductives. |
| Manifests | `MPC/Manifest.lean`, `MPC/Configs/**` | Static rule-package selections for PoC fragments and the Lean 4.29-oriented configuration. |
| Adapters | `MPC/Adapters/**`, `CheckMPCExport.lean`, `ExportRoots.lean`, `MigrateLayer.lean` | Native script input, `lean4export` NDJSON input, generated-record audits, SQLite checked-layer persistence, checked-layer migration, command-line checking, and export-root selection. |
| Fixtures and drivers | `MPCFixtures/**`, `MPCTest.lean`, `tools/**` | Native regression tests, generated-export fixtures, export self-checks, GCD replay, and Omega stress profiling. |

Adapters translate external artifacts into canonical declarations before calling MPC.  The export adapter parses `lean4export` NDJSON, reconstructs MPC syntax, groups inductive records into declarations, calls replay, and compares exported generated records against the constants MPC generated.  The checked-layer adapter reuses declarations through a SQLite store, but reuse is an adapter decision based on declaration groups and generated constants, not a checker rule.

## Status

The repository now contains only MPC code and the files needed to build, drive, and test it.  The old LeanLean executables, faithfulness harness, Arena static fixtures, and stale paper or traceability documents have been removed.  The maintained external surface is the native regression executable, the NDJSON export checker, the export-root lister, the generated fixture scripts, and the export-backed self-check script.

| Surface | Status |
| --- | --- |
| Native regression suite | `lake exe mpctest` passes and covers the core rule packages, adapters, checked layers, and name encoding. |
| Export checker | `mpc-check-export` accepts the maintained generated fixtures and supports text, JSONL, profile JSONL, declaration profiling, and SQLite checked-layer reuse.  With `--cache-layer`, it streams the NDJSON file and replays declarations against the on-demand SQLite cache. |
| Export fixtures | `MPCFixtures` contains the arithmetic GCD/parity example, nested-indexed inductive examples, a mutual even/odd example, and the Omega stress module. |
| Export self-check | `tools/mpc-export-self-check.sh` covers every non-adapter MPC module with source-facing roots and uses `MPC_CACHE_DB` for persistent checked-layer reuse. |
| Performance work | `perf.md` records the current profile data, major optimizations, and remaining proof-heavy replay costs. |
| Known caveat | A stale cache DB can reject because the same Lean name may have different exported content after source changes; run with `MPC_CACHE_DB=` for a cold self-check.  SQLite v2 cache files must be migrated with `mpc-migrate-layer` or replaced with a fresh `.db` path. |

## Running

Run the native test suite with `lake exe mpctest`.  Build the export checker with `lake build mpc-check-export`, then run `.lake/build/bin/mpc-check-export <export.ndjson>`.  Build the root lister with `lake build mpc-export-roots`, then run `.lake/build/bin/mpc-export-roots --module MPC.Name --self-check`.

The current tool scripts are `tools/mpc-export-tests.sh`, `tools/mpc-export-gcd.sh`, `tools/mpc-export-self-check.sh`, and `tools/mpc-omega-stress.sh`.  The export scripts require a matching `lean4export` binary; set `MPC_LEAN4EXPORT` when it is not on `PATH`.  The export self-check script writes a SQLite checked-layer cache to `.tmp/mpc-self-check-cache.db` by default, uses `MPC_CACHE_DB` when supplied, and disables cache use when `MPC_CACHE_DB` is set to the empty string.

Build the cache migrator with `lake build mpc-migrate-layer`, then run `.lake/build/bin/mpc-migrate-layer <source-v2.db> <target-v3.db>` to convert an old bulk SQLite cache into the on-demand format.  The migrator does not recheck declarations; it rewrites accepted cache groups from the old `env` and `content` tables into declaration groups.  `mpc-check-export --cache-layer` refuses v2 files so that large probes do not fall back to the old bulk-cache behavior.
