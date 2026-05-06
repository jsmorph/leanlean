# MPC

This repository contains MPC, a specification-first Lean 4 kernel-checker experiment.  The checker is organized around explicit rule packages selected by manifests.  The main specification is [`spec.md`](spec.md), and the development journal is [`devnotes.md`](devnotes.md).

Run the native regression suite with `lake exe mpctest`.  Build the export checker with `lake build mpc-check-export`, then run `.lake/build/bin/mpc-check-export <export.ndjson>`.  The export scripts under `tools/` require a matching `lean4export` binary; set `MPC_LEAN4EXPORT` when it is not on `PATH`.

The current tool scripts are `tools/mpc-export-tests.sh`, `tools/mpc-export-gcd.sh`, `tools/mpc-export-self-check.sh`, and `tools/mpc-omega-stress.sh`.  The export self-check script uses `MPC_CACHE_DB` when supplied, writes a SQLite checked-layer cache to `.tmp/mpc-self-check-cache.db` by default, and disables cache use when `MPC_CACHE_DB` is set to the empty string.  The stress script is a profiling target rather than an acceptance test.
