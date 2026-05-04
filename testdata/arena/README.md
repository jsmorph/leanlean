# Arena Fixture Copies

This directory contains selected fixtures copied from the Lean Kernel Arena test suite at <https://github.com/leanprover/lean-kernel-arena/tree/master/tests>.  The generated source cases live under `Faithfulness/Arena`; this directory contains static malicious export files that ordinary Lean source should not generate.

The copied fixtures are deliberately narrow.  `level-imax-normalization.ndjson` checks that the level normalizer distinguishes `imax 0 v` from `succ (imax 0 v)`.  `constlevels.ndjson` checks that bad universe-argument counts during unfolding reject instead of being treated as successful delta reduction.  Both are expected to produce the checker outcome `rejected`.

Run `tools/arena-smoke.sh` for the local static Arena smoke test.  The script uses Arena-style `$IN` input rather than a positional file path.  `arena/leanlean-checker.sample.yaml` is the sample checker entry for an Arena checkout.
