# MPC Performance Notes

## Baseline

The first full GCD replay profile used `mpc-check-export --stats-jsonl` against `.lake/build/export-tests/mpc-gcd-parity-arithmetic.ndjson`.  It accepted 493 declaration entries with environment size 571.  The measured declaration replay time was 597,416 ms, or about 9 minutes and 57 seconds.

| Prefix | Declarations | Baseline ms |
|---:|---:|---:|
| 320 | 320 | 30,373 |
| 400 | 400 | 119,030 |
| 430 | 430 | 159,998 |
| 475 | 475 | 364,037 |
| 493 | 493 | 597,416 |

The profile is concentrated near the end of the artifact.  Declarations 400 through 492 consume 478,386 ms, about 80 percent of total replay time.  Names containing `gcd` consume 508,686 ms, about 85 percent of total replay time.

| Index | Elapsed ms | Declaration |
|---:|---:|---|
| 479 | 116,057 | `Nat.Coprime.gcd_mul_left_cancel` |
| 491 | 54,148 | `LeanLeanFaithfulness.ExportArithmetic.gcd_right_two_of_odd` |
| 465 | 50,155 | `Nat.gcd_one_left` |
| 474 | 44,715 | `Nat.gcd_mul_left` |
| 492 | 33,412 | `LeanLeanFaithfulness.ExportArithmetic.gcd_sum_diff_eq_one` |
| 427 | 29,889 | `Nat.gcd_dvd` |
| 462 | 24,777 | `Nat.gcd_assoc` |
| 397 | 23,317 | `Nat.gcd_rec` |
| 466 | 22,310 | `Nat.gcd_one_right` |
| 473 | 17,620 | `Nat.mul_mod_mul_left` |

## Initial Suspects

| Area | Observation | Next check |
|---|---|---|
| Application spines | `Expr.getAppFnArgs` builds the argument list with repeated append.  `whnf` calls this on every application it inspects. | Replace it with an accumulator and compare prefix replay time. |
| Conversion fallback order | `defEq` tries structural comparison, then eta in both directions, then proof irrelevance.  Proof-heavy data applications may pay for failed eta before the proof-irrelevance path succeeds. | Add counters for `defEq`, `whnf`, eta attempts, proof-irrelevance attempts, and success counts before changing the order. |
| Nat primitive reductions | `Nat.add` has symbolic right-argument rules, while `Nat.mul`, `Nat.pow`, and `Nat.sub` currently reduce only when both arguments are numeric.  Lean reduces symbolic right-zero cases such as `Nat.mul n 0`, `Nat.pow n 0`, and `Nat.sub n 0`. | Add only the source-backed right-argument cases that follow the existing logical equations. |
| Environment lookup and unfolding | The environment is a list, and `whnf` repeatedly finds constants and unfolds transparent definitions.  The current environment is small, but late proof replay can multiply these lookups. | Instrument `Env.find?`, delta unfolding, recursor reduction, and primitive reduction counts before changing representation. |

`Nat.gcd` remains outside MPC primitive reduction.  The GCD profile identifies the proof region that dominates replay time, but it does not justify adding a library-level arithmetic operation to conversion.

## Application Spine Decomposition

`Expr.getAppFnArgs` now builds the argument spine with an accumulator instead of repeated append.  This removes a local quadratic operation from a hot utility, but the prefix-400 GCD measurement did not improve.  The result suggests that the current replay cost is dominated by conversion work inside large proof terms rather than by spine-list construction alone.

| Run | Prefix | Measured ms | Baseline ms | Change |
|---|---:|---:|---:|---:|
| Accumulator spine | 400 | 119,122 | 119,030 | +92 |

The measurement is within run-to-run noise.  Keep the implementation because it is the right asymptotic shape and has no semantic effect, but do not treat it as a solution to the GCD replay cost.
