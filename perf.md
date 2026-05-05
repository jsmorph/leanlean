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

## Nat Right-Zero Reductions

The primitive Nat reducer now includes the cheap right-zero cases from the source equations for `Nat.mul`, `Nat.pow`, and `Nat.sub`.  The added rules are `Nat.mul n 0 = 0`, `Nat.pow n 0 = 1`, and `Nat.sub n 0 = n`, with the zero argument recognized after weak-head normalization.  These rules are part of the admitted Nat primitive table, so `spec.md` and the native primitive Nat tests were updated with the implementation.

| Run | Prefix | Measured ms | Baseline ms | Change |
|---|---:|---:|---:|---:|
| Nat right-zero reductions | 475 | 363,973 | 364,037 | -64 |

The measurement is also within run-to-run noise.  The late GCD declarations remain the dominant cost: `Nat.gcd_one_left`, `Nat.gcd_mul_left`, `Nat.gcd_dvd`, `Nat.gcd_assoc`, `Nat.gcd_rec`, and `Nat.mul_mod_mul_left` keep essentially the same times.  The next useful work is instrumentation below declaration level, especially counts for conversion fallback, proof irrelevance, eta, weak-head reduction, delta unfolding, recursor reduction, and primitive Nat reduction.

## Profile JSONL

`mpc-check-export --profile-jsonl` extends the timing row with structural counters computed before declaration replay.  The counters are static and cheap: expression nodes, app nodes, full application spines, maximum spine arity, binder nodes, let nodes, projection nodes, constant references by environment kind, and head applications whose head is a transparent definition, recursor, equality recursor, quotient lift, or admitted primitive Nat constant.  This keeps the kernel pure and avoids threading a profiling monad through `defEq` and `whnf`.

The first profile run used prefix 430, which includes `Nat.gcd_dvd` but stops before the heaviest late declarations.  It measured 159,084 ms, close to the previous 159,998 ms baseline for the same prefix.  The static counters do not explain all timing variation, but they point away from the blind Nat-primitive hypothesis: the slow rows in this prefix have zero primitive Nat head applications.  They do have many transparent-definition head applications, which is consistent with expensive repeated conversion through ordinary proof terms and unfolding.

| Index | Elapsed ms | Nodes | Def-head apps | Rec-head apps | Declaration |
|---:|---:|---:|---:|---:|---|
| 427 | 30,059 | 1,396 | 178 | 0 | `Nat.gcd_dvd` |
| 397 | 23,277 | 2,087 | 335 | 0 | `Nat.gcd_rec` |
| 388 | 17,420 | 5,440 | 406 | 8 | `_private.Init.Data.Nat.Gcd.0.Nat.gcd._unary.eq_def` |
| 395 | 14,428 | 512 | 60 | 0 | `Nat.gcd_succ` |
| 334 | 12,191 | 5,950 | 873 | 0 | `LeanLeanFaithfulness.ExportArithmetic.odd_of_opposite_parity` |
| 319 | 7,882 | 12,622 | 1,716 | 0 | `Nat.mod_add_div` |

The next instrumentation should be dynamic but still narrow: per-declaration counters for `defEq` calls, `whnf` calls, structural failures, eta attempts and successes, proof-irrelevance attempts and successes, delta unfolds, and recursor reductions.  Those counters should be emitted once per declaration, not as per-call logs.

## Conversion Fast Paths

The useful optimization was a top-level alpha-equivalence check at the start of `defEq`.  If two terms are already equal up to binder names and universe equality, conversion now returns before weak-head reduction, structural recursion, eta, or proof irrelevance.  This preserves the conversion relation and removes repeated normalization of subterms that are already identical in exported proof terms.

Two smaller proof-irrelevance changes stayed in the same patch.  Conversion now tries proof irrelevance before function eta after structural conversion fails, and the proof-irrelevance check verifies that the left inferred type is a proposition before comparing the left and right inferred types.  If those types are definitionally equal, the right type has the same proposition sort, so a separate sort check on the right type is redundant.

| Run | Declarations | Measured ms | Baseline ms |
|---|---:|---:|---:|
| Original full GCD profile | 493 | 597,416 | 597,416 |
| Top-level alpha fast path | 493 | 12,646 | 597,416 |
| Alpha fast path plus proof-irrelevance cleanup | 493 | 12,573 | 597,416 |

The remaining hotspot is `Nat.gcd_one_left`, which now takes about 10 seconds and accounts for most of the remaining GCD replay time.  Most previously slow late declarations become cheap after the alpha fast path: `Nat.Coprime.gcd_mul_left_cancel` drops from 116,057 ms to a few milliseconds, and the final project theorem drops from 33,412 ms to single-digit milliseconds in the measured run.

Two candidates were tested and not kept.  Removing eager `repr` construction from structural mismatch errors did not show a reliable improvement and weakened rejection diagnostics.  A second alpha-equivalence check after weak-head reduction also failed to improve the profile, because the extra traversal did not pay for itself on this artifact.

## Omega Stress Fixture

`Faithfulness.ExportOmega` adds small `omega`-produced proofs, and `tools/mpc-omega-stress.sh` exports `LeanLeanFaithfulness.ExportOmega.nat_linear_bounds` before running `mpc-check-export --profile-jsonl`.  The script writes the artifact to `.lake/build/export-tests/mpc-omega-nat-linear-bounds.ndjson` and the profile to `.tmp/mpc-omega-nat-linear-bounds.profile.jsonl`.  It treats accepted, rejected, unsupported, and timed-out checker runs as reportable stress outcomes, because the fixture is for locating the next boundary rather than defining an acceptance test.

The first run did not reach `Lean.Omega` certificate declarations.  It checked through declaration index 1141, took 113,359 ms of measured replay time, and then rejected definition `String.instInhabited` at index 1142 because raw string literals were disabled in the MPC configuration.  LeanCore429 now enables neutral string literals: a raw string literal has type `String`, requires `String` in the environment, and does not reduce to Lean's list or byte-array representation.

With neutral string literals enabled, a traced prefix through declaration index 972 accepts and reaches `Lean.Omega.normalize_sat`.  A longer full stress run rejects at declaration index 1165, the inductive `Lean.Syntax`, because the field `args` is not accepted by the current strict-positivity rule.  The next rule-package question is therefore nested positive occurrences through specified container types in Lean's syntax representation, not an Omega-specific primitive rule.
