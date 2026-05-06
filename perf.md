# MPC Performance Notes

## How To Measure

Performance measurements should name the artifact, command, cache mode, declaration count, environment size, and elapsed replay time.  Cold replay is the right measurement for checker changes because it exercises parsing, lowering, generated-record audit, and ordinary declaration checking from an empty MPC environment.  SQLite cache replay is the right measurement for self-check workflow costs, cache hit behavior, and adapter overhead, but it cannot be compared directly with cold replay.

Use `MPC_LEAN4EXPORT` when `lean4export` is not on `PATH`.  The generated artifacts used below live under `.lake/build/export-tests` or `.lake/build/mpc-export-self-check`, and profiling scratch files should live under `.tmp`.  Keep the exact command in the note for each measurement, because `--limit`, cache mode, telemetry mode, and the selected root change the meaning of the numbers.

| Task | Command |
| --- | --- |
| Build the checker | `lake build mpc-check-export` |
| Generate and check the GCD fixture | `env MPC_LEAN4EXPORT=/path/to/lean4export tools/mpc-export-gcd.sh` |
| Run the generated export regression set | `env MPC_LEAN4EXPORT=/path/to/lean4export tools/mpc-export-tests.sh` |
| Run the export self-check with cache | `env MPC_LEAN4EXPORT=/path/to/lean4export MPC_CACHE_DB=.tmp/mpc-self-check-cache.db tools/mpc-export-self-check.sh` |
| Run the export self-check cold | `env MPC_LEAN4EXPORT=/path/to/lean4export MPC_CACHE_DB= tools/mpc-export-self-check.sh` |
| Run the Omega stress profiler | `env MPC_LEAN4EXPORT=/path/to/lean4export MPC_STRESS_TIMEOUT=120 tools/mpc-omega-stress.sh` |

Use `--stats-jsonl` for per-declaration timing without structural counters.  Use `--profile-jsonl` when the question needs expression-size counters, head-application counters, or constant-kind counters beside timing.  Use `--profile-declaration <n>` when declaration `n` takes too long to finish and the prefix before it can still replay, because this mode replays the prefix and emits counters for the selected declaration without checking that declaration.

```bash
.lake/build/bin/mpc-check-export \
  --stats-jsonl \
  .lake/build/export-tests/mpc-gcd-parity-arithmetic.ndjson \
  > .tmp/mpc-gcd-stats.jsonl

.lake/build/bin/mpc-check-export \
  --profile-jsonl \
  --limit 430 \
  .lake/build/export-tests/mpc-gcd-parity-arithmetic.ndjson \
  > .tmp/mpc-gcd-profile-limit430.jsonl

.lake/build/bin/mpc-check-export \
  --profile-declaration 1174 \
  .lake/build/mpc-export-self-check/mpc-level.ndjson \
  > .tmp/mpc-level-decl-1174.profile.jsonl
```

`--cache-layer`, `--load-layer`, and `--save-layer` measure checked-layer behavior.  `--cache-layer` mutates a SQLite DB and rejects if an existing cached name has different declaration content, which can happen after source changes; use `MPC_CACHE_DB=` for a cold self-check when that distinction is not under test.  Cache modes do not support `--profile-jsonl`, and `--cache-layer` also rejects `--limit`, so cache measurements should use the text outcome or `--stats-jsonl` where supported.

SQLite cache files now use the v3 on-demand format.  A v3 cache stores declaration groups keyed by an anchor name and reads only the candidate groups needed for the declaration being replayed.  `mpc-check-export --cache-layer` also streams the NDJSON input in this mode, so large cached probes do not allocate the full input string, the split line list, or the full lowered declaration list before replay starts.

Older v2 cache files used rendered declarations as content keys and loaded the whole cached environment before replay.  Convert a v2 cache with `.lake/build/bin/mpc-migrate-layer <source-v2.db> <target-v3.db>`, or use a fresh cache path.  The checker refuses a v2 file passed to `--cache-layer`, because the v2 format can dominate memory and disk usage before any MPC rule runs.

When comparing runs, compare the same artifact and the same declaration prefix.  The most useful columns are declaration index, declaration name, status, elapsed milliseconds, cumulative milliseconds, expression node count, and transparent-definition head-application count.  A useful optimization note records both the winning and rejected hypotheses, because several cheap optimizations in this file measured inside run-to-run noise.

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
| 491 | 54,148 | `MPCFixtures.ExportArithmetic.gcd_right_two_of_odd` |
| 465 | 50,155 | `Nat.gcd_one_left` |
| 474 | 44,715 | `Nat.gcd_mul_left` |
| 492 | 33,412 | `MPCFixtures.ExportArithmetic.gcd_sum_diff_eq_one` |
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
| 334 | 12,191 | 5,950 | 873 | 0 | `MPCFixtures.ExportArithmetic.odd_of_opposite_parity` |
| 319 | 7,882 | 12,622 | 1,716 | 0 | `Nat.mod_add_div` |

The next instrumentation should be dynamic but still narrow: per-declaration counters for `defEq` calls, `whnf` calls, structural failures, eta attempts and successes, proof-irrelevance attempts and successes, delta unfolds, and recursor reductions.  Those counters should be emitted once per declaration, not as per-call logs.

## Mathlib Finset Range Filter

The first mathlib finite-set performance boundary came from `Finset.range_filter_eq` in `Mathlib.Data.Finset.Basic`.  The cold profile command reached declaration index 1429 in about 20.8 seconds, then spent the remaining run time on declaration 1430, `_private.Init.Data.List.Nat.Range.0.List.pairwise_lt_range'._proof_1_4`.  That proof comes from Lean's `Init.Data.List.Nat.Range`, where `pairwise_lt_range'` uses `omega` in the successor case.

```bash
.lake/build/bin/mpc-check-export \
  --profile-jsonl \
  .tmp/mathlib-probes/finset-range-filter-eq.ndjson \
  > .tmp/mathlib-probes/finset-range-filter-eq.profile.jsonl

.lake/build/bin/mpc-check-export \
  --profile-declaration 1430 \
  .tmp/mathlib-probes/finset-range-filter-eq.ndjson \
  > .tmp/mathlib-probes/finset-range-filter-eq.decl1430-profile.json
```

The selected declaration has 32,596 expression nodes, 16,094 application nodes, 5,457 transparent-definition constants, and 3,799 transparent-definition head applications.  Trying proof irrelevance before structure eta did not advance past the declaration and slightly increased the prefix time, so that change was reverted.  This leaves the issue classified as proof-conversion throughput over ordinary exported terms rather than a missing rule package.

The SQLite cache exposed an adapter problem during this probe.  Before the cache change, killed `--cache-layer` runs did not persist the accepted prefix because the adapter appended new rows only after complete replay.  The cache path now appends each checked declaration in its own SQLite transaction; in the `Finset.range_filter_eq` probe, killing the run after it reached the slow proof increased the cache from 803 to 1,922 environment rows, with `Nat.le_of_not_lt` as the last cached declaration before the slow proof.

## Mathlib BigOperators Finset

The first `BigOperators` finite-set probe used `Mathlib.Algebra.BigOperators.Group.Finset.Basic`, root `Finset.prod_biUnion`, with the shared SQLite mathlib cache.  Replay reused the accepted prefix through declaration index 2614 and then spent the useful probe budget on declaration 2615, `_private.Init.Grind.Ring.Basic.0.Lean.Grind.Ring.intCast_nat_sub._proof_1_2`.  This declaration comes from Lean's `Init.Grind.Ring.Basic`, theorem `intCast_nat_sub`, whose successor case uses `omega`.

```bash
.lake/build/bin/mpc-check-export \
  --cache-layer .tmp/mathlib-probes/mathlib-cache.db \
  --stats-jsonl \
  .tmp/mathlib-probes/bigops-finset-prod-biUnion.ndjson \
  > .tmp/mathlib-probes/bigops-finset-prod-biUnion.spine-stats.jsonl

.lake/build/bin/mpc-check-export \
  --profile-declaration 2615 \
  .tmp/mathlib-probes/bigops-finset-prod-biUnion.ndjson
```

The selected declaration has 196,906 expression nodes, 98,428 application nodes, 35,330 transparent-definition constants, and 25,701 transparent-definition head applications.  It has no primitive Nat head applications, no recursor head applications, no quotient-lift head applications, and no projection nodes.  A head-frequency scan reports the largest applied heads as `List.cons`, `Nat.cast`, `OfNat.ofNat`, `HSub.hSub`, `HAdd.hAdd`, `Lean.Omega.LinearCombo.mk`, `Lean.Omega.Coeffs.ofList`, and `Lean.Omega.LinearCombo.eval`.

Two cheap traversal changes were tested and not kept.  Comparing application spines directly inside structural conversion did not advance past declaration 2615, and adding an exact-structural `BEq` fast path before alpha equivalence also did not advance past the declaration.  The result keeps the classification as proof-checking throughput over a large generated arithmetic certificate.

## Mathlib Nat Prime Factors

The `Nat.primeFactorsList_unique` probe used `Mathlib.Data.Nat.Factors` with the shared mathlib SQLite cache.  The artifact is 14 MB, and the cached stats run reused every declaration before the hard point.  The reused prefix reached declaration index 2717 in 6,045 ms, then the 300-second command timed out while checking declaration index 2718.

```bash
timeout 300s .lake/build/bin/mpc-check-export \
  --stats-jsonl \
  --cache-layer .tmp/mathlib-probes/mathlib-cache.db \
  .tmp/mathlib-probes/nat-primeFactorsList-unique.ndjson \
  > .tmp/mathlib-probes/nat-primeFactorsList-unique.stats.jsonl \
  2> .tmp/mathlib-probes/nat-primeFactorsList-unique.stats.err
```

The hard declaration is `_private.Mathlib.Data.Nat.Sqrt.0.Nat.sqrt_isSqrt`, not `Nat.primeFactorsList_unique`.  The theorem has 9 type nodes and 47,233 value nodes.  A head-count scan is dominated by `OfNat.ofNat`, `HAdd.hAdd`, `HDiv.hDiv`, `Nat.log2`, `HShiftLeft.hShiftLeft`, `HMul.hMul`, and `Nat.sqrt`, which points to numeric proof conversion through ordinary definitions and overloaded arithmetic projections rather than a rule-package conclusion.

## Mathlib Measure Rat Proof

The measure-theory probe used `Mathlib.MeasureTheory.Constructions.BorelSpace.Metric`, root `Measurable.dist`, with the shared mathlib SQLite cache.  The exported artifact has 834,810 NDJSON rows and a 43 MB file size.  The first cached stats run failed before reaching the hard declaration because requested-content lookup built one SQLite temporary table containing every target declaration key, which exhausted SQLite temporary storage.

```bash
timeout 300s .lake/build/bin/mpc-check-export \
  --stats-jsonl \
  --cache-layer .tmp/mathlib-probes/mathlib-cache.db \
  .tmp/mathlib-probes/measure-metric-dist.ndjson \
  > .tmp/mathlib-probes/measure-metric-dist.stats.jsonl \
  2> .tmp/mathlib-probes/measure-metric-dist.stats.err

env MPC_MATHLIB_DIR=/tmp/mathlib4-v4290-probe \
  MPC_LEAN4EXPORT=/tmp/lean4export/.lake/build/bin/lean4export \
  MPC_PROBE_LABEL=rat-addcommgroup-proof1 \
  MPC_CACHE_DB=.tmp/mathlib-probes/mathlib-cache.db \
  MPC_PROBE_STATS=1 \
  tools/mpc-mathlib-probe.sh Mathlib.Data.Rat.Lemmas Rat.addCommGroup._proof_1
```

After the cache lookup changed to bounded direct key queries, the `Measurable.dist` stats run reached declaration index 3277, `Rat.addCommGroup._proof_1`, before the time budget expired.  The isolated rational root reproduces the same wall at index 1826 after replaying the prefix through `Rat.one_mul`.  A static declaration scan reports 95 type nodes and 2,575 value nodes for the theorem, so the cost is not explained by raw term size alone.

Two diagnostics failed to move the boundary.  Disabling the equality-rec endpoint fallback did not advance the isolated proof, so the prior equality-rec fix is not the cause of this wall.  Direct reduction of projection constants also did not advance the isolated proof, though that reducer is still a projection-package correction for exported structure accessors.  The remaining question needs dynamic counters for `defEq`, `whnf`, equality transport, proof irrelevance, and transparent unfolding if this rational proof becomes the next performance target.

The same rational proof wall appears in `Real.continuous_sqrt` from `Mathlib.Data.Real.Sqrt`.  The cached stats run reached `Rat.addCommGroup._proof_1` at declaration index 3290 after reusing the prefix through `Rat.one_mul` in 4,673 ms, then timed out.  This makes `Rat.addCommGroup._proof_1` a reusable blocker for analysis roots, not an artifact of the measure-theory export.

## Mathlib LinearEquiv NoConfusion

The `LinearMap.det_comp` probe used `Mathlib.LinearAlgebra.Determinant` with the shared mathlib SQLite cache.  The exported artifact is 62 MB, and the cached stats run reused the prefix through declaration index 7357 in 13,926 ms.  The 300-second command then timed out while checking declaration index 7358, before reaching `LinearMap.det_comp`.

```bash
timeout 300s .lake/build/bin/mpc-check-export \
  --stats-jsonl \
  --cache-layer .tmp/mathlib-probes/mathlib-cache.db \
  .tmp/mathlib-probes/linearMap-det-comp.ndjson \
  > .tmp/mathlib-probes/linearMap-det-comp.stats.jsonl \
  2> .tmp/mathlib-probes/linearMap-det-comp.stats.err
```

The hard declaration is `LinearEquiv.noConfusion`, a generated definition with 699 type nodes and 8,297 value nodes.  A head-count scan is dominated by `Semiring.toNonAssocSemiring`, `HEq`, `LinearEquiv`, `RingHomInvPair`, `RingHom`, `Module`, `Eq.ndrec`, and `eq_of_heq`.  This differs from the ordinary proof-term walls because the hard object is derived structure support; a shortcut would be a derived declaration checker or audit layer, not an MPC conversion rule.

## Mathlib Abelian Resource Boundary

The `CategoryTheory.Abelian.image_ι_comp_eq_zero` probe used `Mathlib.CategoryTheory.Abelian.Basic` with the shared mathlib SQLite cache.  The corrected root built successfully and exported `.tmp/mathlib-probes/category-abelian-image-zero.ndjson`, a 27 MB artifact, but the old v2-cache path was killed with exit code 137 before it wrote checker output or declaration stats.  The old cache file was 2.8 GB, and inspecting it showed 12,566 content rows whose rendered declaration keys occupied 2,620,504,409 bytes, with a largest key of 156,683,766 bytes.

Migrating that cache to v3 moved the cache to declaration groups rather than rendered declaration keys.  The current v3 file after subsequent probes is 518 MB, with 13,152 declaration groups, 14,154 cached constant entries, 527,923,069 bytes of cached JSON, and a largest entry JSON value of 34,465,377 bytes.  The remaining input-side memory problem was then the CLI path that read the whole export file and lowered every declaration before cache replay started.

After `--cache-layer` moved to streaming NDJSON replay, the same abelian artifact accepted through the migrated v3 cache:

```bash
timeout 300s .lake/build/bin/mpc-check-export \
  --cache-layer .tmp/mathlib-probes/mathlib-cache-v3.db \
  --stats-jsonl \
  .tmp/mathlib-probes/category-abelian-image-zero.ndjson \
  > .tmp/mathlib-probes/category-abelian-image-zero-v3-stream.stats.jsonl \
  2> .tmp/mathlib-probes/category-abelian-image-zero-v3-stream.stats.err
```

The run reused 5,174 declaration entries, checked none, produced environment size 5,753, and emitted no stderr.  The final declaration row was `CategoryTheory.Abelian.image_ι_comp_eq_zero`, and the measured replay cumulative time in the JSONL stream was 194,059 ms.  This classifies the old abelian failure as an adapter memory problem in the cached path, not a checker rule gap.

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

`MPCFixtures.ExportOmega` adds small `omega`-produced proofs, and `tools/mpc-omega-stress.sh` exports `MPCFixtures.ExportOmega.nat_linear_bounds` before running `mpc-check-export --profile-jsonl`.  The script writes the artifact to `.lake/build/export-tests/mpc-omega-nat-linear-bounds.ndjson` and the profile to `.tmp/mpc-omega-nat-linear-bounds.profile.jsonl`.  It treats accepted, rejected, unsupported, and timed-out checker runs as reportable stress outcomes, because the fixture is for locating the next boundary rather than defining an acceptance test.

The first run did not reach `Lean.Omega` certificate declarations.  It checked through declaration index 1141, took 113,359 ms of measured replay time, and then rejected definition `String.instInhabited` at index 1142 because raw string literals were disabled in the MPC configuration.  LeanCore429 now enables neutral string literals: a raw string literal has type `String`, requires `String` in the environment, and does not reduce to Lean's list or byte-array representation.

With neutral string literals enabled, a traced prefix through declaration index 972 accepts and reaches `Lean.Omega.normalize_sat`.  A longer full stress run rejects at declaration index 1165, the inductive `Lean.Syntax`, because the field `args` is not accepted by the current strict-positivity rule.  The next rule-package question is therefore nested positive occurrences through specified container types in Lean's syntax representation, not an Omega-specific primitive rule.

After adding specified-container positivity for `Array` and `List`, the same stress run checks through the exported theorem.  Declaration index 1243, `MPCFixtures.ExportOmega.nat_linear_bounds._proof_1_1`, dominates the run at 123,902 ms, with 19,758 expression nodes and 2,512 transparent-definition head applications.  The checker then rejects during generated-recorder audit because the artifact expects `Lean.Syntax.rec_2`, which the current nested-inductive recursor generation does not produce.

After adding generated nested recursor families for the specified unary containers, the Omega stress artifact accepts.  The accepted run checked 1245 declarations with environment size 1409, and the total measured replay time was 267,810 ms before nested recursor iota reduction and 248,858 ms after it.  Declaration index 1243 still dominates the profile: `MPCFixtures.ExportOmega.nat_linear_bounds._proof_1_1` took 146,463 ms in the first accepted run and 129,394 ms after the iota rule, with the same 19,758 expression nodes and 2,512 transparent-definition head applications.  The nested-recursor counters are zero on that proof row, so the remaining performance issue remains broad conversion through ordinary proof terms rather than generated recursor audit, helper-target generation, or nested-recursive reduction.

## MPC.Level Self-Check

After projection-universe instantiation, `MPC.Level` no longer rejects at `MPC.Level.reduceIMax._proof_1`.  A prefix replay through declaration 1174 then reached `Lean.Omega.IntList.dot_mod_gcd_left`, which dominated the run.  The original bounded prefix-1175 run accepted, but declaration 1174 alone took 81,846 ms out of 98,947 ms cumulative replay time.

`mpc-check-export --profile-declaration <n>` replays the preceding declarations and emits structural counters for one selected declaration without checking that declaration.  This mode exists because `--profile-jsonl` emits only after a declaration finishes, which made the current wall hard to inspect.  The profile for declaration 1174 has 6,366 nodes, 830 transparent-definition head applications, no primitive Nat head applications, no projection nodes, and no nested recursor head applications, so the cost points to ordinary conversion through transparent proof definitions rather than a missing primitive or generated-reduction rule.

The first successful optimization indexes the environment by name.  The diagnostic chronological-list experiment showed that lookup order was a major cost by making old constants cheap and recent constants expensive.  The committed representation keeps a declaration list for size and diagnostics, while `Env.find?` reads from a `HashMap`, so lookup cost no longer depends on declaration age.

| Run | Prefix setup ms | Declaration 1174 ms | Prefix total ms |
|---|---:|---:|---:|
| Latest-first list baseline | 17,101 | 81,846 | 98,947 |
| Left-type-first proof irrelevance | 16,585 | 81,638 | 98,223 |
| Chronological-list diagnostic | 3,307 | 21,342 | 24,649 |
| Indexed environment | 1,632 | 15,637 | 17,269 |

The indexed-environment run checks the full `MPC.Level` artifact in 34,288 ms: 1,396 declaration entries and environment size 1,594.  The remaining time is still concentrated in proof-heavy declarations, but the old single-declaration wall no longer blocks full replay.  The next performance question is repeated conversion and instantiation inside those proof terms, not environment search.

| Index | Elapsed ms | Declaration |
|---:|---:|---|
| 1174 | 15,566 | `Lean.Omega.IntList.dot_mod_gcd_left` |
| 1234 | 3,149 | `Lean.Omega.tidy_sat` |
| 1274 | 2,559 | `MPC.Level.reduceIMax._proof_5` |
| 1272 | 2,364 | `MPC.Level.reduceIMax._proof_3` |
| 1302 | 2,361 | `MPC.Level.normalizeSummands?._proof_3` |

## MPC.Env Self-Check

After constructor-form structure eta, `MPC.Env` accepts as a whole-artifact export replay.  The first `--profile-jsonl` run checked 2,213 declaration entries in 633,067 ms, with 99.3 percent of measured time in theorem declarations.  Five private library proof declarations account for 576,472 ms, or 91.1 percent of the run, so the remaining performance problem is still proof conversion through imported dependencies rather than checking the MPC environment declarations themselves.

| Index | Elapsed ms | Nodes | Def-head apps | Declaration |
|---:|---:|---:|---:|---|
| 1733 | 211,801 | 45,804 | 6,389 | `_private.Init.Data.Nat.Bitwise.Lemmas.0.Nat.le_of_testBit._proof_1_2` |
| 1661 | 115,653 | 133,482 | 19,284 | `_private.Init.Data.BitVec.Lemmas.0.BitVec.toNat_sub_of_le._proof_1_2` |
| 1845 | 106,489 | 127,996 | 14,583 | `_private.Std.Data.DHashMap.Internal.Defs.0.Std.DHashMap.Internal.Raw₀.expand.go._unary._proof_1` |
| 1732 | 75,515 | 37,282 | 5,213 | `_private.Init.Data.Nat.Bitwise.Lemmas.0.Nat.le_of_testBit._proof_1_1` |
| 1665 | 67,014 | 84,482 | 12,200 | `_private.Init.Data.BitVec.Lemmas.0.BitVec.toNat_sub_of_le._proof_1_3` |

Empty level-substitution fast paths now return the original level or expression without traversing it.  This is a local semantic-preserving optimization: substituting no universe parameters cannot change the term.  On the same `MPC.Env` profile, it reduced measured replay time from 633,067 ms to 620,929 ms, a 12,138 ms improvement; a broader syntactic-identity substitution check measured worse than the empty-only version and was not kept.

| Run | Measured ms | Change |
|---|---:|---:|
| Constructor eta baseline | 633,067 | 0 |
| Empty level-substitution fast path | 620,929 | -12,138 |
| Empty plus identity substitution experiment | 628,556 | -4,511 |

## Checked Layers

The first persistent checked layer stores the checked environment and lowered declaration-content table outside the checker.  Saving the `MPC.Env` layer still pays the cold replay cost, but loading the saved layer avoids rechecking the shared dependency closure for a target artifact.  The file is large because it stores full checked environment entries as JSON: `.tmp/mpc-env.layer.json` measured 417,651,533 bytes.

| Run | Reused declarations | Checked declarations | Measured time |
|---|---:|---:|---:|
| Save `MPC.Env` layer | 0 | 2,213 | cold replay cost |
| Load `MPC.Env` layer for `MPC.Packages.Literal` | 2,062 | 4 | 7,914 ms |
