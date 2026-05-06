# Mathlib Probe Plan

## Purpose

Mathlib gives MPC a gap-finding corpus without becoming a dependency of the MPC repository.  The near-term goal is to export selected mathlib roots, run them through the existing `mpc-check-export` path, and classify the first real checker boundary exposed by each artifact.  A probe succeeds when it tells us whether the next problem is a missing rule package, a rule-package side condition, proof-term performance, generated-declaration audit behavior, or artifact translation.

This plan targets selected roots rather than bulk mathlib checking.  Bulk checking would mix dependency management, artifact size, proof-term performance, and checker soundness into one result that would be hard to interpret.  Targeted probes give better engineering evidence because each selected root has a reason, an expected stress area, and a recorded outcome.

## Boundary

The MPC repository keeps mathlib outside its Lake dependencies for this work.  A probe uses an existing external mathlib checkout built with the Lean version compatible with this repository and the installed `lean4export` binary.  The MPC side remains the checker executable, optional cache DB, profile output, and a small driver script if repeated manual commands become error-prone.

Generated artifacts and profiling output stay out of git.  Use `.tmp/mathlib-probes` or a caller-provided directory for NDJSON, root files, timing JSONL, and cache DBs.  The persistent cache remains an adapter-side optimization: useful for repeated probes, but not part of the checker claim.

## Method

Each probe starts from one module and one or more explicit roots.  The driver builds the target module in the mathlib checkout, runs `lean4export` against that module and root list, then runs the produced NDJSON through `.lake/build/bin/mpc-check-export`.  The driver records the module, roots, mathlib revision, Lean version, export command, checker command, cache mode, declaration count, environment size, elapsed time, and final status.

The first probe uses a scratch module in the mathlib checkout rather than a theorem chosen from the whole library.  That scratch module can import a small mathlib module and define one theorem whose proof shape we control.  This keeps the first artifact tied to mathlib's dependency closure while avoiding uncertainty about public theorem names.

After the scratch probe, use real mathlib roots in a ladder.  Start with early declarations that stress ordinary data, structures, projections, and simple theorem proofs.  Then add roots that stress quotients, finite types, indexed families, tactic-produced arithmetic proofs, and algebraic structures.  The ladder stops at the first unexplained failure long enough to classify it before adding more targets.

## Target Ladder

| Tier | Target shape | Stress area |
| --- | --- | --- |
| 0 | Scratch theorem over `Nat`, `List`, or `Subtype` after importing a small mathlib module. | Tooling, closure size, ordinary definitions, theorem proofs, and basic projection behavior. |
| 1 | Small real theorem over `Nat`, `List`, `Fin`, or `Option`. | Proof irrelevance, recursive definitions, equation-compiler output, and primitive Nat reductions. |
| 2 | Small theorem involving structures, subtypes, or sets. | Projection typing, structure eta, Prop projection restrictions, and large elimination boundaries. |
| 3 | Small theorem involving quotients, finite sets, or equivalence relations. | Low-level quotient primitives, equality transport, and proof-heavy conversion. |
| 4 | Tactic-produced arithmetic theorem using `omega`, `linarith`, `ring`, or heavy `simp`. | Generated proof terms, conversion performance, primitive arithmetic gaps, and resource classification. |

The names in this table are shapes, not commitments to particular mathlib declarations.  Exact module and root names come from the local mathlib checkout before each run.  A selected root needs a short note explaining why it belongs in the ladder and what result would count as informative.

## Result Classes

| Result | Meaning |
| --- | --- |
| Accepted | MPC checked the exported artifact under `LeanCore429`, including generated-record audits. |
| Rejected: rule gap | Replay reached a canonical declaration whose typing, conversion, reduction, or admission needs a rule package MPC lacks. |
| Rejected: side-condition gap | MPC has the relevant package, but the implemented rule is too narrow or too strict for the exported declaration. |
| Rejected: performance | The checker does not reach a semantic rejection in a useful time budget, or it hits a host resource limit. |
| Unsupported artifact | Export parsing or lowering fails before MPC receives a canonical declaration script. |
| Audit mismatch | MPC checks the declaration script, but a redundant generated record disagrees with generated MPC metadata. |

Diagnostic continuation does not establish acceptance.  If a run needs temporary assumptions, skipped declarations, or disabled audits to classify the next boundary, record that mode as diagnostic.  The ordinary acceptance claim remains the unmodified `mpc-check-export` result for the produced artifact.

## First Work Items

1. Add a small external-driver script only after one manual probe works.  The script takes `MPC_MATHLIB_DIR`, `MPC_LEAN4EXPORT`, a module name, and a root list.  It writes all generated data under `.tmp/mathlib-probes` by default.

2. Run one scratch probe with a small import and a controlled theorem.  Record the exact module, root, artifact size, declaration count, status, and first failure if it rejects.  If the closure is already too large to classify, reduce the import before changing MPC.

3. Run two or three real-root probes from the lower tiers.  Prefer roots whose theorem statements and proofs can be inspected quickly in the mathlib checkout.  Stop when a failure identifies a serious rule-package question.

4. For the first slow declaration, use `--stats-jsonl`, `--profile-jsonl`, and `--profile-declaration` as appropriate.  The goal is classification, not broad optimization.  Performance work should enter `perf.md` only after a repeated run identifies a stable cost.

## Non-Goals

Do not add mathlib to this repository's `lakefile.toml`.  Do not add new primitive reductions because a mathlib proof is slow or rejected unless the rule has Lean-version source evidence, a written specification, declaration-shape checks, and focused tests.  Do not convert generated or tactic-produced declarations into assumptions to claim acceptance.

Do not chase many mathlib failures at once.  One classified failure is more useful than a long list of unclassified rejects.  The probe series should keep returning to the MPC rule-package boundary: what rule did the checker need, where should that rule live, and what test demonstrates the rule without importing mathlib into the trusted development path.

## First Probe

The first probe used a temporary external checkout at mathlib tag `v4.29.0`, with only its `lean-toolchain` changed to `leanprover/lean4:v4.29.1` so the produced artifact matched the local `lean4export` binary and MPC's Lean 4.29.1 source baseline.  Mathlib `HEAD` targeted Lean 4.30.0-rc2 when this probe ran, so the pinned release tag avoided using a newer Lean artifact format or kernel implementation.  `lake build Mathlib.Data.Nat.Basic` succeeded under Lean 4.29.1 after the pinned package directories from `lake-manifest.json` were populated.

The scratch module `Mathlib.MPCProbe.Scratch` imported `Mathlib.Data.Nat.Basic` and defined `MPCProbe.MathlibScratch.addZeroProbe`, a theorem whose body is `Nat.add_zero n`.  Exporting that root with `/tmp/lean4export/.lake/build/bin/lean4export` produced `.tmp/mathlib-probes/scratch-add-zero.ndjson`, with 639 NDJSON rows and a 36 KB artifact.  Cold MPC replay with `mpc-check-export --stats-jsonl` accepted the artifact: 23 declaration entries checked, producing environment size 39.

This is an accepted Tier 0 result.  It verifies the external checkout, module build, export command, checker invocation, and scratch-root workflow.  It does not yet test a broad mathlib dependency closure, generated helper classes, quotient-heavy proofs, tactic-produced arithmetic, or performance limits.

## Current Probe Results

| Label | Module | Root | Result | Notes |
| --- | --- | --- | --- | --- |
| Scratch add-zero | `Mathlib.MPCProbe.Scratch` | `MPCProbe.MathlibScratch.addZeroProbe` | Accepted | 639 NDJSON rows, 36 KB artifact, 23 checked declarations, environment size 39. |
| Nat successor injective | `Mathlib.Data.Nat.Basic` | `Nat.succ_injective` | Accepted | 9 checked declarations, environment size 15. |
| Nat nontrivial instance | `Mathlib.Data.Nat.Basic` | `Nat.instNontrivial` | Accepted | 15 checked declarations, environment size 28. |
| Nat linear-order instance | `Mathlib.Data.Nat.Basic` | `Nat.instLinearOrder` | Accepted | 332 checked declarations, environment size 457. |
| Nat set induction | `Mathlib.Data.Nat.Basic` | `Nat.set_induction` | Accepted | 140 checked declarations, environment size 184. |
| Quot congruence on constructors | `Mathlib.Logic.Equiv.Defs` | `Quot.congr_mk` | Accepted | 338 checked declarations, environment size 459.  The first run exposed a WHNF spine-reprocessing bug: delta reduction of `Quot.congr` and `Quot.map` exposed a partially applied `Quot.lift`, while the quotient argument remained outside the unfolded head. |
| SetLike extensionality | `Mathlib.Data.SetLike.Basic` | `SetLike.ext` | Accepted | 23 checked declarations, environment size 36.  This is the first structure/set probe after the quotient fix. |
| Quotient binary lift | `Mathlib.Data.Quot` | `Quotient.lift₂_mk` | Accepted | 20 checked declarations, environment size 33. |
| Quotient representative equation | `Mathlib.Data.Quot` | `Quotient.out_eq` | Accepted | 26 checked declarations, environment size 43. |
| Fin constructor equality | `Mathlib.Data.Fin.Basic` | `Fin.mk_eq_mk` | Accepted | 22 checked declarations, environment size 39. |
| Fin small arithmetic proof | `Mathlib.Data.Fin.Basic` | `Fin.eq_one_of_ne_zero` | Accepted | 1,623 checked declarations, environment size 1,859.  This root uses a `lia` proof and pulls in the Omega proof stack. |
| Finset singleton erase | `Mathlib.Data.Finset.Basic` | `Finset.erase_singleton` | Accepted | 887 checked declarations, environment size 1,071. |
| Finset range union | `Mathlib.Data.Finset.Basic` | `Finset.range_union_range` | Accepted | 1,792 checked declarations, environment size 2,042.  This accepted run took long enough to serve as a finite-set performance signal. |
| Finset singleton filter | `Mathlib.Data.Finset.Basic` | `Finset.filter_singleton` | Accepted | SQLite-cache run checked 593 target declarations into a new mathlib probe cache. |
| Finset filter union | `Mathlib.Data.Finset.Basic` | `Finset.filter_union` | Accepted | SQLite-cache run reused 555 declarations and checked 90 new declarations on the first pass; after the cache grew, it reused all 645 target declarations. |
| Finset range filter | `Mathlib.Data.Finset.Basic` | `Finset.range_filter_eq` | Rejected: performance | Replay reached declaration index 1430, `_private.Init.Data.List.Nat.Range.0.List.pairwise_lt_range'._proof_1_4`, then exceeded the useful probe budget.  The selected declaration has 32,596 expression nodes, 16,094 app nodes, 5,457 transparent-definition constants, and 3,799 transparent-definition head applications. |

The quotient probe reached MPC replay, checked the declaration prefix, and then exposed a WHNF bug in conversion.  Inspecting the exported `Quot.congr_mk` term showed that Lean's ordinary `rfl` proof depends on `Quot.congr` and `Quot.map` reducing through a partial `Quot.lift`.  The fixed run accepts the root, so the next probe can move past the low-level quotient constructor case.

The first serious mathlib performance boundary is an Omega-generated proof imported by a finite-set range theorem.  This is a checker-throughput problem over ordinary proof terms, not a new rule-package requirement.  The SQLite checked-layer cache now persists each checked declaration as it succeeds, so interrupted long probes keep the accepted prefix they have already checked.
