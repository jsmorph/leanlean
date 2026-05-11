# Mathlib Probe Plan

## Purpose

Mathlib gives MPC a gap-finding corpus without becoming a dependency of the MPC repository.  The near-term goal is to export selected mathlib roots, run them through the existing `mpc-check-export` path, and classify the first real checker boundary exposed by each artifact.  A probe succeeds when it tells us whether the next problem is a missing rule package, a rule-package side condition, proof-term performance, generated-declaration audit behavior, or artifact translation.

This plan targets selected roots rather than bulk mathlib checking.  Bulk checking would mix dependency management, artifact size, proof-term performance, and checker soundness into one result that would be hard to interpret.  Targeted probes give better engineering evidence because each selected root has a reason, an expected stress area, and a recorded outcome.

## Boundary

The MPC repository keeps mathlib outside its Lake dependencies for this work.  A probe uses an existing external mathlib checkout built with the Lean version compatible with this repository and the installed `lean4export` binary.  The MPC side remains the checker executable, optional cache DB, profile output, and a small driver script if repeated manual commands become error-prone.

Generated artifacts and profiling output stay out of git.  Use `.tmp/mathlib-probes` or a caller-provided directory for NDJSON, root files, timing JSONL, and cache DBs.  The persistent cache remains an adapter-side optimization: useful for repeated probes, but not part of the checker claim.  Current probes should use a fresh v4 cache DB or a v2 cache migrated with `mpc-migrate-layer`; v3 cache files belong to the earlier anchor-cache format and mutable cache mode refuses them.

## Method

Each probe starts from one module and one or more explicit roots.  The driver builds the target module in the mathlib checkout, runs `lean4export` against that module and root list, then runs the produced NDJSON through `.lake/build/bin/mpc-check-export`.  The driver records the module, roots, mathlib revision, Lean version, export command, checker command, cache mode, declaration count, environment size, elapsed time, and final status.

The driver treats an export with no declaration rows as a root-selection or exporter failure.  `lean4export` can print a panic for an unknown root while still leaving a valid metadata-only NDJSON file, so the probe harness rejects that case before invoking MPC.  A zero-declaration checker result never counts as acceptance for an explicit mathlib root.

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
| Finset range filter | `Mathlib.Data.Finset.Basic` | `Finset.range_filter_eq` | Accepted | V4 cache replay reused 2,453 declaration entries, checked 201 new entries, accepted 2,654 target declarations, and produced environment size 2,975.  The old range proof boundary checked in 367 ms, and the target theorem checked in 4 ms. |
| Finset unique choice | `Mathlib.Data.Finset.Basic` | `Finset.choose_spec` | Accepted | SQLite-cache run reused 372 declarations and checked 34 new declarations. |
| Finset-to-set equivalence | `Mathlib.Data.Finset.Basic` | `Finset.equivToSet` | Accepted | SQLite-cache run reused 544 declarations and checked 13 new declarations. |
| Group left commutation | `Mathlib.Algebra.Group.Basic` | `mul_left_comm` | Accepted | SQLite-cache run reused 12 declarations and checked 13 new declarations. |
| Group inverse cancellation | `Mathlib.Algebra.Group.Basic` | `inv_mul_eq_of_eq_mul` | Accepted | SQLite-cache run reused 299 declarations and checked 67 new declarations. |
| Ring quadratic identity | `Mathlib.Algebra.Ring.Basic` | `vieta_formula_quadratic` | Accepted | SQLite-cache run reused 306 declarations and checked 169 new declarations. |
| Ring no-zero-divisors TFAE | `Mathlib.Algebra.Ring.Basic` | `noZeroDivisors_tfae` | Accepted | SQLite-cache run reused 530 declarations and checked 92 new declarations. |
| Prime factorization uniqueness | `Mathlib.Data.Nat.Factors` | `Nat.primeFactorsList_unique` | Accepted | After the measure run populated the `Nat.sqrt` dependency region, v4 cache replay reused 2,889 declaration entries, checked 414 new entries, accepted 3,303 target declarations, and produced environment size 3,730.  The target theorem checked in 15 ms. |
| List product range division | `Mathlib.Algebra.BigOperators.Group.List.Basic` | `List.prod_range_div` | Accepted | SQLite-cache run reused 430 declarations and checked 52 new declarations. |
| Finset product over `biUnion` | `Mathlib.Algebra.BigOperators.Group.Finset.Basic` | `Finset.prod_biUnion` | Accepted | After broader Grind dependencies were cached, v4 cache replay reused 3,386 declaration entries, checked 40 new entries, accepted 3,426 target declarations, and produced environment size 3,852.  The target theorem checked in 10 ms. |
| Topological open-set intersection | `Mathlib.Topology.Defs.Basic` | `IsOpen.inter` | Accepted | SQLite-cache run reused 14 declarations and checked 10 new declarations. |
| Topological indexed union | `Mathlib.Topology.Basic` | `isOpen_iUnion` | Accepted | SQLite-cache run reused 48 declarations and checked 18 new declarations. |
| Filter infimum membership | `Mathlib.Order.Filter.Basic` | `Filter.mem_inf_iff` | Accepted | SQLite-cache run reused 755 declarations and checked 49 new declarations. |
| Filter complete lattice instance | `Mathlib.Order.Filter.Basic` | `Filter.instCompleteLatticeFilter` | Accepted | SQLite-cache run reused 840 declarations and checked 132 new declarations. |
| Real square-root continuity | `Mathlib.Data.Real.Sqrt` | `Real.continuous_sqrt` | Accepted | After same-constant application congruence, v4 cache replay reused 6,553 declaration entries, checked 3,559 new entries, accepted 10,112 target declarations, and produced environment size 10,955.  The old `Rat.addCommGroup._proof_1` wall now checks in the focused profiler in 12 ms. |
| Polynomial eta | `Mathlib.Algebra.Polynomial.Basic` | `Polynomial.eta` | Accepted | SQLite-cache run reused 568 declarations and checked 20 new declarations. |
| Polynomial constant multiplication | `Mathlib.Algebra.Polynomial.Basic` | `Polynomial.C_mul` | Accepted | The first run exposed the `Eq.ndrec` boundary: MPC had modeled Lean's transparent `Eq.ndrec` abbreviation as a second equality primitive, so conversion could leave `Eq.rec` and `Eq.ndrec` as distinct constant heads.  After moving `Eq.ndrec` back to ordinary definition checking, cache replay reused 3,942 declarations, checked 348 new declarations, and produced environment size 5,777. |
| Continuous function composition | `Mathlib.Topology.Continuous` | `Continuous.comp` | Accepted | SQLite-cache run reused 25 declarations and checked 6 new declarations. |
| Filter tendsto composition | `Mathlib.Order.Filter.Tendsto` | `Filter.Tendsto.comp` | Accepted | The first command used the unqualified root `Tendsto.comp`, which `lean4export` rejected because the exported name is `Filter.Tendsto.comp`.  The corrected root reused 331 declarations and checked 5 new declarations. |
| Polynomial `X` multiplication | `Mathlib.Algebra.Polynomial.Basic` | `Polynomial.X_mul` | Accepted | SQLite-cache run reused 4,247 declarations and checked 26 new declarations. |
| Module extensionality | `Mathlib.Algebra.Module.Defs` | `Module.ext'` | Accepted | SQLite-cache run reused 385 declarations and checked 8 new declarations. |
| Continuous finite supremum | `Mathlib.Topology.Order.Lattice` | `Continuous.finset_sup` | Accepted | SQLite-cache run reused 1,957 declarations and checked 486 new declarations. |
| Linear-map vector cons application | `Mathlib.LinearAlgebra.Pi` | `LinearMap.vecCons_apply` | Accepted | The first run exposed `Fin.cons_zero`: an `Eq.rec` transport remained stuck because its endpoints differed only in proof fields.  After endpoint conversion for equality-rec K reduction, the root reused 742 declarations, checked 25 new declarations, and produced environment size 6,504. |
| Matrix multiplication continuity | `Mathlib.Topology.Instances.Matrix` | `Continuous.matrix_mul` | Accepted | The module build pulled in a large determinant, multilinear, polynomial, and group-action closure.  MPC replay reused 2,040 declarations, checked 65 new declarations, and produced environment size 6,577. |
| Matrix determinant continuity | `Mathlib.Topology.Instances.Matrix` | `Continuous.matrix_det` | Accepted | The first stats run reused 5,546 declaration entries, checked 1,495 new entries, and produced environment size 9,820 in 240,657 ms.  A cache-only rerun then reused all 7,041 target declarations. |
| Linear-map determinant composition | `Mathlib.LinearAlgebra.Determinant` | `LinearMap.det_comp` | Accepted | The run first exposed `LinearEquiv.noConfusion` and then `_private.Mathlib.LinearAlgebra.InvariantBasisNumber.0.inducedEquiv._proof_4` as conversion-throughput walls.  With the replay-level success cache on checked misses, v4 cache replay reused 12,736 declaration entries, checked 56 new entries, accepted 12,792 target declarations, and produced environment size 13,748. |
| Functor map composition associativity | `Mathlib.CategoryTheory.Functor.Basic` | `CategoryTheory.Functor.map_comp_assoc` | Accepted | The first attempt used the unqualified root and exposed the driver guard against metadata-only exports.  The corrected root reused 340 declarations, checked 21 new declarations, and produced environment size 6,606. |
| Fully faithful functor isomorphism reflection | `Mathlib.CategoryTheory.Functor.FullyFaithful` | `CategoryTheory.isIso_of_fully_faithful` | Accepted | SQLite-cache run reused 322 declaration entries, checked 16 new entries, and produced environment size 9,842. |
| Adjunction composition unit | `Mathlib.CategoryTheory.Adjunction.Basic` | `CategoryTheory.Adjunction.comp_unit_app` | Accepted | SQLite-cache replay reused 455 declaration entries, checked 83 new entries, and produced environment size 11,237. |
| Pullback map composition | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` | `CategoryTheory.Limits.pullback.map_comp` | Accepted | The module build added comma-category, Yoneda, adjunction, cone, and pullback support.  SQLite-cache replay reused 373 declaration entries, checked 114 new entries, and produced environment size 10,159. |
| Pushout map composition | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` | `CategoryTheory.Limits.pushout.map_comp` | Accepted | SQLite-cache replay reused 414 declaration entries, checked 73 new entries, and produced environment size 11,045. |
| Kernel comparison projection | `Mathlib.CategoryTheory.Limits.Shapes.Kernels` | `CategoryTheory.Limits.kernelComparison_comp_ι` | Accepted | The module build added zero objects, equalizers, images, zero morphisms, and kernel support.  SQLite-cache replay reused 434 declaration entries, checked 81 new entries, and produced environment size 11,329. |
| Cokernel comparison projection | `Mathlib.CategoryTheory.Limits.Shapes.Kernels` | `CategoryTheory.Limits.π_comp_cokernelComparison` | Accepted | SQLite-cache replay reused 477 declaration entries, checked 55 new entries, and produced environment size 11,384. |
| Abelian image-zero lemma | `Mathlib.CategoryTheory.Abelian.Basic` | `CategoryTheory.Abelian.image_ι_comp_eq_zero` | Accepted | The first attempt used the unqualified root `CategoryTheory.image_ι_comp_eq_zero`, and the driver rejected the metadata-only export.  The corrected root exposed the old v2 cache and whole-file parsing resource boundary, then accepted through the migrated v3 cache.  A fresh v4 SHA-256 cache run checked all 5,174 declaration entries from the artifact, produced environment size 5,753, and left a 29 MB DB; a timed warm replay reused all entries in 135.290 seconds. |
| Abelian image/coimage batch | `Mathlib.CategoryTheory.Abelian.Basic` | Five roots through `CategoryTheory.Abelian.monoLift_comp` | Accepted | SQLite-cache replay reused all 5,552 declaration entries and produced environment size 6,182.  The batch widens the abelian image/coimage comparison and epi/mono factorization coverage. |
| Abelian pullback/pushout batch | `Mathlib.CategoryTheory.Abelian.Basic` | Six roots through `CategoryTheory.Abelian.mono_inl_of_factor_thru_epi_mono_factorization` | Accepted | SQLite-cache replay reused 5,447 declaration entries, checked 185 new entries, and produced environment size 6,250.  The run checks pullback preservation of epimorphisms, pushout preservation of monomorphisms, and the biproduct support used in those proofs. |
| Abelian exactness batch | `Mathlib.CategoryTheory.Abelian.Basic` | Eight roots through `CategoryTheory.Functor.reflects_exact_of_faithful` | Accepted | SQLite-cache replay reused 6,295 declaration entries, checked 138 new entries, and produced environment size 7,115.  The batch first exposed the missing singleton-inductive conversion rule through `PUnit`, then accepted after warm-cache runs through exactness, left and right homology data, and faithful-functor exactness reflection. |
| Snake lemma no-main support | `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma` | Four roots through `CategoryTheory.ShortComplex.SnakeInput.naturality_δ` | Accepted | V4 cache replay reused 5,095 declaration entries, checked 2,596 new entries, and produced environment size 8,447.  The run passed the previous `walkingParallelPairOpEquiv._proof_2` equality-rec endpoint gap and checked through the snake-input naturality support.  The slowest declarations were `HomologyData.ofAbelian._proof_2` at 550,380 ms, `HomologyData.ofAbelian` at 290,910 ms, and `FinCategory.asTypeEquivObjAsType._proof_2` at 169,275 ms. |
| Snake lemma main batch | `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma` | `CategoryTheory.ShortComplex.SnakeInput.snake_lemma` plus support roots | Accepted | V4 cache replay reused 7,525 declaration entries, checked 495 new entries, and produced environment size 8,795.  The main theorem checked at declaration index 7,893 in 70,865 ms after the support prefix had been reused.  The next slowest checked declaration was `CategoryTheory.ComposableArrows.exact_iff_δ₀` at 46,348 ms. |
| Product family map composition | `Mathlib.CategoryTheory.Limits.Shapes.Products` | `CategoryTheory.Limits.Pi.map_comp_map` | Accepted | SQLite-cache replay reused 430 declaration entries, checked 58 new entries, and produced environment size 11,109. |
| Coproduct family map composition | `Mathlib.CategoryTheory.Limits.Shapes.Products` | `CategoryTheory.Limits.Sigma.map_comp_map` | Accepted | SQLite-cache replay reused 462 declaration entries, checked 37 new entries, and produced environment size 11,148. |
| Measure metric distance | `Mathlib.MeasureTheory.Constructions.BorelSpace.Metric` | `Measurable.dist` | Accepted | The first cached stats run exposed a SQLite temporary-storage failure in requested-content lookup, and the next run reached the same rational proof wall as `Real.continuous_sqrt`.  After same-constant application congruence, v4 cache replay reused 9,312 declaration entries, checked 1,169 new entries, accepted 10,481 target declarations, and produced environment size 11,319. |

The quotient probe reached MPC replay, checked the declaration prefix, and then exposed a WHNF bug in conversion.  Inspecting the exported `Quot.congr_mk` term showed that Lean's ordinary `rfl` proof depends on `Quot.congr` and `Quot.map` reducing through a partial `Quot.lift`.  The fixed run accepts the root, so the next probe can move past the low-level quotient constructor case.

The first finite-set range boundary now accepts after the wider cache population and conversion improvements.  The old hard proof remains an ordinary generated proof from Lean's range/list arithmetic support, but it no longer blocks the selected root.  This reinforces the current pattern: several early mathlib walls were dependency-local proof-throughput costs that become manageable once shared support is checked and reused.

The first algebra probes accepted through the same path.  These roots exercise class-heavy structures, bundled homomorphisms, inverse/cancellation lemmas, and `List.TFAE` proposition packaging without exposing a new checker rule.

The prime-factorization probe now accepts after the `Nat.sqrt` dependency region was checked by a wider analysis probe.  The remaining expensive declarations in that slice are still ordinary numeric proof conversions around `Nat.sqrt`, linear arithmetic, division, shifts, and overloaded arithmetic projections.  This result changes the root status from a blocker to a cache-amortized dependency cost.

The first `BigOperators` probes now accept.  The finite-set product root originally reached a large generated proof inside Lean's `Init.Grind.Ring.Basic`, but later wide probes cached that dependency region.  The final run checked only a small suffix through `Finset.prod_biUnion`, so the old wall is now classified as amortized proof-term throughput rather than a new rule package.

The first topology, filter, and polynomial probes accepted after the equality-boundary fix.  `Polynomial.C_mul` was the useful semantic failure in this batch because it showed that Lean exports `Eq.ndrec` as an ordinary transparent abbreviation over `Eq.rec`.  Treating that abbreviation as a primitive created a false constant-head mismatch, while checking it as a definition keeps the MPC equality core at `Eq`, `Eq.refl`, and `Eq.rec`.

The real square-root continuity probe now accepts.  The old rational proof wall came from unfolding shared arithmetic heads before trying same-headed application congruence, which made a small `Rat.addCommGroup._proof_1` theorem behave like a large transparent-normalization problem.  Same-constant application congruence removes that wall and also lets the later measure-theory root pass the same dependency region.

The first linear-algebra probe exposed a second equality-rec boundary.  `Fin.cons_zero` uses a transport whose endpoints are equal only after ordinary conversion sees that two `Fin` constructor proof fields are proof-irrelevant.  MPC now allows the K-style `Eq.rec` conversion case when endpoint conversion succeeds, while keeping the cheap weak-head reducer for the reflexive and alpha-equal cases.

The first matrix-topology probe accepted without a new checker rule.  The useful signal is breadth rather than declaration count: `Mathlib.Topology.Instances.Matrix` forced Lake through a much larger dependency build, including matrix determinant, multilinear maps, polynomial definitions, finite-dimensional linear algebra, and topology algebra modules.  The exported target slice still reused most checked declarations from the shared cache and added only 65 new declaration entries.

The determinant-continuity probe also accepts, but it is a larger replay target than matrix multiplication.  The first stats run checked 1,495 declarations that were absent from the shared cache and took about 241 seconds of measured replay time.  Those checked declarations now persist in the shared cache, and the immediate cache-only rerun reused all 7,041 target declarations.

The determinant-composition probe accepts with the replay-level success cache.  Its hard declaration was repeated successful non-alpha conversion over inherited algebra structures, so the cache belongs to the adapter policy rather than to `MPC.Check`.  This probe remains a performance case for conversion reuse, not a rule-package gap.

The linear-map determinant probe hits a generated-support performance boundary before the determinant composition theorem.  `LinearEquiv.noConfusion` is the first uncached declaration after a fast reused prefix, and it is a generated definition over heterogeneous equality and many structure fields.  The v4 retry confirms that the boundary is independent of the old cache format and the earlier low-disk host condition.  Cached declaration profiling reaches the hard declaration and classifies the term as ordinary transparent-definition checking, with no static evidence for a missing recursor, projection, quotient, equality-rec, equality-ndrec, or primitive-Nat reduction rule.  A larger-host monitored stats retry remained active in the same declaration for more than one hour with flat RSS after prefix replay, so any shortcut belongs outside the MPC typing rules unless the project explicitly adds a derived checker for this class of declarations.

The first category-theory probe accepted after correcting the root name.  `CategoryTheory.Functor.map_comp_assoc` stresses universe-polymorphic structures, category instances, scoped notation expansion, and a `grind` proof over associativity fields, while the replay itself remains small.  This result is useful because it moves MPC into a different mathlib style without adding a new primitive, inductive, quotient, equality, or projection rule.

The fully faithful functor probe accepts through the same category-theory path.  `CategoryTheory.isIso_of_fully_faithful` adds the isomorphism reflection pattern for fully faithful functors and reuses most of the earlier category cache entries.  The replay checked only 16 new declarations, so it widens category coverage without introducing a new performance or rule-package boundary.

The adjunction-composition probe accepts in the same broad category slice.  `CategoryTheory.Adjunction.comp_unit_app` checks the unit component for a composed adjunction, including the surrounding natural transformation, whiskering, unitor, and associator declarations.  The run adds 83 checked declarations and gives coverage outside the limits-cone path.

The pullback map-composition probe accepts and moves the category slice into finite limits.  Building the module added comma categories, Yoneda, adjunctions, cone infrastructure, and pullback constructions to the external mathlib checkout.  MPC replay checked 114 declarations beyond the shared cache, so the result adds useful coverage without exposing a new checker rule.

The pushout map-composition probe accepts as the colimit-side companion in the same module.  It reused the pullback build and most of the category cache, then checked 73 declarations for the pushout side.  This gives both binary pullback and binary pushout map-composition coverage under the same finite-limits and finite-colimits support.

The kernel-comparison probe accepts and moves the category slice into zero morphisms and kernels.  Building the module added zero objects, equalizers, image declarations, and kernel support in the external checkout.  MPC checked 81 new declarations, covering the comparison morphism from a functor-applied kernel to the kernel of the mapped morphism.

The cokernel-comparison probe accepts as the dual zero-morphism case in the same module.  `CategoryTheory.Limits.π_comp_cokernelComparison` reused most of the kernel-comparison cache and checked 55 declarations.  The pair covers both kernel and cokernel comparison projections for functors that preserve zero morphisms.

The product-family map-composition probe accepts in the products module.  `CategoryTheory.Limits.Pi.map_comp_map` checks the dependent product-family version of the same categorical map-composition pattern.  The run adds 58 checked declarations beyond the shared cache, expanding the finite-limits coverage from binary shapes to product families.

The coproduct-family map-composition probe accepts as the dual family-shaped category case.  `CategoryTheory.Limits.Sigma.map_comp_map` reused most of the product-family cache and checked 37 new declarations.  The two product-family probes give both product and coproduct map-composition coverage in the same finite-shape infrastructure.

The abelian-category probe first exposed an adapter resource boundary.  The unqualified root `CategoryTheory.image_ι_comp_eq_zero` produced only exporter diagnostics and metadata, and the probe driver rejected that artifact before invoking MPC.  The corrected root `CategoryTheory.Abelian.image_ι_comp_eq_zero` built successfully and exported a 27 MB artifact, but the old v2-cache path was killed with exit code 137 before producing declaration stats or a semantic rejection.  After the v3 cache migration and streaming cache replay, the same artifact accepted through `--cache-layer` with all 5,174 declaration entries reused.  The later v4 digest-cache run checked the artifact from an empty cache and accepted the same declaration set, then reused every entry on a timed warm replay.

The next three abelian batches accepted.  The first added coimage/image comparison facts and the epi/mono factorization API through `monoLift_comp`; the migrated cache already contained all 5,552 target declarations by the time of the recorded run.  The second added the pullback and pushout stability lemmas for epimorphisms and monomorphisms, checking 185 new declarations around the biproduct presentation of pullbacks and pushouts.  The third added exactness and homology-data facts through `Functor.reflects_exact_of_faithful`; it first exposed the singleton-inductive conversion gap for `PUnit`, then accepted after the fix with several conversion-heavy homology proofs amortized through SQLite.

The snake-lemma support artifact exposed a narrower equality-transport gap before it reached the main lemma.  `walkingParallelPairOpEquiv._proof_2` uses an indexed recursor whose target contains an `Eq.rec` over endpoints with the same application head but reducible nested arguments.  MPC now compares equality-rec endpoints by recursive WHNF-alpha structure, which allowed v4 replay to pass that declaration and accept the no-main support artifact through `CategoryTheory.ShortComplex.SnakeInput.naturality_δ`.  The main batch then accepted with the same v4 cache, checking `CategoryTheory.ShortComplex.SnakeInput.snake_lemma` in 70,865 ms after reusing the expensive support prefix.

The first measure-theory probe now accepts.  The probe first found an adapter bug: the SQLite cache lookup built one large temporary requested-content table, which exhausted SQLite temporary storage on the 834,810-row artifact.  After the cache lookup fix and the same-constant congruence change, `Measurable.dist` checks through the old rational proof wall and reaches the target theorem without exposing a measure-theory-specific rule.
