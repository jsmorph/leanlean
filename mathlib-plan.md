# Mathlib Probe Plan

## Purpose

Mathlib gives MPC a gap-finding corpus without becoming a dependency of the MPC repository.  The near-term goal is to export selected mathlib roots, run them through the existing `mpc-check-export` path, and classify the first real checker boundary exposed by each artifact.  A probe succeeds when it tells us whether the next problem is a missing rule package, a rule-package side condition, proof-term performance, generated-declaration audit behavior, or artifact translation.

This plan targets selected roots rather than bulk mathlib checking.  Bulk checking would mix dependency management, artifact size, proof-term performance, and checker soundness into one result that would be hard to interpret.  Targeted probes give better engineering evidence because each selected root has a reason, an expected stress area, and a recorded outcome.

## Boundary

The MPC repository keeps mathlib outside its Lake dependencies for this work.  A probe uses an existing external mathlib checkout built with the Lean version compatible with this repository and the installed `lean4export` binary.  The MPC side remains the checker executable, optional cache DB, profile output, and a small driver script if repeated manual commands become error-prone.

Generated artifacts and profiling output stay out of git.  Use `.tmp/mathlib-probes` or a caller-provided directory for NDJSON, root files, timing JSONL, and cache DBs.  The persistent cache remains an adapter-side optimization: useful for repeated probes, but not part of the checker claim.

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
| Finset range filter | `Mathlib.Data.Finset.Basic` | `Finset.range_filter_eq` | Rejected: performance | Replay reached declaration index 1430, `_private.Init.Data.List.Nat.Range.0.List.pairwise_lt_range'._proof_1_4`, then exceeded the useful probe budget.  The selected declaration has 32,596 expression nodes, 16,094 app nodes, 5,457 transparent-definition constants, and 3,799 transparent-definition head applications. |
| Finset unique choice | `Mathlib.Data.Finset.Basic` | `Finset.choose_spec` | Accepted | SQLite-cache run reused 372 declarations and checked 34 new declarations. |
| Finset-to-set equivalence | `Mathlib.Data.Finset.Basic` | `Finset.equivToSet` | Accepted | SQLite-cache run reused 544 declarations and checked 13 new declarations. |
| Group left commutation | `Mathlib.Algebra.Group.Basic` | `mul_left_comm` | Accepted | SQLite-cache run reused 12 declarations and checked 13 new declarations. |
| Group inverse cancellation | `Mathlib.Algebra.Group.Basic` | `inv_mul_eq_of_eq_mul` | Accepted | SQLite-cache run reused 299 declarations and checked 67 new declarations. |
| Ring quadratic identity | `Mathlib.Algebra.Ring.Basic` | `vieta_formula_quadratic` | Accepted | SQLite-cache run reused 306 declarations and checked 169 new declarations. |
| Ring no-zero-divisors TFAE | `Mathlib.Algebra.Ring.Basic` | `noZeroDivisors_tfae` | Accepted | SQLite-cache run reused 530 declarations and checked 92 new declarations. |
| Prime factorization uniqueness | `Mathlib.Data.Nat.Factors` | `Nat.primeFactorsList_unique` | Rejected: performance | Cache stats replay reused the prefix through declaration index 2717 in 6,045 ms, then timed out at index 2718, `_private.Mathlib.Data.Nat.Sqrt.0.Nat.sqrt_isSqrt`.  The hard theorem has 9 type nodes and 47,233 value nodes; head counts are dominated by `OfNat.ofNat`, `HAdd.hAdd`, `HDiv.hDiv`, `Nat.log2`, `HShiftLeft.hShiftLeft`, `HMul.hMul`, and `Nat.sqrt`. |
| List product range division | `Mathlib.Algebra.BigOperators.Group.List.Basic` | `List.prod_range_div` | Accepted | SQLite-cache run reused 430 declarations and checked 52 new declarations. |
| Finset product over `biUnion` | `Mathlib.Algebra.BigOperators.Group.Finset.Basic` | `Finset.prod_biUnion` | Rejected: performance | Cache replay reached declaration index 2615, `_private.Init.Grind.Ring.Basic.0.Lean.Grind.Ring.intCast_nat_sub._proof_1_2`, then exceeded the useful probe budget.  The selected declaration has 196,906 expression nodes, 98,428 app nodes, 35,330 transparent-definition constants, and 25,701 transparent-definition head applications. |
| Topological open-set intersection | `Mathlib.Topology.Defs.Basic` | `IsOpen.inter` | Accepted | SQLite-cache run reused 14 declarations and checked 10 new declarations. |
| Topological indexed union | `Mathlib.Topology.Basic` | `isOpen_iUnion` | Accepted | SQLite-cache run reused 48 declarations and checked 18 new declarations. |
| Filter infimum membership | `Mathlib.Order.Filter.Basic` | `Filter.mem_inf_iff` | Accepted | SQLite-cache run reused 755 declarations and checked 49 new declarations. |
| Filter complete lattice instance | `Mathlib.Order.Filter.Basic` | `Filter.instCompleteLatticeFilter` | Accepted | SQLite-cache run reused 840 declarations and checked 132 new declarations. |
| Real square-root continuity | `Mathlib.Data.Real.Sqrt` | `Real.continuous_sqrt` | Rejected: performance | Cache stats replay reused the prefix through declaration index 3289 in 4,673 ms, then timed out at index 3290, `Rat.addCommGroup._proof_1`.  This repeats the rational proof wall seen in the measure-theory probe. |
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
| Linear-map determinant composition | `Mathlib.LinearAlgebra.Determinant` | `LinearMap.det_comp` | Rejected: performance | Cache stats replay reused the prefix through declaration index 7357 in 13,926 ms, then timed out at index 7358, `LinearEquiv.noConfusion`.  The hard declaration is a generated definition with 699 type nodes and 8,297 value nodes; head counts are dominated by `Semiring.toNonAssocSemiring`, `HEq`, `LinearEquiv`, `RingHomInvPair`, `RingHom`, and `Module`. |
| Functor map composition associativity | `Mathlib.CategoryTheory.Functor.Basic` | `CategoryTheory.Functor.map_comp_assoc` | Accepted | The first attempt used the unqualified root and exposed the driver guard against metadata-only exports.  The corrected root reused 340 declarations, checked 21 new declarations, and produced environment size 6,606. |
| Fully faithful functor isomorphism reflection | `Mathlib.CategoryTheory.Functor.FullyFaithful` | `CategoryTheory.isIso_of_fully_faithful` | Accepted | SQLite-cache run reused 322 declaration entries, checked 16 new entries, and produced environment size 9,842. |
| Adjunction composition unit | `Mathlib.CategoryTheory.Adjunction.Basic` | `CategoryTheory.Adjunction.comp_unit_app` | Accepted | SQLite-cache replay reused 455 declaration entries, checked 83 new entries, and produced environment size 11,237. |
| Pullback map composition | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` | `CategoryTheory.Limits.pullback.map_comp` | Accepted | The module build added comma-category, Yoneda, adjunction, cone, and pullback support.  SQLite-cache replay reused 373 declaration entries, checked 114 new entries, and produced environment size 10,159. |
| Pushout map composition | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` | `CategoryTheory.Limits.pushout.map_comp` | Accepted | SQLite-cache replay reused 414 declaration entries, checked 73 new entries, and produced environment size 11,045. |
| Kernel comparison projection | `Mathlib.CategoryTheory.Limits.Shapes.Kernels` | `CategoryTheory.Limits.kernelComparison_comp_ι` | Accepted | The module build added zero objects, equalizers, images, zero morphisms, and kernel support.  SQLite-cache replay reused 434 declaration entries, checked 81 new entries, and produced environment size 11,329. |
| Cokernel comparison projection | `Mathlib.CategoryTheory.Limits.Shapes.Kernels` | `CategoryTheory.Limits.π_comp_cokernelComparison` | Accepted | SQLite-cache replay reused 477 declaration entries, checked 55 new entries, and produced environment size 11,384. |
| Abelian image-zero lemma | `Mathlib.CategoryTheory.Abelian.Basic` | `CategoryTheory.Abelian.image_ι_comp_eq_zero` | Accepted | The first attempt used the unqualified root `CategoryTheory.image_ι_comp_eq_zero`, and the driver rejected the metadata-only export.  The corrected root first exposed the old v2 cache and whole-file parsing resource boundary.  After migrating the cache to v3 and streaming `--cache-layer` input, the run reused 5,174 declaration entries, checked none, and produced environment size 5,753. |
| Product family map composition | `Mathlib.CategoryTheory.Limits.Shapes.Products` | `CategoryTheory.Limits.Pi.map_comp_map` | Accepted | SQLite-cache replay reused 430 declaration entries, checked 58 new entries, and produced environment size 11,109. |
| Coproduct family map composition | `Mathlib.CategoryTheory.Limits.Shapes.Products` | `CategoryTheory.Limits.Sigma.map_comp_map` | Accepted | SQLite-cache replay reused 462 declaration entries, checked 37 new entries, and produced environment size 11,148. |
| Measure metric distance | `Mathlib.MeasureTheory.Constructions.BorelSpace.Metric` | `Measurable.dist` | Rejected: performance | The first cached stats run exposed a SQLite temporary-storage failure in requested-content lookup.  After chunked direct lookup, replay reached declaration index 3277, `Rat.addCommGroup._proof_1`; the isolated root from `Mathlib.Data.Rat.Lemmas` reproduces the same wall at index 1826 with 95 type nodes and 2,575 value nodes. |

The quotient probe reached MPC replay, checked the declaration prefix, and then exposed a WHNF bug in conversion.  Inspecting the exported `Quot.congr_mk` term showed that Lean's ordinary `rfl` proof depends on `Quot.congr` and `Quot.map` reducing through a partial `Quot.lift`.  The fixed run accepts the root, so the next probe can move past the low-level quotient constructor case.

The first serious mathlib performance boundary is an Omega-generated proof imported by a finite-set range theorem.  This is a checker-throughput problem over ordinary proof terms, not a new rule-package requirement.  The SQLite checked-layer cache now persists each checked declaration as it succeeds, so interrupted long probes keep the accepted prefix they have already checked.

The first algebra probes accepted through the same path.  These roots exercise class-heavy structures, bundled homomorphisms, inverse/cancellation lemmas, and `List.TFAE` proposition packaging without exposing a new checker rule.

The prime-factorization probe reaches a performance boundary before the requested uniqueness theorem.  `Nat.primeFactorsList_unique` depends on `Nat.sqrt_isSqrt`, and the private exported proof for that theorem is the first uncached declaration after a fast reused prefix.  This boundary belongs to ordinary numeric proof conversion around `Nat.sqrt`, `Nat.log2`, division, shifts, and overloaded arithmetic projections; it does not yet identify a primitive arithmetic rule to add to MPC.

The first `BigOperators` list probe accepted, but the corresponding finite-set product probe reached a larger generated-proof wall inside Lean's `Init.Grind.Ring.Basic`.  The stuck proof is another ordinary theorem body generated from arithmetic automation.  Its static head-frequency profile is dominated by `List.cons`, `Nat.cast`, `OfNat.ofNat`, `HSub.hSub`, `HAdd.hAdd`, `Lean.Omega.LinearCombo.mk`, and `Lean.Omega.Coeffs.ofList`, which points to proof-term throughput rather than a new rule package.

The first topology, filter, and polynomial probes accepted after the equality-boundary fix.  `Polynomial.C_mul` was the useful semantic failure in this batch because it showed that Lean exports `Eq.ndrec` as an ordinary transparent abbreviation over `Eq.rec`.  Treating that abbreviation as a primitive created a false constant-head mismatch, while checking it as a definition keeps the MPC equality core at `Eq`, `Eq.refl`, and `Eq.rec`.

The real square-root continuity probe repeats the rational proof wall.  `Real.continuous_sqrt` reaches `Rat.addCommGroup._proof_1` after a fast reused prefix and times out there, before any theorem specific to real square roots is checked.  This confirms that the Rat boundary blocks multiple analysis roots, so later real-analysis probing should either fix that performance problem or choose roots whose closures avoid the rational additive-group instance.

The first linear-algebra probe exposed a second equality-rec boundary.  `Fin.cons_zero` uses a transport whose endpoints are equal only after ordinary conversion sees that two `Fin` constructor proof fields are proof-irrelevant.  MPC now allows the K-style `Eq.rec` conversion case when endpoint conversion succeeds, while keeping the cheap weak-head reducer for the reflexive and alpha-equal cases.

The first matrix-topology probe accepted without a new checker rule.  The useful signal is breadth rather than declaration count: `Mathlib.Topology.Instances.Matrix` forced Lake through a much larger dependency build, including matrix determinant, multilinear maps, polynomial definitions, finite-dimensional linear algebra, and topology algebra modules.  The exported target slice still reused most checked declarations from the shared cache and added only 65 new declaration entries.

The determinant-continuity probe also accepts, but it is a larger replay target than matrix multiplication.  The first stats run checked 1,495 declarations that were absent from the shared cache and took about 241 seconds of measured replay time.  Those checked declarations now persist in the shared cache, and the immediate cache-only rerun reused all 7,041 target declarations.

The linear-map determinant probe hits a generated-support performance boundary before the determinant composition theorem.  `LinearEquiv.noConfusion` is the first uncached declaration after a fast reused prefix, and it is a generated definition over heterogeneous equality and many structure fields.  This result is different from the Omega and rational proof walls: the hard object is derived support generated for a structure, so any shortcut belongs outside the MPC typing rules unless the project explicitly adds a derived checker for this class of declarations.

The first category-theory probe accepted after correcting the root name.  `CategoryTheory.Functor.map_comp_assoc` stresses universe-polymorphic structures, category instances, scoped notation expansion, and a `grind` proof over associativity fields, while the replay itself remains small.  This result is useful because it moves MPC into a different mathlib style without adding a new primitive, inductive, quotient, equality, or projection rule.

The fully faithful functor probe accepts through the same category-theory path.  `CategoryTheory.isIso_of_fully_faithful` adds the isomorphism reflection pattern for fully faithful functors and reuses most of the earlier category cache entries.  The replay checked only 16 new declarations, so it widens category coverage without introducing a new performance or rule-package boundary.

The adjunction-composition probe accepts in the same broad category slice.  `CategoryTheory.Adjunction.comp_unit_app` checks the unit component for a composed adjunction, including the surrounding natural transformation, whiskering, unitor, and associator declarations.  The run adds 83 checked declarations and gives coverage outside the limits-cone path.

The pullback map-composition probe accepts and moves the category slice into finite limits.  Building the module added comma categories, Yoneda, adjunctions, cone infrastructure, and pullback constructions to the external mathlib checkout.  MPC replay checked 114 declarations beyond the shared cache, so the result adds useful coverage without exposing a new checker rule.

The pushout map-composition probe accepts as the colimit-side companion in the same module.  It reused the pullback build and most of the category cache, then checked 73 declarations for the pushout side.  This gives both binary pullback and binary pushout map-composition coverage under the same finite-limits and finite-colimits support.

The kernel-comparison probe accepts and moves the category slice into zero morphisms and kernels.  Building the module added zero objects, equalizers, image declarations, and kernel support in the external checkout.  MPC checked 81 new declarations, covering the comparison morphism from a functor-applied kernel to the kernel of the mapped morphism.

The cokernel-comparison probe accepts as the dual zero-morphism case in the same module.  `CategoryTheory.Limits.π_comp_cokernelComparison` reused most of the kernel-comparison cache and checked 55 declarations.  The pair covers both kernel and cokernel comparison projections for functors that preserve zero morphisms.

The product-family map-composition probe accepts in the products module.  `CategoryTheory.Limits.Pi.map_comp_map` checks the dependent product-family version of the same categorical map-composition pattern.  The run adds 58 checked declarations beyond the shared cache, expanding the finite-limits coverage from binary shapes to product families.

The coproduct-family map-composition probe accepts as the dual family-shaped category case.  `CategoryTheory.Limits.Sigma.map_comp_map` reused most of the product-family cache and checked 37 new declarations.  The two product-family probes give both product and coproduct map-composition coverage in the same finite-shape infrastructure.

The abelian-category probe first exposed an adapter resource boundary.  The unqualified root `CategoryTheory.image_ι_comp_eq_zero` produced only exporter diagnostics and metadata, and the probe driver rejected that artifact before invoking MPC.  The corrected root `CategoryTheory.Abelian.image_ι_comp_eq_zero` built successfully and exported a 27 MB artifact, but the old v2-cache path was killed with exit code 137 before producing declaration stats or a semantic rejection.  After the v3 cache migration and streaming cache replay, the same artifact accepted through `--cache-layer` with all 5,174 declaration entries reused.

The first measure-theory probe is classified as a performance rejection.  The probe first found an adapter bug: the SQLite cache lookup built one large temporary requested-content table, which exhausted SQLite temporary storage on the 834,810-row artifact.  The cache adapter now queries requested content keys in bounded chunks and preserves SQLite stderr on writer failures, and the remaining hard declaration is `Rat.addCommGroup._proof_1`, an ordinary theorem body built from nested equality transports around rational casts and multiplication.
