# MPC Indexed Inductive Plan

## Purpose

The indexed-inductive package should test whether MPC can add a rule package that changes declaration admission, generated declarations, normalization, and conversion without changing the artifact boundary.  The package should remain smaller than Lean's full inductive checker while exercising the same structural problem: an inductive type former can depend on parameters and indices, and each constructor can return the family at specific index terms.  The first target is a single-family package with dependent recursors and iota reduction, because that path exposes telescope and substitution errors quickly.

This package should sit beside the existing simple-inductive package.  A manifest can select the simple package or the indexed package, and the indexed package should cover the simple no-index fragment by construction.  The existing `MPC.Configs.Poc` should remain stable, while a new indexed PoC config can enable the richer package for stress testing.

## Boundary

The first implementation should admit one inductive family at a time.  It should allow level parameters, ordinary parameters, indices, constructor-field telescopes, constructor targets that apply the inductive family to the shared parameters and explicit index terms, generated constructors, one generated dependent recursor, and iota reduction for saturated recursor applications.  It should reject proposition-valued families, mutual blocks, nested positive occurrences, large elimination, projections, no-confusion helpers, and generated-record comparison inside MPC.

The package should use canonical MPC declarations.  Script and NDJSON adapters can learn the new declaration shape later, but the first package test should use native Lean data in `MPCTest.lean`.  That keeps the first failure mode inside the checker rather than inside a parser.

## First Fixture

The main accepted fixture should be a vector-like family over the existing axiomatically declared `Nat`:

```lean
Vec : (A : Type) -> Nat -> Type
Vec.nil : (A : Type) -> Vec A 0
Vec.cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Nat.succ n)
```

The test should not require Lean's primitive `Nat.rec`.  It only needs `Nat`, `Nat.zero`, and `Nat.succ` as declarations already present in the MPC test environment.  The recursor test should reduce a saturated `Vec.rec` application whose target is a `Vec.cons` constructor application, and the reduction should apply the cons minor premise to the constructor fields.

## Risk Points

The first risk is binder accounting.  The generated motive must quantify over all indices before the target value, and constructor minor premises must refer to parameters, fields, index terms, and recursive occurrences at the correct de Bruijn depths.  This is the part most likely to reveal whether the existing helper functions are too local to the simple package.

The second risk is constructor-target validation.  A constructor target must reduce to the family head applied to the declared parameters and exactly the declared number of index terms.  The checker must reject a constructor that targets the wrong family, omits an index, or uses a non-shared parameter argument.

The third risk is recursive hypotheses.  A field whose type is a recursive occurrence should produce a recursive-hypothesis binder in the corresponding minor premise, and iota reduction must pass both the recursive field and its recursive result to the minor premise.  The first implementation can start with nondependent constant motives in the reduction test, but the generated recursor type should already include the dependent recursive-hypothesis shape.

## Exit Criteria

| Criterion | Required behavior |
| --- | --- |
| Manifest selection | `MPC.Configs.IndexedPoc` enables the indexed package without changing `MPC.Configs.Poc`. |
| Admission | A vector-like indexed family checks as a declaration and generates constructors plus `Vec.rec`. |
| Recursor type | The generated recursor type checks through ordinary MPC inference. |
| Iota | A saturated `Vec.rec` application over `Vec.cons` reduces to the cons minor premise applied to the constructor fields and recursive result. |
| Rejections | The package rejects a proposition-valued indexed family and a constructor target with the wrong number of indices. |

