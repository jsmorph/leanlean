# MPC Projection Plan

## Purpose

The projection package should add Lean's core projection expression to MPC.  The first slice should cover one-constructor data structures admitted by the simple-inductive package.  This stresses typing, weak-head reduction, normalization, and conversion without adding export metadata or generated-record audits to MPC.

The package is deliberately narrower than Lean's full structure support.  It should not import structure-extension metadata, inherited-field flattening, parent projections, eta rules, projection declarations, or adapter-side validation.  Those can follow after core projection expressions work in the checker.

## Boundary

The first implementation should add an expression form:

```lean
Expr.proj structureName fieldIndex target
```

Typing should infer the target type, reduce it to a one-constructor simple inductive application, and compute the selected field type from the constructor telescope.  Field types may depend on parameters and earlier fields.  Earlier fields should appear in the selected field type as projection expressions from the same target.

Reduction should apply only when the target reduces to the structure constructor:

```lean
proj S i (S.mk params fields) ~~> fieldᵢ
```

Neutral projections should remain neutral.  Conversion should compare neutral projections structurally and should see constructor projections through weak-head reduction.

## First Fixture

The first fixture should define a dependent pair-like structure:

```lean
DPair (A : Type) (B : A -> Type) : Type
DPair.mk : (A : Type) -> (B : A -> Type) -> (fst : A) -> B fst -> DPair A B
```

The test should check that:

```lean
proj DPair 0 (DPair.mk Alpha Pred a predProof)
```

has type `Alpha` and reduces to `a`, and that:

```lean
proj DPair 1 target
```

has type `Pred (proj DPair 0 target)` and reduces to `predProof` when `target` is the constructor application.  This tests dependent field typing rather than only record-field extraction.

## Exit Criteria

| Criterion | Required behavior |
| --- | --- |
| Manifest selection | A projection PoC config enables projections without changing earlier configs. |
| Typing | Projection expressions infer field types from one-constructor simple inductives. |
| Dependency | A later field type can mention an earlier projection from the same target. |
| Reduction | Projections from constructor applications reduce to the selected constructor field. |
| Rejections | Projection inference rejects disabled projections and out-of-range fields. |

