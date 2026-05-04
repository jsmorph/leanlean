# MPC Quotient Plan

## Purpose

The quotient package should test primitive declarations and primitive reduction.  Indexed inductives stressed generated recursors and telescope accounting.  Quotients stress a different boundary: a rule package should add named primitives with ordinary types, attach trusted metadata to selected constants, and add one reduction rule without turning parser artifacts into checker rules.

The first implementation should remain small.  It should include the quotient primitives needed to type and reduce `Quot.lift`, plus the minimal equality primitive needed to state the respectfulness proof.  It should not include full equality elimination, quotient API conveniences, setoid abstractions, extensionality principles, or artifact import.

## Boundary

The package should install primitive constants through an explicit declaration entry.  A manifest must enable quotients, and replay should reject the primitive entry when the package is disabled.  The primitive declarations should have canonical MPC types, so the rest of the checker sees ordinary constants unless normalization reaches the special reduction metadata.

The first primitive set should be:

| Constant | Role |
| --- | --- |
| `Eq` | Minimal equality type former, used to type quotient respectfulness proofs. |
| `Eq.refl` | Minimal equality constructor.  The first package does not add equality eliminators. |
| `Quot` | Primitive quotient type former. |
| `Quot.mk` | Representative injection. |
| `Quot.lift` | Eliminator with a respectfulness proof. |
| `Quot.ind` | Proposition-valued induction principle. |
| `Quot.sound` | Equality proof for related representatives. |

The primitive reduction rule is:

```lean
Quot.lift α r β f h (Quot.mk α r a)  ~~>  f a
```

The rule should live in normalization and therefore in conversion.  The proof argument `h` should be checked by ordinary typing but ignored by reduction, matching the computational behavior of quotient lifting.

## First Fixture

The first accepted fixture should declare ordinary constants:

```lean
α : Type
β : Type
r : α -> α -> Prop
f : α -> β
h : ∀ a b, r a b -> Eq β (f a) (f b)
a : α
ra : r a a
```

The test should check that `Quot.lift α r β f h (Quot.mk α r a)` has type `β` and normalizes to `f a`.  The fixture should also check that the primitive package cannot be installed when quotients are disabled.

## Exit Criteria

| Criterion | Required behavior |
| --- | --- |
| Manifest selection | A new quotient PoC config enables quotients without changing the earlier PoC configs. |
| Primitive replay | The quotient primitive declaration installs the equality and quotient constants exactly once. |
| Typing | `Quot.lift` applications infer the expected result type through ordinary application checking. |
| Reduction | `Quot.lift f h (Quot.mk r a)` normalizes to `f a`. |
| Rejections | Replay rejects quotient primitive installation when the manifest disables quotients and rejects duplicate primitive installation. |

