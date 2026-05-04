# MPC Equality Plan

## Purpose

The equality package should turn the minimal equality support used by quotients into an explicit rule package.  Quotients currently need `Eq` and `Eq.refl` to type the respectfulness proof for `Quot.lift`.  Equality transport adds the next kernel behavior: primitive elimination over reflexive equality with a reduction rule that performs dependent transport.

This package should stay narrow.  It should install primitive equality constants, type-check those primitive declarations through MPC, and add the reflexive reduction rules for `Eq.rec` and `Eq.ndrec`.  It should not add theorem-library conveniences, rewrite tactics, heterogeneous equality, proof-term reconstruction, or artifact-specific equality records.

## Boundary

The first primitive set should be:

| Constant | Role |
| --- | --- |
| `Eq` | Equality type former. |
| `Eq.refl` | Reflexivity constructor. |
| `Eq.rec` | Dependent equality eliminator. |
| `Eq.ndrec` | Nondependent equality eliminator. |

The computational rules should be:

```lean
Eq.rec α a motive minor a (Eq.refl α a)  ~~>  minor
Eq.ndrec α a motive minor a (Eq.refl α a) ~~>  minor
```

The reduction rules should live in normalization, so conversion sees reflexive transports as definitional equalities.  The package should reduce only when the equality proof reduces to `Eq.refl`; it should leave non-reflexive proof heads neutral.

## Quotient Dependency

The quotient package should stop installing private equality constants.  It should require the equality primitives to exist in the environment before installing quotient primitives.  `MPC.Configs.QuotPoc` should enable both equality and quotient packages, but the declaration script should still contain both primitive entries, so dependency ordering remains visible.

## First Fixture

The first accepted fixture should declare:

```lean
Alpha : Type
Pred : Alpha -> Type
a : Alpha
p : Pred a
```

It should then check that:

```lean
Eq.rec Alpha a (fun x _ => Pred x) p a (Eq.refl Alpha a)
```

has type `Pred a` and normalizes to `p`.  The test should also check `Eq.ndrec` on a constant motive.  Rejection coverage should include disabled primitive installation and duplicate primitive installation.

