# MPC Natural Primitive Reduction Plan

## Purpose

The natural primitive reduction package should bring the standalone MPC conversion relation up to the source-backed Lean 4.29 table already recorded in the specification.  The package covers constants whose exported declarations are ordinary transparent definitions but whose Lean kernel computation uses an overridden rule.  The rule package therefore belongs in conversion, because replayed proof terms can rely on the equality even when no source term mentions the primitive in the final theorem statement.

## Boundary

The package is selected by the MPC manifest.  When selected, weak-head reduction checks a reserved constant name before ordinary delta unfolding and applies only the named rule for that constant.  Each rule first checks the declaration shape in the environment, including universe arity, type, transparent-definition status, and the required constructor metadata for boolean results.

The first package should match the admitted Lean 4.29 table from `spec.md`: `Nat.add`, `Nat.mul`, `Nat.pow`, `Nat.sub`, `Nat.beq`, and `Nat.ble`.  Numeric arguments are raw natural literals or constructor spines using `Nat.zero` and `Nat.succ`.  Boolean-valued reductions return `Bool.true` or `Bool.false` only after checking that the selected constant is a nullary constructor of `Bool` with type `Bool`.

## Rules

| Constant | MPC rule |
| --- | --- |
| `Nat.add` | Reduce `Nat.add a 0` to `a` and `Nat.add a (succ b)` to `succ (Nat.add a b)` after reducing the second argument to weak-head form. |
| `Nat.mul` | Reduce two numeric arguments to the raw literal for multiplication. |
| `Nat.pow` | Reduce two numeric arguments to the raw literal for exponentiation. |
| `Nat.sub` | Reduce two numeric arguments to the raw literal for truncated subtraction. |
| `Nat.beq` | Reduce two numeric arguments to the checked `Bool` constructor for equality. |
| `Nat.ble` | Reduce two numeric arguments to the checked `Bool` constructor for less-than-or-equal comparison. |

## Tests

The native MPC fixture should declare `Nat`, `Bool`, and transparent definitions for the six primitive names, then check the reductions through ordinary `normalize` and `defEq`.  Rejection tests should replace one primitive declaration with the wrong type or declaration kind and should replace one boolean constructor with the wrong type.  The tests should also show that the package is manifest-gated: the base PoC may still unfold transparent definitions, but it does not apply the overridden primitive rule before delta reduction.
