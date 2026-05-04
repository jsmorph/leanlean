# MPC Universe Comparison Plan

## Purpose

Universe comparison belongs to the base MPC theory rather than to an optional manifest package.  The current standalone level normalizer handles the first PoC cases, but Lean 4.29 replay needs the specified symbolic equations for `max` and `imax`.  The next step should port the source-backed comparison already used by the main checker into the standalone `MPC.Level` module.

## Boundary

The comparison should normalize `max` levels by flattening summands and keeping the largest offset for each parameter.  It should reduce `imax a b` to `0` when `b` is `0`, to `max a b` when `b` is known to be a data universe, and otherwise leave the `imax` form available for equality and ordering.  Equality should identify `imax 0 u`, `imax 1 u`, and `imax u u` with `u`, while ordering should prove an unresolved `imax a b` is at most `c` when both `a` and `b` are at most `c`.

## Tests

The fixture should stay at the level API.  It should check dominated `max` summands, `imax 0 u = u`, `imax 1 u = u`, `imax u u = u`, and an unresolved `imax` ordering fact.  It should also keep a negative comparison between unrelated parameters so the broader rules do not collapse symbolic universes.
