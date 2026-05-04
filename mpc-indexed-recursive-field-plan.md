# MPC Indexed Recursive Field Plan

## Purpose

The next indexed-inductive slice should handle recursive proof fields that occur under binders.  This is the smallest rule needed before artifact work can help with the gcd example, because Lean's well-founded recursion support depends on `Acc`, whose constructor contains a field of the form `∀ y, r y x -> Acc r y`.

## Boundary

The package should extend indexed recursor metadata rather than add a separate recursor implementation.  A recursive field record should name the constructor field, the binder telescope between the field value and the recursive occurrence, and the recursive target indices.  Direct recursive fields are the special case with an empty telescope.

Recursor type generation should turn a field `f : ∀ y : A, h : r y x, I y` into an induction-hypothesis argument `∀ y : A, h : r y x, motive y (f y h)`.  Iota reduction should construct that hypothesis as a lambda whose body calls the same recursor on `f y h`.  The first implementation should keep nested helper targets, large Prop elimination, and mutual blocks outside the standalone MPC.

## Tests

The fixture should add an `Acc`-shaped indexed Prop family with one constructor.  It should check that the generated recursor type contains a function-valued induction hypothesis and that reducing the recursor on a constructor target supplies the minor premise with that hypothesis.  The test should inspect the minor result through an applied marker function, so reduction must build the recursive-hypothesis lambda rather than merely count fields.
