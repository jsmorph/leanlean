# LeanLean

This repository contains a specification-first experiment for a Lean-style kernel written in Lean 4.  The current target is a focused kernel fragment with universes, transparent and opaque definitions, inductive blocks, generated recursors, propositions, equality, low-level quotients, core projections, and beta, delta, zeta, iota, projection, quotient, eta, and proof-irrelevance conversion.  The main specification lives in [`spec.md`](spec.md), the development journal lives in [`devnotes.md`](devnotes.md), and the long-range plan lives in [`plan.md`](plan.md).

The regression suite runs with `lake exe leanleantest`.  The demonstration executable runs with `lake exe leanlean`.  The Lean 4 faithfulness corpus runs with `lake exe leanleanfaith`, using `LEANLEAN_LEAN` when a specific compiler binary should be checked.
