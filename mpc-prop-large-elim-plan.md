# MPC Prop Large Elimination Plan

## Purpose

The large-elimination slice should let selected proposition-valued inductives eliminate into data.  This is needed before artifact support can help with the gcd example because well-founded recursion relies on `Acc`-shaped proof objects while defining data-valued functions.

## Boundary

Large elimination should be a separate manifest mode from Prop-only inductives.  The existing Prop-only configs should keep their recursors restricted to `Prop`.  A new large-elimination config should add the fresh motive universe parameter only when a proposition-valued inductive satisfies the conservative subsingleton criterion.

The first criterion should accept constructors whose field types are propositions under the constructor telescope.  This admits `Acc`-shaped fields such as `∀ y, r y x -> Acc r y`, because the field type itself lives in `Prop`.  It does not yet implement the full index-forced data-field criterion.

## Tests

The fixture should replay the existing `Reach` family under a large-elimination manifest, infer `Reach.rec` with a motive universe parameter, and reduce a recursor whose motive returns `Nat`.  The Prop-only `Reach` test should remain unchanged, proving that large elimination is an explicit package selection.
