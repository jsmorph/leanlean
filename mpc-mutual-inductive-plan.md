# MPC Mutual Inductive Plan

## Boundary

This rule package adds mutual inductive blocks to MPC without changing the single-inductive rule packages.  The first slice admits blocks whose members share the block universe parameters and parameter telescope, whose members have no indices, and whose constructors target one member of the block.  This covers ordinary mutual data types such as even/odd and exposes the block-level obligations: provisional type constructors, cross-member positivity, one recursor per block member, and reduction across member recursors.

Indexed mutual blocks remain a later slice.  Nested mutual recursion through containers also remains separate, because it composes the mutual block package with the nested-container recursor package.

## Rule Package Shape

The manifest should expose the package as `inductiveBlocks`.  A block declaration should not pass through the single-inductive declaration path.  Block admission needs a provisional environment containing every block member before any constructor field is checked, because a constructor in one member may mention another member.

The generated recursor family should use one motive per block member and one minor premise per constructor across the block.  A recursive field whose type is another block member receives an induction hypothesis from that member’s motive.  Reducing `A.rec` on a constructor for `A` invokes the constructor minor and recursively calls the corresponding `B.rec` or `A.rec` for direct recursive fields.

## Initial Tasks

- [x] Add a mutual inductive fixture that currently fails at the export adapter boundary.
- [x] Add MPC block declaration data and a manifest switch for mutual inductive blocks.
- [x] Implement simple mutual block admission, constructor generation, recursor generation, and recursor reduction.
- [x] Lower exported simple mutual groups into the new declaration form.
- [x] Add native and exported tests for the even/odd block.
