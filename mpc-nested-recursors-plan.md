# MPC Nested Recursors Plan

## Purpose

Nested positivity lets MPC admit an inductive such as `Lean.Syntax`, whose recursive field has type `Array Syntax`.  The Omega stress artifact then checks all ordinary declarations and rejects during generated-recorder audit because Lean exported helper recursors named `Lean.Syntax.rec_2` and `Lean.Syntax.rec_1`.  Those names are not ordinary source declarations.  They are generated recursor targets for the nested types `List Syntax` and `Array Syntax`.

The next rule package should generate the same nested recursor family that justifies those records.  The fix should not add the names as unchecked aliases, and it should not weaken generated-recorder audit.  A generated recursor is trusted kernel behavior, so MPC must derive its type and computation metadata from the inductive block and the specified nested-container rules.

## Boundary

This package belongs to inductive admission.  Artifact adapters should continue to treat exported recursor rows as redundant records.  The adapter can compare those rows only after MPC has generated the corresponding recursor constants and metadata.

The first implementation should cover one-root data inductives whose nested recursive occurrences pass through the specified unary containers already admitted by the nested-positivity package.  The target stress case is `Lean.Syntax`, where the helper targets are `List Syntax` and `Array Syntax`.  Mutual blocks, arbitrary user-defined containers, and nested indexed helper targets can remain outside this slice.

## Rule

Inductive admission should build one recursor family with a target for the root inductive and one target for each discovered nested helper schema.  A direct recursive occurrence headed by the inductive uses the root motive.  A nested occurrence under a specified covariant container creates or reuses a helper target for that instantiated container type.  For `Lean.Syntax`, the family has motives for `Syntax`, `Array Syntax`, and `List Syntax`, and minor premises for the constructors of all three targets.

Each generated recursor constant selects one family target.  The root target keeps the ordinary recursor name, for example `Lean.Syntax.rec`.  Helper targets use Lean's helper suffixes, for example `Lean.Syntax.rec_1` and `Lean.Syntax.rec_2`.  The exact numbering must follow the target discovery order from the generated family, not a post-hoc artifact list.

Each minor premise binds the target locals, constructor fields, and induction hypotheses corresponding to strictly positive fields.  A direct recursive field contributes the selected target's motive applied to the recursive value.  A nested field contributes a hypothesis through the helper target.  Iota reduction must select the recursor target, validate the constructor application against that target, and pass recursive results to the minor premise in field order.

## Implementation Notes

The older LeanLean checker already has the relevant model in `LeanLean/Kernel.lean`: `TargetSchema`, `RawFieldShape`, `FieldShape`, `RecursorFamily`, helper target discovery, recursor type generation, expected generated-recorder comparison, and iota reduction through helper targets.  MPC should not import that code, but it should port the same concepts in smaller MPC-native structures.

The current MPC structures record only direct recursive fields and binder-telescope direct fields.  They need a family-level representation that can name multiple targets and attach each constructor minor premise to a target.  The implementation should avoid turning `Array` or `List` into special recursor primitives; the container rule supplies positivity and target discovery, while the ordinary inductive recursor machinery supplies generated constants and reduction.

## Tests

Native tests should first build a small `Array`-nested inductive and assert that admission produces the root recursor and at least one helper recursor.  The test should check the helper recursor's type enough to prove that it has motives for both the root and helper target.  A second test should reduce a helper-recursive constructor case if the implementation adds iota in the same slice; otherwise the iota test should mark the next step.

The artifact test is the Omega stress fixture.  The expected movement is from generated-recorder rejection at `Lean.Syntax.rec_2` to either acceptance of the artifact or a later ordinary checker boundary.  If the artifact accepts, the result should still remain a stress script rather than a required fast regression until resource policy improves.

## Status

The first implementation slice generates the nested recursor family for one-root simple inductives through the specified unary `Array` and `List` containers.  MPC now records helper recursors with a distinct `.nestedRecursor` kind, validates their generated types during inductive admission, and lets adapter audits accept only generated names that exist in the environment.  Normalization reduces saturated nested recursor applications by selecting the target-specific minor premise and recursively applying the appropriate root or helper recursor to recursive fields.  The native fixture builds the root, `Array root`, and `List root` family shape, checks helper metadata, and reduces a `List.cons` helper-recursion case.  The Omega stress artifact accepts after checking 1245 declaration entries.
