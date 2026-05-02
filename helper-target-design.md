# Telescope-Aware Helper Targets

## Problem

The current inductive kernel represents a nested helper target as a closed expression.  That representation works for shapes such as `List T`, because the helper target depends only on the inductive parameters.  It fails for shapes such as `(n : Nat) → WrapAt n T`, because the nested target depends on a local binder that cannot be lowered out of the field context without loss.

This is not a peripheral omission.  The same representation boundary will reappear when constructor fields become dependent and when indexed inductive families enter the subset.  The redesign therefore replaces the helper-target representation itself, not the treatment of one rejected example.

## Proposed Representation

The family of recursors should be organized around contextual target schemas rather than bare target expressions.  A target schema records the local telescope under which the helper target lives, together with the normalized target body in that context.  The schema remains parameterized by the root inductive parameters, because every helper target in the family still shares the same outer parameter substitution.

The design should use two shape layers.  The first layer is a raw analysis result that still carries target schemas directly.  The second layer is the finalized family representation, in which each nested occurrence has been resolved to an index in the family table.  That split keeps positivity analysis local while removing expression-based family lookup from the trusted recursor rules.

```lean
structure TargetSchema where
  locals : List Binder
  target : Expr
  headName : Name

inductive RawFieldShape where
  | none
  | direct
  | pi : Binder → RawFieldShape → RawFieldShape
  | nested : TargetSchema → RawFieldShape

inductive FieldShape where
  | none
  | direct
  | pi : Binder → FieldShape → FieldShape
  | nested : Nat → FieldShape
```

The `TargetSchema.target` expression should be stored in the combined context of the root inductive parameters and the local telescope, with the local telescope innermost.  The body should already be normalized by the same canonicalization routine used by positivity analysis.  `headName` should be derived from the normalized target body, not trusted as separate input.

## Schema Invariants

Each target schema should satisfy four invariants.  First, `target` must decompose as an application of an earlier inductive or the root inductive itself after the root recursive occurrence has been specialized away into one of that inductive's positive parameters.  Second, the schema may mention only the root parameters and the local telescope recorded in `locals`.  Third, both the local binder types and the target body must be stored in canonical normalized form.  Fourth, schema equality should ignore binder names but respect binder order, binder-type definitional equality, and normalized target-body equality under that telescope.

Those invariants make family lookup structural.  The current kernel uses repeated `alphaEq` tests on helper-target expressions after reduction.  The revised kernel should intern each schema once, assign it an index, and use that index everywhere else in typing and reduction.

## Family Construction

`analyzeRecursiveShape` should return `RawFieldShape`.  When it descends through a `Π` binder, it should extend the local telescope carried by the recursive analysis rather than attempting to lower the nested target immediately.  When it reaches a nested positive target, it should package the current local telescope together with the normalized target body as a `TargetSchema`.

`buildRecursorFamily` should then intern raw schemas into a family table.  Interning should canonicalize the local binder types and the target body before comparison, then reuse an existing target index when the schema already appears in the table.  After interning, every raw field shape should be rewritten to an indexed `FieldShape`, so the remainder of the kernel works with a stable family graph rather than repeated expression comparisons.

## Motives and Minor Premises

If the family target at index `i` has schema `Δ ⊢ U`, the corresponding motive type should be `∀ Δ, U → Sort u`.  The helper recursor `rec_i` should therefore take the common parameter telescope, the full vector of family motives, the full vector of family minor premises, the local telescope `Δ`, and then a target term `t : U`.  Its result type should be the application of motive `i` to the local variables and `t`.

Minor-premise generation should use the same schema.  For a constructor of target `U`, the minor premise should quantify first over `Δ`, then over the constructor fields specialized by the root parameters and the local variables, then over the induction hypotheses determined by the specialized field shapes, and finally return the motive for that constructor application.  This change is the point where helper recursors become faithful to binder-dependent nested targets rather than only to closed ones.

## Induction Hypotheses

The surrounding `FieldShape.pi` constructors already describe the local function binders that appear in a recursive field.  After interning, a nested field shape `nested i` should be interpreted relative to that surrounding telescope.  The schema at family index `i` is required to match that telescope, so induction-hypothesis typing can apply motive `i` to the local variables and the recursive field term without reconstructing the target by syntactic search.

This gives the expected result for the previously rejected example.  If a field has type `(n : Nat) → WrapAt n T`, its induction hypothesis becomes `(n : Nat) → motive_wrapAt n (f n)`, and the corresponding helper recursor application becomes `WrapAt.rec_helper ... n (f n)`.  No lowering step is required, because the helper target remains contextual all the way through motive formation and reduction.

## Reduction

The reduction rule for helper recursors must account for local telescopes explicitly.  `splitFamilyRecursorArgs` should become target-specific: after the common parameters, motives, and minors, it should consume the local arguments prescribed by the target schema before the final target term.  Iota reduction should then compare the constructor target against the instantiated schema target in that extended local context, including the parameter-matching side condition already added to the current reducer.

This change removes the remaining expression-based helper-target lookup from normalization.  Reduction will inspect the family target chosen by the recursor constant, instantiate its schema with the explicit parameters and local arguments, and then verify that the actual constructor target matches that instantiated schema definitionally.  The operational rule then becomes a direct implementation of the stored family data rather than a partial re-derivation from raw syntax.

## Status

The repository now implements this redesign.  `TargetSchema`, `RawFieldShape`, and indexed `FieldShape` replaced the old closed helper-target representation.  Family construction, motive formation, induction-hypothesis generation, and iota reduction now use interned target schemas rather than expression lookup on lowered helper targets.

The next step is no longer the helper-target rewrite itself.  The next step is to extend the same representation to constructor-field dependencies and indexed inductive families.  This redesign should still remain separate from `Prop`, large elimination, and general universe polymorphism, because those extensions do not determine the present inductive-core boundary.
