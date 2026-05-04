# MPC Prop Inductive Plan

## Purpose

The Prop inductive package should add proposition-valued inductive declarations to the standalone MPC without hiding elimination policy inside the existing data-inductive path.  The first slice should admit simple proposition-valued inductives and generate Prop-only recursors.  Large elimination remains a later rule.

## Boundary

The package is selected by the manifest.  The base PoC keeps the data-only simple-inductive rule, while `InductivePropPoc` enables the Prop-valued path.  Admission should require the general Prop package, because the checker must understand `Sort 0`, proposition-valued functions, and proof irrelevance before it admits Prop inductive declarations.

The first recursor form uses a motive whose result is `Prop`, not `Sort u`.  It therefore does not introduce a fresh motive universe parameter.  Iota reduction should use the same constructor-headed reduction path as data recursors, with no artifact-specific checks or generated-record comparison inside MPC.

## Tests

The first fixture should keep the base PoC rejection for `PropOnly : Prop`.  The new manifest should accept the same declaration, generate `PropOnly.intro` and `PropOnly.rec`, infer the recursor type, and reduce `PropOnly.rec motive minor PropOnly.intro` to the minor premise.  A second rejection should show that disabling the general Prop package rejects the Prop-inductive package.
