# MPC PoC Plan

## Purpose

The PoC should test whether a standalone MPC can be organized as a clean peer of the current LeanLean checker.  It should prove the package-and-manifest architecture on the parts most likely to matter: ordinary declaration admission, one local expression feature, one cross-cutting logical feature, and one declaration form that generates constants and reduction rules.

The PoC should not try to replace the current checker.  It should be small enough for peer development and review while still exercising the structural design needed for a later Lean 4.29 configuration.

## Scope

The PoC has four MPC rule packages and two artifact adapters.  The packages live in the standalone MPC library.  The adapters sit above MPC and translate input into canonical MPC declarations.

| Component | Kind | Role |
| --- | --- | --- |
| Declaration admission | Rule package | Establishes the checked environment path for axioms, transparent definitions, opaque definitions, and theorem declarations when `Prop` is enabled. |
| Natural literals | Rule package | Tests a leaf feature that affects typing and conversion without owning declaration admission. |
| `Prop` | Rule package | Tests cross-cutting behavior in function-sort inference, theorem admission, proof irrelevance, and manifest validation. |
| Simple inductives | Rule package | Tests primitive declaration admission that generates constructors, recursors, and iota reduction rules. |
| Canonical script reader | Adapter | Reads a repo-native declaration script and feeds canonical declarations to MPC. |
| NDJSON subset adapter | Adapter | Reads a small `lean4export`-style subset, translates it to canonical declarations, calls MPC, and audits redundant generated records outside MPC. |

## Rule Packages

### Declaration Admission

This package should define the canonical environment-growth path.  The first implementation should admit axioms, transparent definitions, opaque definitions, and theorem declarations.  A definition checks its declared type and value.  A transparent definition unfolds during conversion, while an opaque definition stores a checked value but does not unfold.  A theorem checks only when `Prop` is enabled and the declared type is a proposition.

The package should not include dependency-aware replay, trusted-base assumptions, generated-constructor checks, generated-recursor checks, export primitive checks, or diagnostics.  Those belong to adapters or audit layers.

### Natural Literals

This package should add raw natural literals.  A natural literal has type `Nat` when the environment contains the required `Nat`, `Nat.zero`, and `Nat.succ` declarations.  Conversion should identify raw numeric literals with matching `Nat.zero` and `Nat.succ` constructor spines.  `Nat.rec` reduction on raw literals may enter with the simple inductive package if the PoC includes the generated `Nat` recursor shape needed to test it.

String literals should stay outside the PoC or remain neutral typed literals if needed for parser coverage.  Full Lean string computation is not part of this plan.

### `Prop`

This package should add `Sort 0` as `Prop`, proposition-valued function behavior, theorem admission, and proof irrelevance.  It should make package interactions explicit.  For example, theorem declarations require `Prop`; quotients are absent from the PoC but would later require `Prop`; proposition-valued inductives should remain disabled until the inductive package grows the corresponding elimination rules.

`Prop` should not be treated as an isolated plugin.  The central checker should call named `Prop` helpers where the interaction occurs: function-sort inference, theorem admission, and conversion.

### Simple Inductives

This package should admit a deliberately narrow inductive fragment:

| Included | Excluded |
| --- | --- |
| Single inductive declarations | Mutual inductives |
| Parameters | Indexed families |
| Non-indexed constructor targets | Nested positive occurrences |
| Constructor field telescopes | Proposition-valued inductives |
| Strict positivity without nesting | Large elimination |
| Generated constructors | Projections |
| One generated recursor | Structure eta |
| Iota reduction | Generated-record comparison inside MPC |

This package is the main architectural test.  It adds a declaration form, environment metadata, generated constants, and a reduction rule used by conversion.  The first version should be data-only.  It should reject proposition-valued inductive declarations unless a later subpackage specifies the `Prop` interaction and elimination boundary.

## Manifest

The manifest should be native Lean data.  It should select from statically known packages rather than load dynamic plugins.  Central operations should take a manifest explicitly:

```lean
infer   : Manifest -> Env -> LevelContext -> Context -> Expr -> Result Expr
defEq   : Manifest -> Env -> LevelContext -> Context -> Expr -> Expr -> Result Unit
whnf    : Manifest -> Env -> LevelContext -> Expr -> Result Expr
addDecl : Manifest -> Env -> Declaration -> Result Env
replay  : Manifest -> Env -> List Declaration -> Result Env
```

The PoC manifest should enable declaration admission, natural literals, `Prop`, and simple inductives.  Manifest validation should reject incoherent combinations before checking begins.  At minimum, theorem declarations require `Prop`, natural literals require the base constants they use, and proposition-valued inductives remain unavailable in the simple inductive package.

The later Lean 4.29 configuration should be another manifest, not another checker:

```lean
def Poc : Manifest :=
  base
    + declarationAdmission
    + naturalLiterals
    + prop
    + simpleInductives

def LeanCore429 : Manifest :=
  base
    + declarationAdmission
    + prop
    + fullSpecifiedInductives
    + quotients
    + projections
    + literals429
    + primitiveReductions429
    + resourcePolicy
```

The notation above is descriptive.  The implementation can use records or closed inductive options.

## Adapters

### Canonical Script Reader

The canonical script reader should parse a repo-native declaration script into MPC declarations.  The format can be inconvenient and explicit.  Its purpose is not user ergonomics; it gives peer developers stable fixtures for the MPC API without Lean export details.

The reader should support the PoC declarations and expressions only.  It should not contain implicit elaboration, name resolution beyond the script format, source recursion, or generated-record comparison.

### NDJSON Subset Adapter

The NDJSON adapter should support a small `lean4export`-style subset:

| Supported | Outside PoC |
| --- | --- |
| Names needed by the fixtures | Full structured-name implementation |
| Levels used by the fixtures | All export level edge cases |
| Expressions used by the PoC packages | Full Lean expression import |
| Axioms, definitions, opaque definitions, theorems | Unsafe and partial policy |
| One simple inductive group | Mutual, indexed, nested inductives |
| Generated constructor and recursor audit outside MPC | Generated-record admission inside MPC |

The adapter should translate artifact records into canonical declarations, call `MPC.replay`, then compare redundant generated constructor and recursor records against the environment produced by MPC.  That comparison proves the adapter split without putting artifact redundancy into `MPC.Declaration`.

## Proposed Layout

```text
MPC/
  Basic.lean
  Name.lean
  Level.lean
  Expr.lean
  Context.lean
  Error.lean
  Env.lean
  Manifest.lean
  Check.lean
  Normalize.lean
  DefEq.lean
  Declaration.lean
  Replay.lean

  Packages/
    Declaration.lean
    Literal.lean
    Prop.lean
    Inductive/
      Basic.lean
      Positivity.lean
      Recursor.lean
      Admission.lean
      Reduction.lean

  Configs/
    Poc.lean
    LeanCore429.lean

  Adapters/
    Script.lean
    NDJSON.lean
```

The current LeanLean implementation should remain available while MPC grows beside it.  The PoC may copy ideas and tests from LeanLean, but it should avoid imports from `LeanLean.Import`, `LeanLean.Export`, `SelfCheck`, `CheckExport`, or `CheckModule`.

## Exit Criteria

- The standalone MPC library builds as a peer of LeanLean.
- `MPC.Configs.Poc` validates and enables exactly the four PoC packages.
- The canonical script reader checks accepted scripts and rejects malformed scripts for each package.
- The NDJSON subset adapter checks at least one exported fixture using declaration admission, natural literals, `Prop`, and a simple inductive.
- Generated constructor and recursor records in the NDJSON fixture are audited outside MPC.
- The PoC contains at least one rejection test for each package boundary: theorem without `Prop`, malformed natural literal environment, negative recursive occurrence, and attempted proposition-valued inductive under the simple inductive package.

## Non-Goals

This PoC does not include full Lean 4.29 parity, full string computation, quotients, projections, primitive arithmetic reductions beyond what the PoC fixtures require, mutual inductives, indexed inductives, nested positive occurrences, proposition-valued inductives, `.olean` reading, whole-artifact replay, unsafe or partial policy, generated-support burn-down, or gap reports.
