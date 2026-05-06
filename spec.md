# MPC Specification

This document specifies MPC, the standalone minimal principled checker.  MPC checks a canonical kernel declaration language, grows a checked environment, and implements the conversion rules selected by a static manifest.  The specification is the target contract for MPC code and for any adapter that translates external artifacts into MPC declarations.

MPC has a small kernel boundary.  It owns names, universe levels, expressions, contexts, substitution, environments, typing, conversion, normalization, declaration admission, and the rule packages selected by a manifest.  It does not own Lean source parsing, elaboration, `.olean` loading, NDJSON parsing, root selection, unsafe-policy choices, generated-record audits, diagnostic continuation, telemetry, or persistent checked-declaration caches.

The rule-package model is a specification discipline.  A package may add expression behavior, declaration forms, environment metadata, typing rules, conversion rules, or reduction rules, but only as part of a named manifest choice.  A checker claim must name the manifest configuration and the adapter policy that translated external data into MPC declarations.

## Core API

MPC exposes a checked environment and a small set of judgment procedures.  Each procedure takes canonical MPC syntax and returns either a checked result or a structured error.  A higher-level tool may translate another format into this syntax, but that translation cannot add kernel rules.

| Operation | Meaning |
| --- | --- |
| `emptyEnv` | The empty checked environment. |
| `infer manifest env levels ctx expr` | Infer the type of `expr` under a universe context and term context. |
| `check manifest env levels ctx expr type` | Check that `expr` has `type` by conversion. |
| `defEq manifest env levels ctx left right` | Check definitional equality under the selected conversion rules. |
| `whnf manifest env levels expr` | Compute weak-head normal form under the selected reduction rules. |
| `normalize manifest env levels expr` | Normalize recursively after weak-head reduction. |
| `addDecl manifest env decl` | Check one declaration and return the extended environment. |
| `replay manifest env decls` | Fold `addDecl` over an ordered declaration script. |

`Declaration` is the only trusted input form for environment growth.  Generated constants belong to the declaration rule that creates them, not to an artifact record that repeats them.  If an export artifact contains generated constructors or recursors, the adapter audits those records against the environment produced by MPC.

## Syntax

MPC names are canonical strings.  An adapter that consumes Lean names must translate them injectively before constructing MPC declarations.  The core checker does not interpret private-name structure, macro scopes, quoted components, or module paths.

Universe levels are part of the trusted syntax.  They appear in sorts and in explicit constant universe arguments.  They have this grammar:

```text
level ::= 0
        | param name
        | succ level
        | max level level
        | imax level level
```

A level is closed when every `param` appears in the active universe context.  Level substitution replaces named parameters with supplied levels and traverses all constructors.  Level comparison normalizes `max` summands, reduces `imax u 0` to `0`, reduces `imax u v` to `max u v` when `v` is known to be a data universe, and preserves unresolved symbolic `imax` terms.

Expressions are post-elaboration kernel terms.  They contain no free variables, metavariables, binder annotations, or metadata.  They have this grammar:

```text
literal ::= nat n | string s
expr    ::= bvar i
          | Sort level
          | const name [level*]
          | lit literal
          | app expr expr
          | lam name expr expr
          | forall name expr expr
          | let name expr expr expr
          | proj structureName fieldIndex expr
```

Bound variables use de Bruijn indices.  Constants carry explicit universe arguments.  Binder names carry no typing meaning and matter only for diagnostics and exported display.

Declaration scripts are ordered MPC inputs.  The checker processes them by repeated calls to `addDecl`.  Scripts contain these entries:

| Declaration | Data | Environment effect |
| --- | --- | --- |
| Axiom | name, universe parameters, type | Adds an opaque assumption after the type infers a sort. |
| Definition | name, universe parameters, type, value | Adds a transparent constant after the type infers a sort and the value checks against it. |
| Opaque | name, universe parameters, type, value | Adds a checked constant whose value does not unfold during conversion. |
| Theorem | name, universe parameters, proposition type, proof | Adds a checked proof constant whose value does not unfold during conversion. |
| Simple inductive | type former, parameters, result universe, constructors | Adds the type former, constructors, and recursor family. |
| Indexed inductive | type former, parameters, indices, result universe, constructors with target indices | Adds the indexed type former, constructors, and indexed recursor. |
| Mutual inductive block | shared universe parameters and simple inductive members | Adds all type formers atomically, then constructors and one recursor per member. |
| Equality primitives | no additional data | Adds `Eq`, `Eq.refl`, `Eq.rec`, and `Eq.ndrec`. |
| Quotient primitives | no additional data | Adds `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, and `Quot.sound`. |

Projection functions are ordinary definitions whose bodies end in core projection expressions.  MPC does not need a special projection-declaration entry.  Structure metadata from Lean artifacts belongs to an adapter or audit layer unless a later MPC package gives that metadata a typing role.

## Environments and Contexts

An environment stores checked constants by name.  Each `ConstantInfo` records the constant name, universe parameters, type, optional value, and constant kind.  Constant kinds distinguish ordinary declarations, inductive type formers, constructors, recursors, equality primitives, and quotient primitives.

The environment preserves chronological entries and a name index.  Lookup uses the name index, and duplicate names are rejected.  A constant instantiation must provide exactly one level argument for each declared universe parameter, and every supplied level must be closed in the active universe context.

Runtime contexts store term binders innermost first.  De Bruijn index `0` refers to the head of the context, and index `i + 1` refers one binder farther out.  When lookup returns the type of index `i`, it lifts the stored binder type by `i + 1` so that the type lives in the current context.

Source telescopes are written outermost first.  Binding a telescope as dependent function types therefore introduces the first listed binder as the outermost binder and the last listed binder as the innermost binder.  Constructor fields and inductive parameters use this source order.

Simultaneous substitution is primitive.  Given source-order values `[v_0, ..., v_n]`, substitution replaces the innermost exposed variable with `v_n`, the next variable with `v_{n-1}`, and so on.  Under binders, the cutoff increases and inserted values are lifted to avoid capture.

## Base Typing

`Sort u` has type `Sort (succ u)` when `u` is closed.  A dependent function type `forall x : A, B` has sort `imax u v` when `A : Sort u` and `B : Sort v`.  If `Prop` is enabled and the codomain sort is `0`, the function sort is `0`.

A constant expression checks its level arguments for closure and arity, then instantiates the stored constant type.  Application reduces the inferred function type to weak-head normal form and requires a dependent-function type.  Lambda inference checks that the domain infers a sort, infers the body under the extended context, and returns the corresponding dependent-function type.

Checking a lambda against an expected dependent-function type is bidirectional.  MPC first weak-head reduces the expected type, compares the lambda domain with the expected domain, and checks the body against the expected body under the extended context.  Non-lambda checking infers a type and compares it with the expected type by definitional equality.

A `let` checks the declared type, checks the value, and continues with the value substituted into the body.  Zeta substitution is part of typing as well as conversion.  This rule keeps dependent uses of local definitions visible during checking.

Natural literals have type `Nat` when the literal package is enabled and the environment contains `Nat`, `Nat.zero`, and `Nat.succ`.  String literals have type `String` when string literals are enabled and the environment contains `String`.  Raw string literals are neutral in current MPC conversion.

## Conversion and Reduction

Weak-head normalization performs beta, zeta, delta for transparent definitions, projection reduction, inductive recursor reduction, equality-rec reduction, quotient-lift reduction, and selected primitive reductions.  Opaque constants and theorem constants do not unfold.  A recursor or primitive redex reduces only when the selected package is enabled and the environment metadata has the required shape.  After reducing a function position, weak-head normalization reprocesses the rebuilt application spine, because delta reduction may expose a partially applied eliminator or primitive whose remaining arguments were outside the unfolded head.

Definitional equality starts with alpha-equivalence.  If that fails, it compares weak-head normal forms structurally and recurses through full conversion on subterms.  If structural comparison fails, conversion may try structure eta, proof irrelevance, and function eta when their packages allow those rules.

Proof irrelevance applies when the left term has a proposition type and the right term has a type definitionally equal to it.  Function eta identifies a lambda with a function when the function has a dependent-function type and the lambda body is definitionally equal to applying that function to the bound variable.  Structure eta applies only to the projection fragment described below.

Natural-literal comparison identifies a raw numeric literal with the corresponding `Nat.zero` and `Nat.succ` constructor spine.  This comparison rule does not expand large literals during normalization.  Inductive recursor reduction may view raw natural literals as `Nat.zero` or `Nat.succ` when reducing the `Nat` recursor.

## Rule Packages

### Manifest

A manifest statically selects the rule packages available to the checker.  The base representation always contains the syntax for every package, but typing and reduction rules remain disabled until the manifest enables them.  `Manifest.validate` requires checked declaration admission before any environment-growth operation succeeds.

| Manifest field | Current modes |
| --- | --- |
| `declarations` | disabled, checked |
| `prop` | disabled, enabled |
| `literals` | none, nat, natAndString |
| `inductives` | none, simple, indexed |
| `inductiveBlocks` | disabled, mutual |
| `nestedContainers` | disabled, lean429 |
| `inductiveProp` | disabled, propOnly, largeElim |
| `equality` | disabled, primitive |
| `quotients` | disabled, primitive |
| `projections` | disabled, core |
| `primitiveReductions` | disabled, nat429 |
| `functionEta` | disabled, enabled |

### Declaration Admission

Axioms and definitions may declare universe parameters.  The declared type must infer a sort under those parameters, and a definition value must check against the declared type.  Transparent definitions unfold during conversion, while opaque declarations store checked values without unfolding them.

Theorem declarations require `Prop`.  The theorem type must infer sort `0`, and the proof value must check against that type.  The proof stays in the environment for auditing and does not unfold during conversion.

### Prop

`Prop` is `Sort 0`.  When enabled, propositions affect dependent-function sorts, theorem admission, proof irrelevance, and proposition-valued inductive declarations.  When disabled, any rule that requires `Prop` rejects rather than treating `Sort 0` as an ordinary data universe.

Proposition-valued inductives require the Prop package and the Prop-inductive package.  A proposition-valued recursor eliminates only to `Prop` unless the large-elimination eligibility rule admits a motive in a data universe.  Large elimination for Prop inductives is allowed only for conservative subsingleton shapes.

Large-elimination eligibility requires every constructor field to satisfy one of two checks.  A field is eligible when its type is a proposition.  In an indexed proposition-valued inductive, a field is also eligible when the field value is definitionally equal to a whole target-index argument of that constructor.

### Equality Primitives

The equality package adds four primitive constants.  `Eq.{u} (alpha : Sort u) (left right : alpha) : Prop` is the equality type.  `Eq.refl.{u} (alpha : Sort u) (value : alpha) : Eq alpha value value` is reflexivity.

`Eq.rec.{v,u}` is the dependent equality eliminator.  Its motive has type `(b : alpha) -> Eq alpha a b -> Sort v`, its minor premise has type `motive a (Eq.refl alpha a)`, and the result at endpoint `b` and proof `h` has type `motive b h`.  `Eq.ndrec.{v,u}` is the non-dependent proof-argument variant whose motive has type `alpha -> Sort v`.

Equality-rec reduction applies to `Eq.rec` and `Eq.ndrec`.  A redex with proof reducing to `Eq.refl` reduces to the minor premise at the reflexive endpoint.  A redex whose endpoints reduce to alpha-equivalent expressions also reduces to the minor premise, which captures the K-style reflexive endpoint case used by exported Lean proofs.

### Quotient Primitives

The quotient package requires `Prop` and the equality primitives.  It adds `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, and `Quot.sound` with explicit carrier and relation arguments.  The primitives enter as checked constants with primitive kinds, not as axioms with unchecked reduction behavior.

`Quot.{u} alpha r` forms a type in `Sort u` when `alpha : Sort u` and `r : alpha -> alpha -> Prop`.  `Quot.mk` injects a representative into the quotient, and `Quot.sound` proves equality of quotient elements whose representatives are related.  `Quot.ind` eliminates quotients into propositions.

`Quot.lift` eliminates a quotient into a non-dependent target.  The reduction rule maps `Quot.lift alpha r beta f resp (Quot.mk r' a)` to `f a` when the major premise weak-head reduces to a `Quot.mk` application.  For a well-typed redex, carrier and relation agreement follows from the type of the major premise; the reducer therefore follows Lean's primitive quotient reduction rather than imposing a separate syntactic relation comparison.  The rule preserves trailing applications after the reduced result.

### Literals

The literal package is a typing and conversion package.  Natural literals require `Nat`, `Nat.zero`, and `Nat.succ`, because conversion can view a numeric literal as a constructor spine.  String literals require `String` and otherwise remain neutral.

Natural literals are not primitive declarations.  They are expression forms whose type and conversion behavior depend on the manifest and the environment.  Full Lean string computation through characters, lists, byte arrays, or compiler primitives is outside the current literal package.

### Inductive Declarations

Simple inductives have universe parameters, a parameter telescope, a result universe, and constructors with dependent field telescopes.  Indexed inductives add an index telescope and require each constructor to declare the target-index terms for its result.  Mutual blocks group simple inductive declarations that share universe parameters and a parameter telescope.

Inductive admission is atomic at the block boundary.  MPC first checks headers, adds type formers to a provisional environment when mutual references need them, checks constructor fields and target shapes, then adds constructor constants and recursor constants.  Generated constructors and recursors must infer sorts before the environment accepts them.

A result universe must be closed under the declaration universe parameters.  A data-valued inductive result must live above `Prop`, and constructor-field universes must not exceed the declared result universe after parameters and earlier fields are available.  A proposition-valued result must follow the Prop-inductive and large-elimination rules above.

Sort-polymorphic inductive results require a written subsingleton rule before MPC may treat them as both `Prop` and data.  The accepted conservative shapes are empty families and one-constructor families with no data fields.  Any broader sort-polymorphic shape is a conformance obligation, not an implicit permission.

Strict positivity is checked in constructor field types.  A recursive occurrence may not appear in a function domain.  A recursive occurrence may appear in a function codomain or in a positive argument of an available covariant container.

Covariant-container information comes from two sources.  Under the Lean 4.29 nested-container mode, `Array`, `List`, and `Vec` have fixed covariance metadata when their declarations exist in the environment.  MPC also computes covariance flags for admitted simple and indexed inductive declarations by a fixed point, with indexed-family indices treated as non-positive arguments.

Nested recursor families are generated for simple root inductives when recursive fields pass through supported positive containers.  A helper target records a target expression, its universe levels, its parameter arguments, and any local telescope needed for indexed targets.  Helper target comparison uses alpha-equivalence of the target and binder types, and schema instantiation uses simultaneous substitution.

Recursive fields under local binders produce function-valued induction hypotheses.  Direct recursive occurrences headed by a block member use the corresponding block-member motive at the occurrence indices.  Nested recursive occurrences use the helper recursor target selected by the nested family.

A recursor redex reduces when the application contains the full recursor prefix and the major premise reduces to a constructor application for the selected target.  The reduction checks constructor field counts, target indices, and recursor metadata before applying a minor premise.  If the recursor result has trailing applications, reduction reapplies those arguments to the minor-premise result.

### Projections

Core projections have the expression form `proj S i target`.  The projection package requires `S` to name a simple one-constructor inductive declaration, and the inferred type of `target` must reduce to an application of `S` to its parameters.  The field type is the selected constructor field type with structure levels, parameters, and earlier fields substituted by the corresponding projections.

Projection reduction applies when the projection target reduces to the structure constructor.  The selected field is taken from the constructor arguments after the parameters.  The rule checks the constructor's parent inductive and field count before reducing.

Structure eta is a conversion fallback for the same projection fragment.  It compares a saturated constructor application with a non-constructor-headed value of the same inferred type by comparing every constructor field with the corresponding projection from the value.  The current eta rule applies only to data-valued, non-recursive, one-constructor simple inductives.

Projection from proposition-valued structures must not extract computational data.  A projection whose structure type lives in `Prop` is valid only when the selected field type is a proposition after substituting parameters and earlier projections.  This restriction follows the same boundary as large elimination from `Prop`.

### Primitive Nat Reductions

The primitive Nat package is versioned to Lean 4.29.  A primitive reduction applies only to the reserved name, the required declaration shape, and a transparent definition in the environment.  A user declaration with a matching printed name but the wrong kind, universe parameters, type, or value status does not receive the primitive rule.

| Constant | Required type | Reduction |
| --- | --- | --- |
| `Nat.add` | `Nat -> Nat -> Nat` | Reduces on the weak-head form of the right argument: `a + 0` becomes `a`, and `a + succ b` becomes `succ (Nat.add a b)`. |
| `Nat.mul` | `Nat -> Nat -> Nat` | Reduces when both arguments have numeric values, and reduces right zero to `0`. |
| `Nat.pow` | `Nat -> Nat -> Nat` | Reduces when both arguments have numeric values, and reduces right zero to `1`. |
| `Nat.sub` | `Nat -> Nat -> Nat` | Reduces when both arguments have numeric values, and reduces right zero to the left argument. |
| `Nat.beq` | `Nat -> Nat -> Bool` | Reduces numeric comparisons to `Bool.true` or `Bool.false`. |
| `Nat.ble` | `Nat -> Nat -> Bool` | Reduces numeric comparisons to `Bool.true` or `Bool.false`. |

Numeric values include raw natural literals and constructor spines made from `Nat.zero` and `Nat.succ`.  Boolean primitive results require `Bool.true` and `Bool.false` to be nullary constructors of `Bool`.  The package does not include `Nat.div`, `Nat.mod`, `Nat.gcd`, string primitives, byte-array primitives, fixed-width integer primitives, or floating-point primitives.

### Function Eta

Function eta is a conversion package.  It compares a lambda with another term after weak-head reducing the lambda side.  The other term must infer a dependent-function type whose domain is definitionally equal to the lambda domain, and the lambda body must be definitionally equal to the other term applied to the bound variable.

The rule runs in both orientations after structural comparison and the other enabled conversion fallbacks.  It uses the same context and universe context as ordinary conversion.  It does not create a new expression form or declaration form.

## LeanCore429 Configuration

`MPC.Configs.LeanCore429` is the current broad MPC configuration for Lean 4.29-oriented replay.  It starts from the PoC manifest and enables natural and string literals, indexed inductives, mutual inductive blocks, Lean 4.29 nested containers, Prop inductives with large elimination, equality primitives, quotient primitives, core projections, Lean 4.29 natural primitive reductions, and function eta.  It remains a manifest choice over MPC rules rather than an adapter policy.

The small PoC configurations are manifest variants used to test package boundaries.  Each one enables a narrow package slice such as equality, quotients, projections, primitive Nat reduction, function eta, simple Prop inductives, indexed inductives, indexed Prop inductives, or indexed Prop large elimination.  These configurations help keep package interactions explicit while the broad LeanCore429 manifest remains the target for artifact-oriented replay.

## External Boundaries

An NDJSON or `.olean` checker is an adapter over MPC.  The adapter parses artifact syntax, translates names, levels, expressions, and declaration records into canonical MPC declarations, calls `replay`, and audits redundant generated records against the environment.  Acceptance of an external artifact depends on both the MPC manifest and the adapter policy.

Generated constructor and recursor records are audit data.  MPC generates those constants from inductive declarations and stores their metadata in the environment.  An adapter may reject an artifact when its redundant generated record disagrees with MPC, but that audit does not add a kernel rule.

Unsafe declarations, partial declarations, source-recursion metadata, equation-compiler metadata, environment extensions, imported-module bases, and trusted assumptions belong to adapter policy.  The policy may reject, skip, or assume external data only under a named checker mode.  MPC sees only checked environments and canonical declarations.

The SQLite checked-declaration cache is outside MPC.  A cache may store checked environments and declaration-content keys, then reuse them before calling MPC on cache misses.  Cache reuse is valid only when it reconstructs the same MPC environment entries and never changes typing, conversion, declaration admission, or generated-record audit rules.

## Conformance Obligations

This specification contains conformance obligations that the current MPC code must audit or implement.  Inductive universe bounds, sort-polymorphic inductive restrictions, and Prop projection restrictions are kernel-soundness obligations.  MPC code must enforce these rules before the corresponding manifest can support arbitrary Lean 4.29 artifacts.

The checker must also classify resource failures.  Normalization, conversion, and replay may need fuel, sharing, or explicit limits for large artifacts.  Exhausting such a limit should produce a checker result rather than host nontermination or a stack failure.

Adding a rule package requires a written rule, owned environment metadata, reduction and typing tests, and at least one artifact-shaped test when the rule targets Lean replay.  Primitive reductions require source evidence for the Lean version named by the package.  Adapter work cannot substitute for a missing MPC rule.
