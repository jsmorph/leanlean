# Lean 4.29.1 Primitive Reduction Inventory

This inventory records source evidence for kernel-overridden computation in Lean 4.29.1.  It is not an admission list.  A constant enters local conversion only after `spec.md` states the rule, the implementation checks the declaration shape, and a generated export test forces the rule through `leanlean-check-export`.

The source paths below refer to the Lean toolchain used by this repository: `~/.elan/toolchains/leanprover--lean4---v4.29.1/src/lean`.  Line numbers are evidence for this toolchain revision, not stable identifiers.  Future Lean upgrades must repeat this inventory against the new source tree.

## Admitted Rules

| Constant | Source evidence | Local status |
| --- | --- | --- |
| `Nat.add` | `Init/Prelude.lean:1731` says the function is overridden in the kernel and compiler.  The declaration has `@[extern "lean_nat_add", implicit_reducible]`. | Implemented as a specified primitive reduction. |
| `Nat.mul` | `Init/Prelude.lean:1750` says the function is overridden in the kernel and compiler.  The declaration has `@[extern "lean_nat_mul", implicit_reducible]`. | Implemented as a specified primitive reduction. |
| `Nat.pow` | `Init/Prelude.lean:1765` says the function is overridden in the kernel and compiler.  The declaration has `@[extern "lean_nat_pow"]`. | Implemented as a specified primitive reduction. |
| `Nat.beq` | `Init/Prelude.lean:1779` says the function is overridden in the kernel and compiler.  The declaration has `@[extern "lean_nat_dec_eq"]`. | Implemented as a specified primitive reduction. |
| `Nat.ble` | `Init/Prelude.lean:1844` says the function is overridden in the kernel and compiler.  The declaration has `@[extern "lean_nat_dec_le"]`. | Implemented as a specified primitive reduction. |

## Source-Backed Candidates

| Constant | Source evidence | Work before admission |
| --- | --- | --- |
| `Nat.decEq` | `Init/Prelude.lean:1824` says the decision procedure is overridden in the kernel and compiler.  The declaration has `@[reducible, extern "lean_nat_dec_eq"]`. | Specify how the checker constructs the `Decidable` result and its proof payload, or show that ordinary reduction through `Nat.beq` suffices for all accepted exports. |
| `Nat.decLe` | `Init/Prelude.lean:2049` gives the declaration `@[extern "lean_nat_dec_le"]`.  The logical model builds a `Decidable` value from `Nat.ble`. | Decide whether this is a kernel conversion rule or only an external runtime entry point.  If admitted, specify the `Decidable` result and proof payload. |
| `Nat.decLt` | `Init/Prelude.lean:2063` gives the declaration `@[extern "lean_nat_dec_lt"]`.  The logical model delegates to `Nat.decLe (succ n) m`. | Decide whether this is a kernel conversion rule or only an external runtime entry point.  If admitted, specify the `Decidable` result and proof payload. |
| `Nat.sub` | `Init/Prelude.lean:2075` says the definition is overridden in the kernel and compiler.  The declaration has `@[extern "lean_nat_sub", implicit_reducible]`. | Add a truncated-subtraction rule for numeric arguments, with declaration-shape checks and export coverage. |
| `Nat.blt` | `Init/Data/Nat/Basic.lean:86` says the function is overridden in the kernel and compiler.  The current source defines it as `ble a.succ b` with `@[expose]`. | Check whether Lean's kernel gives `Nat.blt` a separate reduction rule or obtains the behavior through unfolding and `Nat.ble`. |
| `Nat.gcd` | `Init/Data/Nat/Gcd.lean:25` says the Euclidean implementation is overridden in the kernel and compiler.  The declaration has `@[extern "lean_nat_gcd"]`. | Add a numeric GCD rule only after specifying interaction with `Nat.mod`, recursion, and exported proof terms that depend on closed GCD computation. |

## Runtime Externs Without Kernel Reduction Evidence

`Nat.div`, `Nat.modCore`, and the wrapper `Nat.mod` have runtime externs in `Init/Prelude.lean`, but the surrounding comments say runtime override rather than kernel override.  They remain outside local conversion unless a later source audit finds kernel evidence.  The same rule applies to array, byte-array, string, IO, and fixed-width integer externs whose comments describe runtime or compiler behavior without saying that the kernel reduces them.

`Float` and `Float32` declarations are explicit negative evidence.  Their source comments repeatedly state that the functions do not reduce in the kernel.  The checker must not add floating-point conversion rules without new source evidence and a separate soundness account.
