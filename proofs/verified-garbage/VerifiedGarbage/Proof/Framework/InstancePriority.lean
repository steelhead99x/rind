module

/-!
# Instance search without detours through Mathlib's hierarchies

Untrusted: this only changes how proofs are found.

With Mathlib imported, a `Decidable` instance for a bounded quantifier over a
list or for membership in a list, the most common propositions proofs decide
(`∀ r ∈ regs, r ∈ clobbered`, `r ∉ [.rax, .rdx]`, `omega`'s
`Coeffs.isZero xs`, that is `∀ x, x ∈ xs → x = 0`), took 5–15 ms to find:
four hundredths of the whole build. The search went the long way twice:

* `∀ x, x ∈ xs → p x` tried Mathlib's instances for quantifiers over finite
  types, finite sets and multisets (which unify with any `∀`) before core's
  `List.decidableBAll`. It is tried first here.
* Membership needs `BEq α` and `LawfulBEq α`, and core's instances deriving
  them from an order (`Std.PreorderPackage`, `Std.LawfulBEqOrd`, …), tried
  first since they are newer, searched Mathlib's whole order hierarchy
  (lattices, Boolean algebras, …) for every register type before failing.
  They are tried last here.

The search finds the same instances as before, so every term (and what the
kernel evaluates) is unchanged; this includes `omega`'s, `List.decidableBAll`
deciding each `x = 0` by `Int.instDecidableEq`.
-/

@[expose] public section

attribute [instance low] Std.PreorderPackage.toBEq Std.LawfulBEqOrd.lawfulBEq
  Std.instLawfulBEqOfLawfulOrderBEqOfIsPartialOrder

attribute [instance high] List.decidableBAll
