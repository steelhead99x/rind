module

public import Lean.ToExpr

/-!
# Sets of registers as bit masks

The taint analyses (`VG.Taint`) are evaluated by the kernel, which is slow at
lists of registers: every membership test compares registers one at a time,
and removing a register rebuilds the list. A `RegSet` is a `Nat` whose bit
`idx r` says whether `r` is in the set, so that the kernel evaluates every
set operation with a few native `Nat` bitwise operations. They are written
with the `Nat` functions themselves (`Nat.lor`, not `|||`; `Nat.beq`, not
`Nat.testBit`, whose `!=` goes through `Decidable`), which spares the kernel
unfolding the instances every time; the lemmas state them with the usual
operations.
-/

@[expose] public section

namespace VG

/-- Registers numbered injectively, for `RegSet`. -/
class RegIdx (R : Type) where
  idx : R → Nat
  idx_inj : ∀ {a b : R}, idx a = idx b → a = b

/-- A set of registers: bit `RegIdx.idx r` of `bits` says whether `r` is in it. -/
structure RegSet (R : Type) where
  bits : Nat
  deriving DecidableEq

namespace RegSet

variable {R : Type} [RegIdx R]

instance [Lean.ToExpr R] : Lean.ToExpr (RegSet R) where
  toExpr s := Lean.mkApp2 (.const ``RegSet.mk []) (Lean.toTypeExpr R) (Lean.toExpr s.bits)
  toTypeExpr := Lean.mkApp (.const ``RegSet []) (Lean.toTypeExpr R)

def bit (r : R) : Nat := Nat.pow 2 (RegIdx.idx r)

def mem (s : RegSet R) (r : R) : Bool := !Nat.beq (Nat.land 1 (Nat.shiftRight s.bits (RegIdx.idx r))) 0

instance : Membership R (RegSet R) := ⟨fun s r => s.mem r = true⟩

instance (r : R) (s : RegSet R) : Decidable (r ∈ s) := inferInstanceAs (Decidable (s.mem r = true))

def empty : RegSet R := ⟨0⟩

def insert (s : RegSet R) (r : R) : RegSet R := ⟨Nat.lor s.bits (bit r)⟩

def erase (s : RegSet R) (r : R) : RegSet R := ⟨Nat.xor s.bits (Nat.land s.bits (bit r))⟩

def inter (a b : RegSet R) : RegSet R := ⟨Nat.land a.bits b.bits⟩

/-- Every register of `a` is in `b`. -/
def subset (a b : RegSet R) : Bool := Nat.beq (Nat.land a.bits b.bits) a.bits

def ofList (rs : List R) : RegSet R := rs.foldr (fun r s => s.insert r) empty

/-- `k s`, with the set `s` evaluated: what `k` is given has a numeral for its
bits, whatever term `s` is, so that two sets that are equal are the same term
(see "An analysis the kernel finds again" in the `proof-performance` skill).
The kernel evaluates `Nat.succ` of a numeral to a numeral, and a recursor on
that one hands over its predecessor, a numeral. -/
def force {α : Type} (s : RegSet R) (k : RegSet R → α) : α :=
  Nat.casesOn (motive := fun _ => α) (Nat.succ s.bits) (k s) (fun n => k ⟨n⟩)

omit [RegIdx R] in
theorem force_eq {α : Type} (s : RegSet R) (k : RegSet R → α) : s.force k = k s := rfl

instance : Coe (List R) (RegSet R) := ⟨ofList⟩

theorem mem_iff {s : RegSet R} {r : R} : r ∈ s ↔ s.bits.testBit (RegIdx.idx r) = true := by
  show s.mem r = true ↔ _
  rw [mem, Nat.testBit, bne, Bool.not_eq_true', Bool.not_eq_true', Bool.eq_false_iff, Bool.eq_false_iff,
    Ne, Ne, Nat.beq_eq, beq_iff_eq]
  rfl

theorem bit_eq (r : R) : bit r = 2 ^ RegIdx.idx r := rfl

theorem insert_bits (s : RegSet R) (r : R) : (s.insert r).bits = s.bits ||| bit r := rfl

theorem erase_bits (s : RegSet R) (r : R) : (s.erase r).bits = s.bits ^^^ (s.bits &&& bit r) := rfl

omit [RegIdx R] in
theorem inter_bits (a b : RegSet R) : (a.inter b).bits = a.bits &&& b.bits := rfl

omit [RegIdx R] in
theorem subset_eq (a b : RegSet R) : a.subset b = ((a.bits &&& b.bits) == a.bits) := by
  rw [subset, Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]; rfl

theorem testBit_bit {r : R} {i : Nat} : (bit r).testBit i = decide (RegIdx.idx r = i) := by
  rw [bit_eq, Nat.testBit_two_pow]

@[simp] theorem not_mem_empty (r : R) : ¬r ∈ (empty : RegSet R) := by
  rw [mem_iff]; simp [empty]

@[simp] theorem mem_insert {s : RegSet R} {d r : R} : r ∈ s.insert d ↔ r = d ∨ r ∈ s := by
  rw [mem_iff, mem_iff, insert_bits, Nat.testBit_or, testBit_bit, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (RegIdx.idx_inj h.symm)
  · rintro (rfl | h)
    · exact Or.inr rfl
    · exact Or.inl h

@[simp] theorem mem_erase {s : RegSet R} {d r : R} : r ∈ s.erase d ↔ r ≠ d ∧ r ∈ s := by
  rw [mem_iff, mem_iff, erase_bits, Nat.testBit_xor, Nat.testBit_and, testBit_bit]
  by_cases e : RegIdx.idx d = RegIdx.idx r
  · have := RegIdx.idx_inj e; subst this
    cases s.bits.testBit (RegIdx.idx d) <;> simp
  · have : r ≠ d := fun h => e (h ▸ rfl)
    cases s.bits.testBit (RegIdx.idx r) <;> simp [e, this]

@[simp] theorem mem_inter {a b : RegSet R} {r : R} : r ∈ a.inter b ↔ r ∈ a ∧ r ∈ b := by
  rw [mem_iff, mem_iff, mem_iff, inter_bits, Nat.testBit_and, Bool.and_eq_true]

theorem mem_of_subset {a b : RegSet R} (h : a.subset b = true) {r : R} (hr : r ∈ a) : r ∈ b := by
  rw [subset_eq, beq_iff_eq] at h
  rw [mem_iff, ← h, Nat.testBit_and, Bool.and_eq_true] at hr
  exact mem_iff.mpr hr.2

@[simp] theorem mem_ofList {rs : List R} {r : R} : r ∈ ofList rs ↔ r ∈ rs := by
  induction rs with
  | nil => simp [ofList]
  | cons d rs ih => simp only [ofList, List.foldr_cons, mem_insert, List.mem_cons] at ih ⊢; rw [ih]

end RegSet

end VG
