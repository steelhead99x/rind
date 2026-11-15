import Rind.Portable.Funs
import Rind.Bytes
open Aeneas Aeneas.Std Result

/-!
# The constant-time compares on the portable backend

`low::generic::ct_equal` compares two slices through `ct_compare_16`, for
16-byte ones, or `ct_compare_bytes`. They are Rust here, which
`Rind.Portable.Compare` models, so this proves what x86_64 and aarch64 take
from HOL Light as axioms, and adds none.
-/

namespace rind.portable

theorem val_eq_zero {ty : UScalarTy} (x : UScalar ty) : x.val = 0 ↔ x.bv = 0#_ := by
  rw [UScalar.val, BitVec.toNat_eq, BitVec.toNat_zero]

theorem or_eq_zero (x y : U8) : (x ||| y).val = 0 ↔ x.val = 0 ∧ y.val = 0 := by
  rw [val_eq_zero, val_eq_zero, val_eq_zero, UScalar.bv_or]
  exact BitVec.or_eq_zero_iff

theorem xor_eq_zero (x y : U8) : (x ^^^ y).val = 0 ↔ x = y := by
  rw [val_eq_zero, UScalar.bv_xor, U8.eq_equiv_bv_eq]
  exact BitVec.xor_eq_zero_iff

/-- Base-256 digits of one length that read as the same number are the same. -/
theorem ofDigits_inj : ∀ {l1 l2 : List Nat}, l1.length = l2.length →
    (∀ d ∈ l1, d < 256) → (∀ d ∈ l2, d < 256) →
    Nat.ofDigits 256 l1 = Nat.ofDigits 256 l2 → l1 = l2
  | [], [], _, _, _, _ => rfl
  | a :: xs, b :: ys, hl, h1, h2, h => by
    simp only [Nat.ofDigits_cons] at h
    have ha := h1 a (by simp)
    have hb := h2 b (by simp)
    have e : a = b := by omega
    subst e
    rw [ofDigits_inj (l1 := xs) (l2 := ys) (by simpa using hl) (fun d hd => h1 d (by simp [hd]))
      (fun d hd => h2 d (by simp [hd])) (by omega)]

/-- Bytes of one length that read as the same little-endian number are the
same. -/
theorem fromLEBytes_inj {a b : List U8} (hl : a.length = b.length)
    (h : (BitVec.fromLEBytes (a.map (·.bv))).toNat = (BitVec.fromLEBytes (b.map (·.bv))).toNat) :
    a = b := by
  rw [spec.toNat_fromLEBytes, spec.toNat_fromLEBytes, List.map_map, List.map_map] at h
  have := ofDigits_inj (by simpa using hl) (by simp; intro u _; scalar_tac)
    (by simp; intro u _; scalar_tac) h
  exact List.map_injective_iff.2 (fun x y hxy => by
    rw [U8.eq_equiv_bv_eq]; exact BitVec.eq_of_toNat_eq hxy) this

/-- A value of twice `n` bits is zero exactly when both its halves are. -/
theorem halves_eq_zero {n : Nat} (x : BitVec (2 * n)) :
    x.setWidth n = 0#n ∧ (x >>> n).setWidth n = 0#n ↔ x = 0#(2 * n) := by
  have hx := x.isLt
  simp only [BitVec.toNat_eq, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_zero,
    Nat.shiftRight_eq_div_pow]
  have hp : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [two_mul, Nat.pow_add]
  rw [hp] at hx
  constructor
  · rintro ⟨h1, h2⟩
    rw [Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hx)] at h2
    rw [← Nat.div_add_mod x.toNat (2 ^ n), h1, h2]; simp
  · intro h; simp [h]

/-- `ct_compare_16`'s fold of 128 bits into 32 is zero exactly when they are. -/
theorem fold_eq_zero (d : BitVec 128) :
    ((d.setWidth 64 ||| (d >>> 64).setWidth 64).setWidth 32 |||
      ((d.setWidth 64 ||| (d >>> 64).setWidth 64) >>> 32).setWidth 32) = 0#32 ↔ d = 0#128 := by
  rw [BitVec.or_eq_zero_iff, halves_eq_zero (n := 32), BitVec.or_eq_zero_iff,
    halves_eq_zero (n := 64) d]

theorem foldl_or_eq_zero (l : List U8) (acc : U8) :
    (l.foldl (· ||| ·) acc).val = 0 ↔ acc.val = 0 ∧ ∀ x ∈ l, x.val = 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, or_eq_zero]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem zipWith_xor_eq_zero (a b : List U8) :
    (∀ x ∈ List.zipWith (· ^^^ ·) a b, x.val = 0) ↔
      a.take (min a.length b.length) = b.take (min a.length b.length) := by
  induction a generalizing b with
  | nil => simp
  | cons x a ih =>
    cases b with
    | nil => simp
    | cons y b =>
      simp only [List.zipWith_cons_cons, List.mem_cons, forall_eq_or_imp, ih, xor_eq_zero,
        List.length_cons, Nat.add_min_add_right, List.take_succ_cons, List.cons.injEq]

/-- `ct_compare_16` returns zero exactly when the blocks are equal. -/
@[step]
theorem ct_compare_16_spec (a b : Std.Array U8 16#usize) :
    low.portable.cpu.ct_compare_16 a b ⦃ r => (r.val = 0 ↔ a.val = b.val) ⦄ := by
  unfold low.portable.cpu.ct_compare_16
  simp only [WP.spec_ok]
  have la : a.val.length = 16 := a.property
  have lb : b.val.length = 16 := b.property
  have hw : 32 ≤ UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
  have hxl := (BitVec.fromLEBytes (a.val.map (·.bv))).isLt
  have hyl := (BitVec.fromLEBytes (b.val.map (·.bv))).isLt
  simp only [List.length_map, la, lb] at hxl hyl
  have hxy : (BitVec.fromLEBytes (a.val.map (·.bv))).setWidth 128 =
      (BitVec.fromLEBytes (b.val.map (·.bv))).setWidth 128 ↔ a.val = b.val := by
    constructor
    · intro h
      apply fromLEBytes_inj (by rw [la, lb])
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hxl,
        Nat.mod_eq_of_lt hyl] at this
    · intro h
      obtain rfl : a = b := (Array.eq_iff a b).2 h
      rfl
  generalize hd : (BitVec.fromLEBytes (a.val.map (·.bv))).setWidth 128 ^^^
    (BitVec.fromLEBytes (b.val.map (·.bv))).setWidth 128 = d
  simp only [UScalar.val, BitVec.toNat_setWidth]
  generalize hs : ((d.setWidth 64 ||| (d >>> 64).setWidth 64).setWidth 32 |||
      ((d.setWidth 64 ||| (d >>> 64).setWidth 64) >>> 32).setWidth 32) = s
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by decide) hw)),
    show (0 : Nat) = (0#32).toNat from rfl, ← BitVec.toNat_eq, ← hs, fold_eq_zero, ← hd, BitVec.xor_eq_zero_iff, hxy]

/-- `ct_compare_bytes` returns zero exactly when the bytes up to the shorter
length are equal. -/
@[step]
theorem ct_compare_bytes_spec (a b : Slice U8) :
    low.portable.cpu.ct_compare_bytes a b ⦃ r =>
      (r.val = 0 ↔ a.val.take (min a.length b.length) = b.val.take (min a.length b.length)) ⦄ := by
  unfold low.portable.cpu.ct_compare_bytes
  simp only [WP.spec_ok, foldl_or_eq_zero, Slice.length]
  rw [← zipWith_xor_eq_zero]
  simp

theorem ct_equal_diff (d : Usize) (p : Prop) [Decidable p] (hd : d.val = 0 ↔ p) :
    decide (d = 0#usize) = decide p := by
  rw [decide_eq_decide, ← hd]
  constructor
  · intro h; rw [h]; rfl
  · intro h; scalar_tac

/-- `ct_equal` returns whether its slices are equal. -/
theorem ct_equal_spec (h : low.entry.Entry.assert_held = ok ()) (x y : Slice U8) :
    low.generic.ct_equal.ct_equal x y ⦃ b => b = decide (x.val = y.val) ⦄ := by
  unfold low.generic.ct_equal.ct_equal
  rw [h, bind_ok]
  have hx : (Slice.len x).val = x.length := Slice.len_val x
  have hy : (Slice.len y).val = y.length := Slice.len_val y
  by_cases hl : x.length = y.length
  · have hne : (Slice.len x != Slice.len y) = false := by
      simp only [bne_eq_false_iff_eq]; exact UScalar.eq_of_val_eq (by rw [hx, hy, hl])
    simp only [hne, Bool.false_eq_true, ite_false]
    have hbytes : ∀ r : U8, (r.val = 0 ↔ x.val.take (min x.length y.length) =
        y.val.take (min x.length y.length)) → (r.val = 0 ↔ x.val = y.val) := by
      intro r hr
      rw [hr, ← hl, Nat.min_self, List.take_of_length_le (by simp [Slice.length]),
        List.take_of_length_le (by simp [Slice.length, hl])]
    step as ⟨r⟩
    step as ⟨r1⟩
    split
    · rename_i a1 ha1
      split
      · rename_i b1 hb1
        step as ⟨d, hd⟩
        obtain ⟨ha, -⟩ := ha1
        obtain ⟨hb, -⟩ := hb1
        apply ct_equal_diff
        rw [hd, ha, hb]
      · step as ⟨c, hc⟩
        apply ct_equal_diff
        rw [← hbytes c hc]
        rw [core.convert.num.FromUsizeU8.from_val_eq]
    · step as ⟨c, hc⟩
      apply ct_equal_diff
      rw [← hbytes c hc]
      rw [core.convert.num.FromUsizeU8.from_val_eq]
  · have hne : (Slice.len x != Slice.len y) = true := by
      simp only [bne_iff_ne, ne_eq]; intro he; apply hl; rw [← hx, ← hy, he]
    simp only [hne, ite_true, WP.spec_ok]
    symm; rw [decide_eq_false_iff_not]
    intro he; apply hl; simp [Slice.length, he]

end rind.portable
