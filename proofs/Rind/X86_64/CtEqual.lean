import Rind.X86_64.Funs
open Aeneas Aeneas.Std Result

/-!
# The constant-time compares on x86_64

`low::generic::ct_equal` compares two slices through `ct_compare_16`, for
16-byte ones, or `ct_compare_bytes`. Their `asm!` blocks are proven in HOL
Light, of the bytes rind's build emits, in `proofs/hol-light/x86_64/`, and
each axiom here restates one of those theorems, at rind's commit, about the
opaque Rust wrapper around the block. The restatement, and that the wrapper
passes the arguments the theorem names, are trusted. Each file's `_SAFE`
theorem proves the block's loads and branches depend only on the
addresses and lengths, which no Lean theorem states. `admin/prove` writes
the aarch64 and armv7 proofs from this file by renaming the target.
-/

namespace rind.x86_64

/-- `CT_COMPARE_16_CORRECT`, in `proofs/hol-light/x86_64/ct_compare_16.ml`:
the wrapper loads each block as little-endian words, and the block's result
is zero exactly when each pair of words is equal. -/
@[step]
axiom ct_compare_16_spec (a b : Std.Array U8 16#usize) :
    low.x86_64.cpu.ct_compare_16 a b ⦃ r => (r.val = 0 ↔ a.val = b.val) ⦄

/-- `CT_COMPARE_BYTES_CORRECT`, in `proofs/hol-light/x86_64/ct_compare_bytes.ml`,
over the shorter slice's length, whose result the wrapper returns as its low
byte: zero exactly when the bytes are equal. -/
@[step]
axiom ct_compare_bytes_spec (a b : Slice U8) :
    low.x86_64.cpu.ct_compare_bytes a b ⦃ r =>
      (r.val = 0 ↔ a.val.take (min a.length b.length) = b.val.take (min a.length b.length)) ⦄

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

end rind.x86_64
