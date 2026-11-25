import Rind.Portable.Keccak
open Aeneas Aeneas.Std Result rind.spec

/-!
# Keccak-f[1600]'s dispatch on the portable backend

What the routines rind's sponge calls compute, from `Rind.Portable.Keccak`:
`keccak_f1600_spec`, one state; `keccak4_f1600_spec`, four;
`keccak_nof4_f1600_spec`, the first `N` of four, over FIPS 202's round
constants `mid::sha3::RC`. The sponge's proof, `Rind.Portable.Sha3`, which
`admin/prove` writes from x86_64's, uses these names, which
`Rind.X86_64.KeccakDispatch` proves for x86_64. There is no CPU dispatch here.
-/

namespace rind.portable

/-- rind's SHA-3 runs here: its entry guard and the debug build's check that
one is held pass. Neither reads an input. -/
def RunsSha3 : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ low.entry.Entry.assert_held = ok ()

theorem sha3_new_secret_spec (h : RunsSha3) : low.entry.Entry.new_secret ⦃ _ => True ⦄ := by
  obtain ⟨⟨e, he⟩, -⟩ := h
  simp [he]

theorem sha3_assert_held_spec (h : RunsSha3) : low.entry.Entry.assert_held ⦃ _ => True ⦄ := by
  obtain ⟨-, he⟩ := h
  simp [he]

theorem rc_bv : mid.sha3.RC.val.map (·.bv) = keccakRoundConstants := by
  simp [mid.sha3.RC, keccakRoundConstants]

/-- `keccak_f1600_spec`: one state. -/
theorem keccak_f1600_spec (_h : RunsSha3) (a : Std.Array U64 25#usize) :
    low.portable.keccak.sha3_keccak_f1600 a mid.sha3.RC ⦃ r =>
      lanes r = keccak 24 (lanes a) ⦄ :=
  keccak_f1600_rc_spec a _ rc_bv

/-- `keccak4_f1600_spec`: four states. -/
theorem keccak4_f1600_spec (_h : RunsSha3) (a : Std.Array (Std.Array U64 25#usize) 4#usize) :
    low.portable.keccak.sha3_keccak4_f1600 a mid.sha3.RC ⦃ r =>
      states r = (states a).map (keccak 24) ⦄ :=
  keccak4_f1600_rc_spec a _ rc_bv

/-- `keccak_nof4_f1600_spec`: the first `N` of four states. -/
theorem keccak_nof4_f1600_spec (_h : RunsSha3) (N : Usize) (hN : 1 ≤ N.val ∧ N.val ≤ 4)
    (a : Std.Array (Std.Array U64 25#usize) 4#usize) :
    low.portable.keccak.sha3_keccak_nof4_f1600 N a mid.sha3.RC ⦃ r =>
      (states r).take N.val = ((states a).take N.val).map (keccak 24) ⦄ :=
  keccak_nof4_f1600_rc_spec N hN.2 a _ rc_bv

end rind.portable
