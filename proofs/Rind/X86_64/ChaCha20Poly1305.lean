import Rind.X86_64.ChaCha20Poly1305Api
import Rind.X86_64.CtEqual
import Rind.X86_64.VgChaCha20Poly1305
open Aeneas Aeneas.Std Result rind.spec

/-!
# ChaCha20-Poly1305's one pass on x86_64

`Rind.X86_64.ChaCha20Poly1305Api` proves the AEAD API's ChaCha20-Poly1305 and
XChaCha20-Poly1305 from `Seals` and `Opens`, that the one pass computes RFC
8439's AEAD. `seals` and `opens` prove those on CPUs that run a one pass,
which `RunsChaCha20Poly1305` states. CPUs that pass
`HaveIfmaForVgChaCha20Poly1305`'s check run pyca/verified-garbage's IFMA one
pass, whose theorems `Rind.X86_64.VgChaCha20Poly1305` imports as axioms, so on
them the theorems here earn the ✓. CPUs that fail it and pass `HaveSse41`'s
run aws-lc's one-pass routines, which the theorems take as the hypothesis
`OnePass`: that they compute RFC 8439's ciphertext and tag. No proof covers
those routines yet, so on those CPUs no theorem here earns the ✓. CPUs that
fail both run the separate passes, which no theorem here covers yet.
-/

namespace rind.x86_64

/-- aws-lc's one-pass routines, behind `one_pass`, compute RFC 8439's AEAD for
a message of at most 2^38 - 64 bytes, as many as its 32-bit block counter
covers from block 1: sealing leaves the ChaCha20 ciphertext in place and
returns the Poly1305 tag over the AAD and it, and opening leaves the
plaintext and returns the tag over the AAD and the ciphertext it was given.
Either half, AVX2 or SSE4.1, computes the same. -/
def OnePass : Prop :=
  ∀ sse41 avx2 (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8),
    inout.length ≤ 2 ^ 38 - 64 →
    low.x86_64.chacha20poly1305.one_pass sse41 avx2 key nonce aad inout true ⦃ r =>
      r.2.length = inout.length ∧
      (bvs r.2.val, bvs r.1.val) =
        chacha20poly1305.seal (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) ⦄ ∧
    low.x86_64.chacha20poly1305.one_pass sse41 avx2 key nonce aad inout false ⦃ r =>
      r.2.length = inout.length ∧
      bvs r.2.val = chacha20.encrypt (bvs key.val) 1 (bvs nonce.val) (bvs inout.val) ∧
      bvs r.1.val = poly1305.mac (chacha20poly1305.otk (bvs key.val) (bvs nonce.val))
        (chacha20poly1305.macData (bvs aad.val) (bvs inout.val)) ⦄

/-- rind runs a one pass a theorem covers on this CPU: its entry guard
passes and holds, and of its CPU-feature checks, either
`HaveIfmaForVgChaCha20Poly1305`'s passes and `HaveSse41`'s, which the
dispatch reads first, returns, so it runs pyca/verified-garbage's one pass,
or the first fails and `HaveSse41`'s passes, so it runs aws-lc's, and
`OnePass` holds. None reads an input. -/
def RunsChaCha20Poly1305 : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ low.entry.Entry.assert_held = ok () ∧
  ((∃ t, low.x86_64.cpu.HaveIfmaForVgChaCha20Poly1305.check = ok (some t)) ∧
      (∃ s, low.x86_64.cpu.HaveSse41.check = ok s) ∨
    low.x86_64.cpu.HaveIfmaForVgChaCha20Poly1305.check = ok none ∧
      (∃ s, low.x86_64.cpu.HaveSse41.check = ok (some s)) ∧
      (∃ a, low.x86_64.cpu.HaveAvx2.check = ok a) ∧ OnePass)

/-! ## The one-pass seal and open, `low::x86_64::chacha20poly1305` -/

theorem chacha20_poly1305_seal_spec (h : RunsChaCha20Poly1305) (key : Std.Array U8 32#usize)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (hl : inout.length ≤ 2 ^ 38 - 64) :
    low.x86_64.chacha20poly1305.seal key nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧
      (bvs r.2.val, bvs r.1.val) =
        chacha20poly1305.seal (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) ⦄ := by
  unfold low.x86_64.chacha20poly1305.seal
  obtain ⟨-, -, ⟨⟨t, hi⟩, ⟨s, hs⟩⟩ | ⟨hi, ⟨s, hs⟩, ⟨a, ha⟩, hop⟩⟩ := h
  · simp only [hi, hs, bind_ok]
    exact seal_ifma_spec t key nonce aad inout
  · simp only [hi, hs, ha, bind_ok]
    exact (hop s a key nonce aad inout hl).1

/-- The one-pass open returns whether RFC 8439's tag is `tag`, leaving the
plaintext in place if it is. Where it is not, VG's leaves zeros and aws-lc's
the plaintext, which `open_tail_spec` zeroes either way. -/
theorem chacha20_poly1305_open_spec (h : RunsChaCha20Poly1305) (key : Std.Array U8 32#usize)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (tag : Std.Array U8 16#usize)
    (hl : inout.length ≤ 2 ^ 38 - 64) :
    low.x86_64.chacha20poly1305.open key nonce aad inout tag ⦃ r =>
      let o := chacha20poly1305.open (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val)
        (bvs tag.val)
      r.2.length = inout.length ∧ r.1 = o.2 ∧ (o.2 → bvs r.2.val = o.1) ⦄ := by
  have hh := h.2.1
  unfold low.x86_64.chacha20poly1305.open
  obtain ⟨-, -, ⟨⟨t, hi⟩, ⟨s, hs⟩⟩ | ⟨hi, ⟨s, hs⟩, ⟨a, ha⟩, hop⟩⟩ := h
  · simp only [hi, hs, bind_ok]
    apply WP.spec_mono (open_ifma_spec t key nonce aad inout tag)
    rintro ⟨valid, pt⟩ ⟨hv, hpt⟩
    have hk : (bvs key.val).length = 32 := by simp
    have hn : (bvs nonce.val).length = 12 := by simp
    refine ⟨?_, hv, fun ho => by rw [hpt, ite_eq_left ho]⟩
    have hlen := congrArg List.length hpt
    rw [bvs_length] at hlen
    change pt.val.length = inout.val.length
    rw [hlen]
    split <;> simp [chacha20poly1305.open, spec.vg.length_encrypt _ _ _ _ hk hn, Slice.length]
  · simp only [hi, hs, ha, bind_ok]
    apply WP.spec_bind (hop s a key nonce aad inout hl).2
    rintro ⟨actual, pt⟩ ⟨hlen, hpt, hmac⟩
    simp only [lift, bind_ok]
    apply WP.spec_bind (ct_equal_spec hh _ _)
    rintro _ rfl
    refine (WP.spec_ok _).2 ⟨hlen, ?_, fun _ => hpt⟩
    simp only [chacha20poly1305.open]
    rw [← hmac]
    simp only [Std.Array.to_slice, Slice.from_val]
    by_cases hv : actual.val = tag.val
    · simp [hv]
    · have hb : (bvs actual.val == bvs tag.val) = false := by
        rw [Bool.eq_false_iff]; intro hb; exact hv ((bvs_inj _ _).1 (beq_iff_eq.1 hb))
      simp [hv, hb]

/-- On these CPUs the one pass seals every message the counter covers as RFC
8439 does. -/
theorem seals (h : RunsChaCha20Poly1305) (len : Nat) : Seals len :=
  ⟨h.1, fun key nonce aad inout hlen hl =>
    chacha20_poly1305_seal_spec h key nonce aad inout (hlen ▸ hl)⟩

/-- On these CPUs the one pass opens every message the counter covers as RFC
8439 does. -/
theorem opens (h : RunsChaCha20Poly1305) (len : Nat) : Opens len :=
  ⟨h.1, fun key nonce aad inout tag hlen hl =>
    chacha20_poly1305_open_spec h key nonce aad inout tag (hlen ▸ hl)⟩

end rind.x86_64
