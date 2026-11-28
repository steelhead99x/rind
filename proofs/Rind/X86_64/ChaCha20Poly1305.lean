import Rind.X86_64.ChaCha20Poly1305Api
import Rind.X86_64.CtEqual
import Rind.X86_64.VgChaCha20Poly1305
open Aeneas Aeneas.Std Result rind.spec

/-!
# ChaCha20-Poly1305's one pass on x86_64

`Rind.X86_64.ChaCha20Poly1305Api` proves the AEAD API's ChaCha20-Poly1305 and
XChaCha20-Poly1305 from `Seals` and `Opens`, that the one pass computes RFC
8439's AEAD. `seals` and `opens` prove those on CPUs that run a one pass,
which `RunsSeal` and `RunsOpen` state. CPUs that pass
`HaveVgChaCha20Poly1305`'s `check_seal` or `check_open` for the
message's length run pyca/verified-garbage's IFMA or AVX2 one pass, whose
theorems `Rind.X86_64.VgChaCha20Poly1305` imports as axioms, so on them the
theorems here earn the ✓: with AVX-512 IFMA every length, but on Zen 4 a
seal of fewer than 800 bytes and an open of fewer than 512, and on Intel's
CPUs with AVX2 but no AVX-512 from the lengths `cpu::INTEL_AVX2_SEAL_FROM`
and `INTEL_AVX2_OPEN_FROM` name. CPUs that fail the check and pass
`HaveSse41`'s run aws-lc's one-pass routines, but for the AVX2 seal, rind's
structured copy of aws-lc's, which the theorems take as the hypothesis
`OnePass`: that they compute RFC 8439's ciphertext and tag.
`Rind.X86_64.ChaCha20Poly1305Asm` proves the copy constant-time, but no
proof covers what any of them computes yet, so on those CPUs no theorem here
earns the ✓. CPUs that
fail both run the separate passes, which no theorem here covers yet.
-/

namespace rind.x86_64

/-- The one-pass routines behind `one_pass`, aws-lc's and rind's structured
copy of aws-lc's AVX2 seal, compute RFC 8439's AEAD for a message of at most
2^38 - 64 bytes, as many as its 32-bit block counter covers from block 1:
sealing leaves the ChaCha20 ciphertext in place and returns the Poly1305 tag
over the AAD and it, and opening leaves the plaintext and returns the tag
over the AAD and the ciphertext it was given. Either half, AVX2 or SSE4.1,
computes the same. -/
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

/-- rind runs a one pass a theorem covers when it seals a message of `len`
bytes on this CPU: its entry guard passes and holds, and of its CPU-feature
checks, either `HaveVgChaCha20Poly1305`'s `check_seal` passes and
`HaveSse41`'s, which the dispatch reads first, returns, so it runs
pyca/verified-garbage's one pass, or the first fails and `HaveSse41`'s passes,
so it runs rind's copy of aws-lc's AVX2 seal, or aws-lc's SSE4.1 one without
AVX2, and `OnePass` holds. None reads an input but the length,
which each takes as any `Usize` of value `len`. -/
def RunsSeal (len : Nat) : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ low.entry.Entry.assert_held = ok () ∧
  ((∃ t, ∀ l : Usize, l.val = len →
      low.x86_64.cpu.HaveVgChaCha20Poly1305.check_seal l = ok (some t)) ∧
      (∃ s, low.x86_64.cpu.HaveSse41.check = ok s) ∨
    (∀ l : Usize, l.val = len →
      low.x86_64.cpu.HaveVgChaCha20Poly1305.check_seal l = ok none) ∧
      (∃ s, low.x86_64.cpu.HaveSse41.check = ok (some s)) ∧
      (∃ a, low.x86_64.cpu.HaveAvx2.check = ok a) ∧ OnePass)

/-- As `RunsSeal`, for an open of `len` bytes, whose dispatch reads
`check_open`. -/
def RunsOpen (len : Nat) : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ low.entry.Entry.assert_held = ok () ∧
  ((∃ t, ∀ l : Usize, l.val = len →
      low.x86_64.cpu.HaveVgChaCha20Poly1305.check_open l = ok (some t)) ∧
      (∃ s, low.x86_64.cpu.HaveSse41.check = ok s) ∨
    (∀ l : Usize, l.val = len →
      low.x86_64.cpu.HaveVgChaCha20Poly1305.check_open l = ok none) ∧
      (∃ s, low.x86_64.cpu.HaveSse41.check = ok (some s)) ∧
      (∃ a, low.x86_64.cpu.HaveAvx2.check = ok a) ∧ OnePass)

/-! ## The one-pass seal and open, `low::x86_64::chacha20poly1305` -/

theorem chacha20_poly1305_seal_spec (key : Std.Array U8 32#usize)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (h : RunsSeal inout.length)
    (hl : inout.length ≤ 2 ^ 38 - 64) :
    low.x86_64.chacha20poly1305.seal key nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧
      (bvs r.2.val, bvs r.1.val) =
        chacha20poly1305.seal (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) ⦄ := by
  unfold low.x86_64.chacha20poly1305.seal
  have hlen : (Slice.len inout).val = inout.length := by simp [Slice.len_val, Slice.length]
  obtain ⟨-, -, ⟨⟨t, hi⟩, ⟨s, hs⟩⟩ | ⟨hi, ⟨s, hs⟩, ⟨a, ha⟩, hop⟩⟩ := h
  · simp only [hi (Slice.len inout) hlen, hs, bind_ok]
    exact seal_vg_spec t key nonce aad inout
  · simp only [hi (Slice.len inout) hlen, hs, ha, bind_ok]
    exact (hop s a key nonce aad inout hl).1

/-- The one-pass open returns whether RFC 8439's tag is `tag`, leaving the
plaintext in place if it is. Where it is not, VG's leaves zeros and aws-lc's
the plaintext, which `open_tail_spec` zeroes either way. -/
theorem chacha20_poly1305_open_spec (key : Std.Array U8 32#usize)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (tag : Std.Array U8 16#usize)
    (h : RunsOpen inout.length) (hl : inout.length ≤ 2 ^ 38 - 64) :
    low.x86_64.chacha20poly1305.open key nonce aad inout tag ⦃ r =>
      let o := chacha20poly1305.open (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val)
        (bvs tag.val)
      r.2.length = inout.length ∧ r.1 = o.2 ∧ (o.2 → bvs r.2.val = o.1) ⦄ := by
  have hh := h.2.1
  have hlen : (Slice.len inout).val = inout.length := by simp [Slice.len_val, Slice.length]
  unfold low.x86_64.chacha20poly1305.open
  obtain ⟨-, -, ⟨⟨t, hi⟩, ⟨s, hs⟩⟩ | ⟨hi, ⟨s, hs⟩, ⟨a, ha⟩, hop⟩⟩ := h
  · simp only [hi (Slice.len inout) hlen, hs, bind_ok]
    apply WP.spec_mono (open_vg_spec t key nonce aad inout tag)
    rintro ⟨valid, pt⟩ ⟨hv, hpt⟩
    have hk : (bvs key.val).length = 32 := by simp
    have hn : (bvs nonce.val).length = 12 := by simp
    refine ⟨?_, hv, fun ho => by rw [hpt, ite_eq_left ho]⟩
    have hlen := congrArg List.length hpt
    rw [bvs_length] at hlen
    change pt.val.length = inout.val.length
    rw [hlen]
    split <;> simp [chacha20poly1305.open, spec.vg.length_encrypt _ _ _ _ hk hn, Slice.length]
  · simp only [hi (Slice.len inout) hlen, hs, ha, bind_ok]
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
8439 does, at the length the dispatch reads. -/
theorem seals (len : Nat) (h : RunsSeal len) : Seals len :=
  ⟨h.1, fun key nonce aad inout hlen hl =>
    chacha20_poly1305_seal_spec key nonce aad inout (by rw [hlen]; exact h) (hlen ▸ hl)⟩

/-- On these CPUs the one pass opens every message the counter covers as RFC
8439 does, at the length the dispatch reads. -/
theorem opens (len : Nat) (h : RunsOpen len) : Opens len :=
  ⟨h.1, fun key nonce aad inout tag hlen hl =>
    chacha20_poly1305_open_spec key nonce aad inout tag (by rw [hlen]; exact h) (hlen ▸ hl)⟩

end rind.x86_64
