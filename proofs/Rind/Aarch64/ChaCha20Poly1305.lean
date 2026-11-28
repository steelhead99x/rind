import Rind.Aarch64.VgChaCha20Poly1305
import Rind.Aarch64.ChaCha20Poly1305Api
import Rind.Aarch64.CtEqual
open Aeneas Aeneas.Std Result rind.spec

/-!
# ChaCha20-Poly1305's one pass on aarch64

`Rind.Aarch64.ChaCha20Poly1305Api` proves the AEAD API's ChaCha20-Poly1305 and
XChaCha20-Poly1305 from `Seals` and `Opens`, that the one pass computes RFC
8439's AEAD for a message of a given length. `seals` and `opens` prove them
where a proof covers the code the one pass runs, which `SealCovered` and
`OpenCovered` state: on a CPU with SVE2, pyca/verified-garbage's SVE2
routines, at every length; on one without it, VG's NEON routines at the
lengths `SealsNeon` and `OpensNeon` name, and aws-lc's NEON routines at the
rest, which the theorems take as the hypothesis `AwsLc`. rind runs its
structured copy of aws-lc's routines, whose constant time
`Rind.Aarch64.ChaCha20Poly1305Asm` proves but whose results no proof covers
yet, so `seals_sve2`, `opens_sve2`, `seals_neon`, and `opens_neon` state
where the theorems earn the ✓.
-/

namespace rind.aarch64

/-- aws-lc's NEON one pass, behind `seal_aws_lc` and `open_aws_lc`, computes
RFC 8439's AEAD for a message of at most 2^38 - 64 bytes, as many as its
32-bit block counter covers from block 1: sealing leaves the ChaCha20
ciphertext in place and returns the Poly1305 tag over the AAD and it, and
opening leaves the plaintext and returns the tag over the AAD and the
ciphertext it was given. -/
def AwsLc : Prop :=
  ∀ (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8),
    inout.length ≤ 2 ^ 38 - 64 →
    low.aarch64.chacha20poly1305.seal_aws_lc key nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧
      (bvs r.2.val, bvs r.1.val) =
        chacha20poly1305.seal (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) ⦄ ∧
    low.aarch64.chacha20poly1305.open_aws_lc key nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧
      bvs r.2.val = chacha20.encrypt (bvs key.val) 1 (bvs nonce.val) (bvs inout.val) ∧
      bvs r.1.val = poly1305.mac (chacha20poly1305.otk (bvs key.val) (bvs nonce.val))
        (chacha20poly1305.macData (bvs aad.val) (bvs inout.val)) ⦄

/-- rind runs its one pass on this CPU: its entry guard passes and holds, and
its SVE2 check returns `s`. None reads an input. -/
def RunsChaCha20Poly1305 (s : Option low.aarch64.cpu.HaveSve2) : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ low.entry.Entry.assert_held = ok () ∧
  low.aarch64.cpu.HaveSve2.check = ok s

/-- A proof covers the one pass's seal of `len` bytes on a CPU whose SVE2
check returns `s`: VG's routines run it, with SVE2 or at the lengths
`SealsNeon` names, or aws-lc's do and meet `AwsLc`. -/
def SealCovered (s : Option low.aarch64.cpu.HaveSve2) (len : Nat) : Prop :=
  s.isSome ∨ SealsNeon len ∨ AwsLc

/-- A proof covers the one pass's open of `len` bytes on a CPU whose SVE2
check returns `s`: VG's routines run it, with SVE2 or at the lengths
`OpensNeon` names, or aws-lc's do and meet `AwsLc`. -/
def OpenCovered (s : Option low.aarch64.cpu.HaveSve2) (len : Nat) : Prop :=
  s.isSome ∨ OpensNeon len ∨ AwsLc

/-! ## aws-lc's routines, at the lengths VG's do not run -/

theorem chacha20_poly1305_seal_aws_lc_spec (h : low.aarch64.cpu.HaveSve2.check = ok none) (ha : AwsLc)
    (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8)
    (hv : ¬ SealsNeon inout.length) (hl : inout.length ≤ 2 ^ 38 - 64) :
    low.aarch64.chacha20poly1305.seal key nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧
      (bvs r.2.val, bvs r.1.val) =
        chacha20poly1305.seal (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) ⦄ := by
  unfold low.aarch64.chacha20poly1305.seal
  simp only [h, bind_ok, seal_runs_vg_eq, Slice.len_val, decide_eq_false hv, Bool.false_eq_true,
    ↓reduceIte]
  exact (ha key nonce aad inout hl).1

/-- aws-lc's open returns the tag, which rind compares with `tag` in
constant time. -/
theorem chacha20_poly1305_open_aws_lc_spec (hh : low.entry.Entry.assert_held = ok ())
    (h : low.aarch64.cpu.HaveSve2.check = ok none) (ha : AwsLc)
    (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8)
    (tag : Std.Array U8 16#usize) (hv : ¬ OpensNeon inout.length) (hl : inout.length ≤ 2 ^ 38 - 64) :
    low.aarch64.chacha20poly1305.open key nonce aad inout tag ⦃ r =>
      let o := chacha20poly1305.open (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val)
        (bvs tag.val)
      r.2.length = inout.length ∧ r.1 = o.2 ∧ (o.2 → bvs r.2.val = o.1) ⦄ := by
  unfold low.aarch64.chacha20poly1305.open
  simp only [h, bind_ok, open_runs_vg_eq, Slice.len_val, decide_eq_false hv, Bool.false_eq_true,
    ↓reduceIte]
  apply WP.spec_bind (ha key nonce aad inout hl).2
  rintro ⟨actual, pt⟩ ⟨hlen, hpt, hmac⟩
  simp only [lift, bind_ok]
  apply WP.spec_bind (ct_equal_spec hh _ _)
  rintro _ rfl
  refine (WP.spec_ok _).2 ⟨hlen, ?_, fun _ => hpt⟩
  simp only [chacha20poly1305.open]
  rw [← hmac]
  simp only [Std.Array.to_slice, Slice.from_val]
  by_cases heq : actual.val = tag.val
  · simp [heq]
  · have hb : (bvs actual.val == bvs tag.val) = false := by
      rw [Bool.eq_false_iff]; intro hb; exact heq ((bvs_inj _ _).1 (beq_iff_eq.1 hb))
    simp [heq, hb]

/-! ## Every path -/

/-- VG's open, which leaves zeros where the tag is not RFC 8439's, leaves
what `Opens` states. -/
theorem opens_of_vg (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8)
    (tag : Std.Array U8 16#usize) (o : List (BitVec 8) × Bool)
    (ho : o = chacha20poly1305.open (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val)
      (bvs tag.val))
    (r : Bool × Slice U8) (hr : r.1 = o.2 ∧ bvs r.2.val = if o.2 then o.1 else List.replicate inout.length 0) :
    r.2.length = inout.length ∧ r.1 = o.2 ∧ (o.2 → bvs r.2.val = o.1) := by
  obtain ⟨hv, hpt⟩ := hr
  have hk : (bvs key.val).length = 32 := by simp
  have hn : (bvs nonce.val).length = 12 := by simp
  refine ⟨?_, hv, fun h => by rw [hpt, ite_eq_left h]⟩
  have hlen := congrArg List.length hpt
  rw [bvs_length] at hlen
  change r.2.val.length = inout.val.length
  rw [hlen, ho]
  split <;> simp [chacha20poly1305.open, spec.vg.length_encrypt _ _ _ _ hk hn, Slice.length]

/-- The one pass seals `len` bytes as RFC 8439 does wherever a proof covers
the code it runs. -/
theorem seals {s : Option low.aarch64.cpu.HaveSve2} (h : RunsChaCha20Poly1305 s) (len : Nat)
    (hc : SealCovered s len) : Seals len := by
  obtain ⟨he, -, hs⟩ := h
  refine ⟨he, fun key nonce aad inout hlen hl => ?_⟩
  subst hlen
  rcases s with _ | t
  · by_cases hv : SealsNeon inout.length
    · exact chacha20_poly1305_seal_neon_spec hs key nonce aad inout hv
    · have ha : AwsLc := by
        rcases hc with hc | hc | hc
        · simp at hc
        · exact absurd hc hv
        · exact hc
      exact chacha20_poly1305_seal_aws_lc_spec hs ha key nonce aad inout hv hl
  · exact chacha20_poly1305_seal_sve2_spec t hs key nonce aad inout

/-- The one pass opens `len` bytes as RFC 8439 does wherever a proof covers
the code it runs. -/
theorem opens {s : Option low.aarch64.cpu.HaveSve2} (h : RunsChaCha20Poly1305 s) (len : Nat)
    (hc : OpenCovered s len) : Opens len := by
  obtain ⟨he, hh, hs⟩ := h
  refine ⟨he, fun key nonce aad inout tag hlen hl => ?_⟩
  subst hlen
  rcases s with _ | t
  · by_cases hv : OpensNeon inout.length
    · exact WP.spec_mono (chacha20_poly1305_open_neon_spec hs key nonce aad inout tag hv)
        (opens_of_vg key nonce aad inout tag _ rfl)
    · have ha : AwsLc := by
        rcases hc with hc | hc | hc
        · simp at hc
        · exact absurd hc hv
        · exact hc
      exact chacha20_poly1305_open_aws_lc_spec hh hs ha key nonce aad inout tag hv hl
  · exact WP.spec_mono (chacha20_poly1305_open_sve2_spec t hs key nonce aad inout tag)
      (opens_of_vg key nonce aad inout tag _ rfl)

/-! ## Where the theorems earn the ✓ -/

/-- On a CPU with SVE2, the one pass seals every message as RFC 8439 does. -/
theorem seals_sve2 {t : low.aarch64.cpu.HaveSve2} (h : RunsChaCha20Poly1305 (some t)) (len : Nat) :
    Seals len :=
  seals h len (Or.inl rfl)

/-- On a CPU with SVE2, the one pass opens every message as RFC 8439 does. -/
theorem opens_sve2 {t : low.aarch64.cpu.HaveSve2} (h : RunsChaCha20Poly1305 (some t)) (len : Nat) :
    Opens len :=
  opens h len (Or.inl rfl)

/-- On a CPU without SVE2, the one pass seals a message of a length
`SealsNeon` names, 1350 bytes and 16 KiB among them, as RFC 8439 does. -/
theorem seals_neon (h : RunsChaCha20Poly1305 none) (len : Nat) (hv : SealsNeon len) : Seals len :=
  seals h len (Or.inr (Or.inl hv))

/-- On a CPU without SVE2, the one pass opens a message of a length
`OpensNeon` names as RFC 8439 does. -/
theorem opens_neon (h : RunsChaCha20Poly1305 none) (len : Nat) (hv : OpensNeon len) : Opens len :=
  opens h len (Or.inr (Or.inl hv))

end rind.aarch64
