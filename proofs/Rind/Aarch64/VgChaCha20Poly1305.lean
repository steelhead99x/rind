import Rind.Aarch64.AesKey
import Rind.VgChaCha20Poly1305
open Aeneas Aeneas.Std Result rind.spec

/-!
# ChaCha20-Poly1305's one pass on aarch64 with SVE2

On a CPU with SVE2, `low::aarch64::chacha20poly1305`'s `seal` and `open` run
pyca/verified-garbage's (VG's) `vg_chacha20_poly1305_seal_sve2` and
`vg_chacha20_poly1305_open_sve2`, each behind one wrapper, whose contracts
the two axioms restate over VG's spec, `Spec/ChaCha20Poly1305.lean`.
`Rind.VgChaCha20Poly1305` proves that spec is `Rind.Spec`'s RFC 8439, so the
theorems here state the one pass as the x86_64 proof's `OnePass` does. Each
axiom states only what its wrapper returns, not VG's wipe of its stack
scratch, its memory safety, or that it runs in constant time.

The wrappers pass Rust objects, which never overlap one another, the stack,
or the end of the address space, as VG's contracts require; the token proves
SVE2. VG's contracts set no bound on the length, past which ChaCha20's
32-bit block counter wraps, as `Rind.Spec`'s does too: the AEAD API refuses
a message past RFC 8439's `P_MAX` before it reaches these.
-/

namespace rind.aarch64

/-- `vg_chacha20_poly1305_seal_sve2`'s `sealContract`, whose ciphertext the
wrapper leaves in `inout` and whose tag it returns: https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20Poly1305/AArch64/Verified.lean#L2641
(`seal_framed`, at the SVE2 variant `Artifacts/ChaCha20Poly1305/AArch64.lean`
registers as `vg_chacha20_poly1305_seal_sve2`). -/
axiom vg_chacha20_poly1305_seal_sve2_spec (t : low.aarch64.cpu.HaveSve2)
    (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) :
    low.aarch64.chacha20poly1305.seal_sve2 t key nonce aad inout ⦃ r =>
      VG.Spec.ChaCha20Poly1305.encrypt (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) =
        (bvs r.2.val, bvs r.1.val) ⦄

/-- `vg_chacha20_poly1305_open_sve2`'s `openZeroContract`, whose 1 the
wrapper returns as `true`, leaving the plaintext in `inout`, and whose 0 as
`false`, leaving zeros: https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20Poly1305/AArch64/Verified.lean#L2658
(`open_framed`, at the SVE2 variant `Artifacts/ChaCha20Poly1305/AArch64.lean`
registers as `vg_chacha20_poly1305_open_sve2`). -/
axiom vg_chacha20_poly1305_open_sve2_spec (t : low.aarch64.cpu.HaveSve2)
    (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8)
    (tag : Std.Array U8 16#usize) :
    low.aarch64.chacha20poly1305.open_sve2 t key nonce aad inout tag ⦃ r =>
      match VG.Spec.ChaCha20Poly1305.decrypt (bvs key.val) (bvs nonce.val) (bvs aad.val)
          (bvs inout.val) (bvs tag.val) with
      | some pt => r.1 = true ∧ bvs r.2.val = pt
      | none => r.1 = false ∧ bvs r.2.val = List.replicate inout.length 0 ⦄

/-- On a CPU with SVE2, the one-pass seal leaves RFC 8439's ciphertext in
place and returns its tag over the AAD and it. -/
theorem chacha20_poly1305_seal_sve2_spec (t : low.aarch64.cpu.HaveSve2)
    (h : low.aarch64.cpu.HaveSve2.check = ok (some t)) (key : Std.Array U8 32#usize)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) :
    low.aarch64.chacha20poly1305.seal key nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧
      (bvs r.2.val, bvs r.1.val) =
        chacha20poly1305.seal (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) ⦄ := by
  have hk : (bvs key.val).length = 32 := by simp
  have hn : (bvs nonce.val).length = 12 := by simp
  unfold low.aarch64.chacha20poly1305.seal
  simp only [h, bind_ok]
  apply WP.spec_mono (vg_chacha20_poly1305_seal_sve2_spec t key nonce aad inout)
  rintro ⟨tag, ct⟩ hr
  rw [spec.vg.vgSeal_eq _ _ _ _ hk hn] at hr
  refine ⟨?_, hr.symm⟩
  have hl := congrArg (fun p => p.1.length) hr
  simp only [chacha20poly1305.seal, spec.vg.length_encrypt _ _ _ _ hk hn, List.length_map] at hl
  exact hl.symm

/-- On a CPU with SVE2, the one-pass open returns whether RFC 8439's tag over
the AAD and the ciphertext is `tag`, leaving the plaintext in place if it is
and zeros if not. -/
theorem chacha20_poly1305_open_sve2_spec (t : low.aarch64.cpu.HaveSve2)
    (h : low.aarch64.cpu.HaveSve2.check = ok (some t)) (key : Std.Array U8 32#usize)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) (tag : Std.Array U8 16#usize) :
    low.aarch64.chacha20poly1305.open key nonce aad inout tag ⦃ r =>
      let o := chacha20poly1305.open (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val)
        (bvs tag.val)
      r.1 = o.2 ∧ bvs r.2.val = if o.2 then o.1 else List.replicate inout.length 0 ⦄ := by
  have hk : (bvs key.val).length = 32 := by simp
  have hn : (bvs nonce.val).length = 12 := by simp
  unfold low.aarch64.chacha20poly1305.open
  simp only [h, bind_ok]
  apply WP.spec_mono (vg_chacha20_poly1305_open_sve2_spec t key nonce aad inout tag)
  rintro ⟨valid, pt⟩ hr
  rw [spec.vg.vgOpen_eq _ _ _ _ _ hk hn] at hr
  split at hr <;> simp_all

end rind.aarch64
