import Rind.X86_64.ValeAesGcm
import Rind.VgChaCha20Poly1305
open Aeneas Aeneas.Std Result rind.spec

/-!
# ChaCha20-Poly1305's one pass on x86_64 from pyca/verified-garbage

On a CPU and at a length that pass `HaveVgChaCha20Poly1305`'s check,
`low::x86_64::chacha20poly1305`'s `seal` and `open` run
pyca/verified-garbage's (VG's) `vg_chacha20_poly1305_seal_ifma` and
`vg_chacha20_poly1305_open_ifma` where the token names the IFMA pair, or
`vg_chacha20_poly1305_seal_avx2` and `vg_chacha20_poly1305_open_avx2` where
it names the AVX2 pair, each pair behind one wrapper. VG proves both pairs to
the same contracts, which the two axioms restate over VG's spec, `Spec/ChaCha20Poly1305.lean`.
`Rind.VgChaCha20Poly1305` proves that spec is `Rind.Spec`'s RFC 8439, so the
theorems here state the one pass in `Rind.Spec`'s terms. Each axiom states
only what its wrapper returns, not VG's wipe of its stack scratch and
registers, its memory safety, or that it runs in constant time.

The wrappers pass Rust objects, which never overlap the stack or the end of
the address space. What the routines write, the data and seal's tag, are
exclusive borrows, which overlap no other argument; the key, nonce, AAD, and
open's tag may overlap one another, which VG's contracts allow for buffers a
routine only reads (`TCB/Sig.lean`). The token proves AVX, AVX2, AVX-512 F and
VL, and AVX512_IFMA for the IFMA pair, and AVX and AVX2 for the AVX2 pair. VG's contracts set no bound on the length, past which
ChaCha20's 32-bit block counter wraps, as `Rind.Spec`'s does too: the AEAD
API refuses a message past RFC 8439's `P_MAX` before it reaches these. VG's
theorems rest on its models of the instructions, which `admin/prove vg`
cosimulates for each instruction of the two routines, on the CPU or, where it
lacks a feature, under Intel SDE.
-/

namespace rind.x86_64

/-- `vg_chacha20_poly1305_seal_ifma`'s and `vg_chacha20_poly1305_seal_avx2`'s
`sealContract`, whose ciphertext the wrapper leaves in `inout` and whose tag
it returns: the registration `sealReg`, at the `ifma` and `avx2` variants
`Artifacts/ChaCha20Poly1305/X86_64.lean` registers under those names, of VG's `Shared.seal_verified`
with its stack and registers cleared: https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20Poly1305/X86_64/Scrub.lean#L604 -/
axiom vg_chacha20_poly1305_seal_spec (t : low.x86_64.cpu.HaveVgChaCha20Poly1305)
    (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) :
    low.x86_64.chacha20poly1305.seal_vg t key nonce aad inout ⦃ r =>
      VG.Spec.ChaCha20Poly1305.encrypt (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) =
        (bvs r.2.val, bvs r.1.val) ⦄

/-- `vg_chacha20_poly1305_open_ifma`'s and `vg_chacha20_poly1305_open_avx2`'s
`openZeroContract`, whose 1 the wrapper returns as `true`, leaving the
plaintext in `inout`, and whose 0 as `false`, leaving zeros: the registration
`openReg`, at the `ifma` and `avx2` variants
`Artifacts/ChaCha20Poly1305/X86_64.lean` registers under those names, of VG's `Shared.open_verified` with its
stack and registers cleared: https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20Poly1305/X86_64/Scrub.lean#L858 -/
axiom vg_chacha20_poly1305_open_spec (t : low.x86_64.cpu.HaveVgChaCha20Poly1305)
    (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8)
    (tag : Std.Array U8 16#usize) :
    low.x86_64.chacha20poly1305.open_vg t key nonce aad inout tag ⦃ r =>
      match VG.Spec.ChaCha20Poly1305.decrypt (bvs key.val) (bvs nonce.val) (bvs aad.val)
          (bvs inout.val) (bvs tag.val) with
      | some pt => r.1 = true ∧ bvs r.2.val = pt
      | none => r.1 = false ∧ bvs r.2.val = List.replicate inout.length 0 ⦄

/-- VG's one-pass seal leaves RFC 8439's ciphertext in place and returns its
tag over the AAD and it. -/
theorem seal_vg_spec (t : low.x86_64.cpu.HaveVgChaCha20Poly1305)
    (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) :
    low.x86_64.chacha20poly1305.seal_vg t key nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧
      (bvs r.2.val, bvs r.1.val) =
        chacha20poly1305.seal (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) ⦄ := by
  have hk : (bvs key.val).length = 32 := by simp
  have hn : (bvs nonce.val).length = 12 := by simp
  apply WP.spec_mono (vg_chacha20_poly1305_seal_spec t key nonce aad inout)
  rintro ⟨tag, ct⟩ hr
  rw [spec.vg.vgSeal_eq _ _ _ _ hk hn] at hr
  refine ⟨?_, hr.symm⟩
  have hl := congrArg (fun p => p.1.length) hr
  simp only [chacha20poly1305.seal, spec.vg.length_encrypt _ _ _ _ hk hn, List.length_map] at hl
  exact hl.symm

/-- VG's one-pass open returns whether RFC 8439's tag over the AAD and the
ciphertext is `tag`, leaving the plaintext in place if it is and zeros if
not. -/
theorem open_vg_spec (t : low.x86_64.cpu.HaveVgChaCha20Poly1305)
    (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8)
    (tag : Std.Array U8 16#usize) :
    low.x86_64.chacha20poly1305.open_vg t key nonce aad inout tag ⦃ r =>
      let o := chacha20poly1305.open (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val)
        (bvs tag.val)
      r.1 = o.2 ∧ bvs r.2.val = if o.2 then o.1 else List.replicate inout.length 0 ⦄ := by
  have hk : (bvs key.val).length = 32 := by simp
  have hn : (bvs nonce.val).length = 12 := by simp
  apply WP.spec_mono (vg_chacha20_poly1305_open_spec t key nonce aad inout tag)
  rintro ⟨valid, pt⟩ hr
  rw [spec.vg.vgOpen_eq _ _ _ _ _ hk hn] at hr
  split at hr <;> simp_all

end rind.x86_64
