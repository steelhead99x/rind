import Rind.Aarch64.AesKey
import Rind.VgChaCha20Poly1305
open Aeneas Aeneas.Std Result rind.spec

/-!
# ChaCha20-Poly1305's one pass on pyca/verified-garbage's routines, on aarch64

On a CPU with SVE2, `low::aarch64::chacha20poly1305`'s `seal` and `open` run
pyca/verified-garbage's (VG's) `vg_chacha20_poly1305_seal_sve2` and
`vg_chacha20_poly1305_open_sve2`, and on one without it, at the lengths
`SealsNeon` and `OpensNeon` name, `vg_chacha20_poly1305_seal_neon` and
`vg_chacha20_poly1305_open_neon`, each behind one wrapper, whose contracts
the four axioms restate over VG's spec, `Spec/ChaCha20Poly1305.lean`.
`Rind.VgChaCha20Poly1305` proves that spec is `Rind.Spec`'s RFC 8439, so the
theorems here state the one pass as `Rind.Aarch64.ChaCha20Poly1305Api`'s
`Seals` and `Opens` do. Each axiom states only what its wrapper returns, not
VG's wipe of its stack scratch, its memory safety, or that it runs in
constant time.

The wrappers pass Rust objects, which never overlap one another, the stack,
or the end of the address space, as VG's contracts require; rind requires
NEON, and the token proves SVE2. VG's contracts set no bound on the length,
past which ChaCha20's 32-bit block counter wraps, as `Rind.Spec`'s does too:
the AEAD API refuses a message past RFC 8439's `P_MAX` before it reaches
these.
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

/-- `vg_chacha20_poly1305_seal_neon`'s `sealContract`, whose ciphertext the
wrapper leaves in `inout` and whose tag it returns: https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20Poly1305/AArch64/Verified.lean#L2641
(`seal_framed`, at the NEON variant `Artifacts/ChaCha20Poly1305/AArch64.lean`
registers as `vg_chacha20_poly1305_seal_neon`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/ChaCha20Poly1305/AArch64.lean#L17). -/
axiom vg_chacha20_poly1305_seal_neon_spec
    (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) :
    low.aarch64.chacha20poly1305.seal_neon key nonce aad inout ⦃ r =>
      VG.Spec.ChaCha20Poly1305.encrypt (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) =
        (bvs r.2.val, bvs r.1.val) ⦄

/-- `vg_chacha20_poly1305_open_neon`'s `openZeroContract`, whose 1 the
wrapper returns as `true`, leaving the plaintext in `inout`, and whose 0 as
`false`, leaving zeros: https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20Poly1305/AArch64/Verified.lean#L2658
(`open_framed`, at the NEON variant `Artifacts/ChaCha20Poly1305/AArch64.lean`
registers as `vg_chacha20_poly1305_open_neon`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/ChaCha20Poly1305/AArch64.lean#L22). -/
axiom vg_chacha20_poly1305_open_neon_spec
    (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8)
    (tag : Std.Array U8 16#usize) :
    low.aarch64.chacha20poly1305.open_neon key nonce aad inout tag ⦃ r =>
      match VG.Spec.ChaCha20Poly1305.decrypt (bvs key.val) (bvs nonce.val) (bvs aad.val)
          (bvs inout.val) (bvs tag.val) with
      | some pt => r.1 = true ∧ bvs r.2.val = pt
      | none => r.1 = false ∧ bvs r.2.val = List.replicate inout.length 0 ⦄

/-! ## From VG's spec to RFC 8439 -/

/-- What VG's seal contract gives is RFC 8439's seal. -/
theorem vg_seal_rfc (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize)
    (aad inout : Slice U8) (tag : Std.Array U8 16#usize) (ct : Slice U8)
    (hr : VG.Spec.ChaCha20Poly1305.encrypt (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) =
      (bvs ct.val, bvs tag.val)) :
    ct.length = inout.length ∧
      (bvs ct.val, bvs tag.val) =
        chacha20poly1305.seal (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) := by
  have hk : (bvs key.val).length = 32 := by simp
  have hn : (bvs nonce.val).length = 12 := by simp
  rw [spec.vg.vgSeal_eq _ _ _ _ hk hn] at hr
  refine ⟨?_, hr.symm⟩
  have hl := congrArg (fun p => p.1.length) hr
  simp only [chacha20poly1305.seal, spec.vg.length_encrypt _ _ _ _ hk hn, List.length_map] at hl
  exact hl.symm

/-- What VG's open contract gives: whether RFC 8439's tag is `tag`, and the
plaintext if it is, zeros if not. -/
theorem vg_open_rfc (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize)
    (aad inout : Slice U8) (tag : Std.Array U8 16#usize) (valid : Bool) (pt : Slice U8)
    (hr : match VG.Spec.ChaCha20Poly1305.decrypt (bvs key.val) (bvs nonce.val) (bvs aad.val)
          (bvs inout.val) (bvs tag.val) with
      | some pt' => valid = true ∧ bvs pt.val = pt'
      | none => valid = false ∧ bvs pt.val = List.replicate inout.length 0) :
    let o := chacha20poly1305.open (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val)
      (bvs tag.val)
    valid = o.2 ∧ bvs pt.val = if o.2 then o.1 else List.replicate inout.length 0 := by
  have hk : (bvs key.val).length = 32 := by simp
  have hn : (bvs nonce.val).length = 12 := by simp
  rw [spec.vg.vgOpen_eq _ _ _ _ _ hk hn] at hr
  split at hr <;> simp_all

/-! ## The lengths at which a CPU without SVE2 runs VG's routines -/

/-- The lengths `seal_runs_vg` names, at which a CPU without SVE2 seals with
VG's NEON routine. -/
abbrev SealsNeon (len : Nat) : Prop := (577 ≤ len ∧ len ≤ 768) ∨ 897 ≤ len

/-- The lengths `open_runs_vg` names, at which a CPU without SVE2 opens with
VG's NEON routine. -/
abbrev OpensNeon (len : Nat) : Prop := (129 ≤ len ∧ len ≤ 256) ∨ (449 ≤ len ∧ len ≤ 895) ∨ 961 ≤ len

theorem seal_runs_vg_eq (len : Usize) :
    low.aarch64.chacha20poly1305.seal_runs_vg len = ok (decide (SealsNeon len.val)) := by
  unfold low.aarch64.chacha20poly1305.seal_runs_vg SealsNeon
  split_ifs <;> simp only [ok.injEq] <;> symm <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not] <;>
    scalar_tac

theorem open_runs_vg_eq (len : Usize) :
    low.aarch64.chacha20poly1305.open_runs_vg len = ok (decide (OpensNeon len.val)) := by
  unfold low.aarch64.chacha20poly1305.open_runs_vg OpensNeon
  split_ifs <;> simp only [ok.injEq] <;> symm <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not] <;>
    scalar_tac

/-! ## The one pass on VG's routines -/

/-- On a CPU with SVE2, the one-pass seal leaves RFC 8439's ciphertext in
place and returns its tag over the AAD and it. -/
theorem chacha20_poly1305_seal_sve2_spec (t : low.aarch64.cpu.HaveSve2)
    (h : low.aarch64.cpu.HaveSve2.check = ok (some t)) (key : Std.Array U8 32#usize)
    (nonce : Std.Array U8 12#usize) (aad inout : Slice U8) :
    low.aarch64.chacha20poly1305.seal key nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧
      (bvs r.2.val, bvs r.1.val) =
        chacha20poly1305.seal (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) ⦄ := by
  unfold low.aarch64.chacha20poly1305.seal
  simp only [h, bind_ok]
  apply WP.spec_mono (vg_chacha20_poly1305_seal_sve2_spec t key nonce aad inout)
  rintro ⟨tag, ct⟩ hr
  exact vg_seal_rfc key nonce aad inout tag ct hr

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
  unfold low.aarch64.chacha20poly1305.open
  simp only [h, bind_ok]
  apply WP.spec_mono (vg_chacha20_poly1305_open_sve2_spec t key nonce aad inout tag)
  rintro ⟨valid, pt⟩ hr
  exact vg_open_rfc key nonce aad inout tag valid pt hr

/-- On a CPU without SVE2, the one-pass seal of a message whose length
`SealsNeon` names leaves RFC 8439's ciphertext in place and returns its tag
over the AAD and it. -/
theorem chacha20_poly1305_seal_neon_spec (h : low.aarch64.cpu.HaveSve2.check = ok none)
    (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8)
    (hv : SealsNeon inout.length) :
    low.aarch64.chacha20poly1305.seal key nonce aad inout ⦃ r =>
      r.2.length = inout.length ∧
      (bvs r.2.val, bvs r.1.val) =
        chacha20poly1305.seal (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val) ⦄ := by
  unfold low.aarch64.chacha20poly1305.seal
  simp only [h, bind_ok, seal_runs_vg_eq, Slice.len_val, decide_eq_true hv, ↓reduceIte]
  apply WP.spec_mono (vg_chacha20_poly1305_seal_neon_spec key nonce aad inout)
  rintro ⟨tag, ct⟩ hr
  exact vg_seal_rfc key nonce aad inout tag ct hr

/-- On a CPU without SVE2, the one-pass open of a message whose length
`OpensNeon` names returns whether RFC 8439's tag over the AAD and the
ciphertext is `tag`, leaving the plaintext in place if it is and zeros if
not. -/
theorem chacha20_poly1305_open_neon_spec (h : low.aarch64.cpu.HaveSve2.check = ok none)
    (key : Std.Array U8 32#usize) (nonce : Std.Array U8 12#usize) (aad inout : Slice U8)
    (tag : Std.Array U8 16#usize) (hv : OpensNeon inout.length) :
    low.aarch64.chacha20poly1305.open key nonce aad inout tag ⦃ r =>
      let o := chacha20poly1305.open (bvs key.val) (bvs nonce.val) (bvs aad.val) (bvs inout.val)
        (bvs tag.val)
      r.1 = o.2 ∧ bvs r.2.val = if o.2 then o.1 else List.replicate inout.length 0 ⦄ := by
  unfold low.aarch64.chacha20poly1305.open
  simp only [h, bind_ok, open_runs_vg_eq, Slice.len_val, decide_eq_true hv, ↓reduceIte]
  apply WP.spec_mono (vg_chacha20_poly1305_open_neon_spec key nonce aad inout tag)
  rintro ⟨valid, pt⟩ hr
  exact vg_open_rfc key nonce aad inout tag valid pt hr

end rind.aarch64
