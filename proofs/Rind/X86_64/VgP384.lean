import Rind.X86_64.Funs
import Rind.VgP384
open Aeneas Aeneas.Std Result VG.Spec.Weierstrass

/-!
# pyca/verified-garbage's P-384 contracts on X86_64

Each axiom restates the contract VG's theorems prove of the routines one of
rind's wrappers in `low::x86_64::p384_vg` calls, at the revision
`admin/import-vg` pins (0aa40d6c): `VG.Spec.EcKey.Instance.publicKeyContract`
and `VG.Spec.Ecdsa.Instance.verifyHashContract`, at P-384, which
`admin/import-vg-models` vendors. Each theorem is VG's registration of the
routine, which discharges the curve's facts its proof takes, such as
`Law Spec.P384.curve`, from VG's own proofs of them. The wrappers call VG's
routines through raw pointers to a scratch buffer, which Aeneas cannot
translate, so each axiom is about the opaque wrapper, and covers every
routine it may call, which all state the one contract. Their preconditions on
memory hold for every call from safe Rust: a routine writes only its output
and scratch, which the wrapper owns, so they overlap neither each other, its
inputs, nor the stack the routine reserves; its inputs may overlap. The CPU
features are the token's to prove: `MulBase::check` holds BMI2 and ADX for
the variant that takes them, and `Verify::check` passed only with them. A
routine returns 1 or 0, and the wrapper returns `some` or `true` where it
returned 1. What a routine leaves in its scratch buffer, which the contract
leaves unspecified and rind does not wipe, what it clears from registers, and
what it may leak, are left out.

Trusted: the restatement; that rind's `vg_*` routines are VG's at the pin,
whose instructions and relocation targets `admin/prove vg` checks along with
VG's models of the instructions they run; that the constant tables
`admin/import-vg` generates beside them are VG's at the pin, which no check
reads back; and VG's proofs and models.
-/

namespace rind.x86_64

open rind.spec.vgP384

/-- `vg_ec_p384_public_key`'s and `vg_ec_p384_public_key_adx`'s
`publicKeyContract`, the routines `MulBase::public_key` calls, without and
with BMI2 and ADX:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/EcKey/X86_64/P384/Verified.lean#L161 (`pk_verified`) and
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/EcKey/X86_64/P384/VerifiedAdx.lean#L134 (`pk_verified_adx`),
registered at
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/EcP384/X86_64.lean#L111 and #L115. -/
@[step]
axiom vg_p384_public_key_spec (self : low.x86_64.p384_vg.MulBase) (d : Std.Array U8 48#usize) :
    low.x86_64.p384_vg.MulBase.public_key self d ⦃ r =>
      match VG.Spec.EcKey.publicKey C (ofBytes (vgBytes d)) with
      | some (.affine x y) => ∃ out, r = some out ∧ vgBytes out = VG.Spec.EcKey.encodePoint (.affine x y)
      | _ => r = none ⦄

/-- `vg_ecdsa_p384_verify_adx`'s `verifyHashContract`, for a 48-byte hash,
the routine `Verify::ecdsa_verify` calls:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Ecdsa/Verify/X86_64/P384/JointVerified.lean#L251 (`verifyHash_verified_adx`),
registered at
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/EcdsaP384/X86_64.lean#L126. -/
@[step]
axiom vg_p384_verify_spec (self : low.x86_64.p384_vg.Verify) (pub : Std.Array U8 97#usize)
    (e : Std.Array U8 48#usize) (sig : Std.Array U8 96#usize) :
    low.x86_64.p384_vg.Verify.ecdsa_verify self pub e sig ⦃ b =>
      b = VG.Spec.Ecdsa.verify C (vgBytes pub) (VG.Spec.Ecdsa.hashToInt C (vgBytes e)) (vgBytes sig) ⦄

end rind.x86_64
