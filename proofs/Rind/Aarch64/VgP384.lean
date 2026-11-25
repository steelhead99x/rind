import Rind.Aarch64.Funs
import Rind.VgP384
open Aeneas Aeneas.Std Result VG.Spec.Weierstrass

/-!
# pyca/verified-garbage's P-384 contracts on aarch64

Each axiom restates the contract VG's theorems prove of the routine one of
rind's wrappers in `low::aarch64::p384_vg` calls, at the revision
`admin/import-vg` pins (0aa40d6c): `VG.Spec.EcKey.Instance.publicKeyContract`
and `VG.Spec.Ecdsa.Instance.verifyHashContract`, at P-384, which
`admin/import-vg-models` vendors. Each theorem is VG's registration of the
routine, which discharges the curve's facts its proof takes, such as
`Law Spec.P384.curve`, from VG's own proofs of them. The wrappers call VG's
routines through raw pointers to a scratch buffer, which Aeneas cannot
translate, so each axiom is about the opaque wrapper. Their preconditions on
memory hold for every call from safe Rust: a routine writes only its output
and scratch, which the wrapper owns, so they overlap neither each other, its
inputs, nor the stack the routine reserves; its inputs may overlap. The
routines need only the base AArch64 instructions. A routine returns 1 or 0,
and the wrapper returns `some` or `true` where it returned 1. What a routine
leaves in its scratch buffer, which the contract leaves unspecified and rind
does not wipe, what it clears from registers, and what it may leak, are left
out.

Trusted: the restatement; that rind's `vg_*` routines are VG's at the pin,
whose instructions and relocation targets `admin/prove vg` checks along with
VG's models of the instructions they run; that the constant tables
`admin/import-vg` generates beside them are VG's at the pin, which no check
reads back; and VG's proofs and models.
-/

namespace rind.aarch64

open rind.spec.vgP384

/-- `vg_ec_p384_public_key`'s `publicKeyContract`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/EcKey/AArch64/P384/Verified.lean#L76 (`pk_verified`),
registered at
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/EcP384/AArch64.lean#L50. -/
@[step]
axiom vg_p384_public_key_spec (self : low.aarch64.p384_vg.MulBase) (d : Std.Array U8 48#usize) :
    low.aarch64.p384_vg.MulBase.public_key self d ⦃ r =>
      match VG.Spec.EcKey.publicKey C (ofBytes (vgBytes d)) with
      | some (.affine x y) => ∃ out, r = some out ∧ vgBytes out = VG.Spec.EcKey.encodePoint (.affine x y)
      | _ => r = none ⦄

/-- `vg_ecdsa_p384_verify`'s `verifyHashContract`, for a 48-byte hash:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/Verified.lean#L1432 (`verifyHash_verified`),
registered at
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/EcdsaP384/AArch64.lean#L94. -/
@[step]
axiom vg_p384_verify_spec (self : low.aarch64.p384_vg.Verify) (pub : Std.Array U8 97#usize)
    (e : Std.Array U8 48#usize) (sig : Std.Array U8 96#usize) :
    low.aarch64.p384_vg.Verify.ecdsa_verify self pub e sig ⦃ b =>
      b = VG.Spec.Ecdsa.verify C (vgBytes pub) (VG.Spec.Ecdsa.hashToInt C (vgBytes e)) (vgBytes sig) ⦄

end rind.aarch64
