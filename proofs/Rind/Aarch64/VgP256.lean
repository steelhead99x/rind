import Rind.Aarch64.Funs
import Rind.VgP256
open Aeneas Aeneas.Std Result VG.Spec.Weierstrass

/-!
# pyca/verified-garbage's P-256 contracts on aarch64

Each axiom restates the contract VG's theorems prove of the routines one of
rind's wrappers in `low::aarch64::p256_vg` calls, at the revision
`admin/import-vg` pins (0aa40d6c): `VG.Spec.EcKey.Instance.publicKeyContract`,
`VG.Spec.Ecdh.Instance.exchangeContract`, and
`VG.Spec.Ecdsa.Instance.verifyHashContract`, at P-256, which
`admin/import-vg-models` vendors. Each theorem is VG's registration of the
routine, which discharges the curve's facts its proof takes, such as
`Law Spec.P256.curve`, from VG's own proofs of them. The wrappers call VG's
routines through raw pointers to a scratch buffer, which Aeneas cannot
translate, so each axiom is about the opaque wrapper, and covers every
routine it may call, which all state the one contract. Their preconditions on
memory hold for every call from safe Rust: a routine writes only its output
and scratch, which the wrapper owns, so they overlap neither each other, its
inputs, nor the stack the routine reserves; its inputs may overlap. The routines need only the base AArch64 instructions. A routine returns 1 or 0,
and the wrapper returns `some` or `true` where it returned 1. What a routine
leaves in its scratch buffer, which the contract leaves unspecified and rind
does not wipe, what it clears from registers, and what it may leak, are left
out.

Trusted: the restatement; that rind's `vg_*` routines are VG's at the pin,
whose instructions and relocation targets `admin/prove vg` checks along with
VG's models of the instructions they run; that the constant tables
`admin/import-vg` generates beside them are VG's at the pin, which
`admin/prove vg` checks for each table a routine reaches, byte for byte and
relocation for relocation; and VG's proofs and models.
-/

namespace rind.aarch64

open rind.spec.vgP256

/-- `vg_ec_p256_public_key`'s `publicKeyContract`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Ecdsa/AArch64/BoothVerified.lean#L49 (`booth_pk_verified`),
registered at
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/EcP256/AArch64.lean#L70. -/
@[step]
axiom vg_p256_public_key_spec (self : low.aarch64.p256_vg.P256) (d : Std.Array U8 32#usize) :
    low.aarch64.p256_vg.P256.public_key self d ⦃ r =>
      match VG.Spec.EcKey.publicKey C (ofBytes (vgBytes d)) with
      | some (.affine x y) => ∃ out, r = some out ∧ vgBytes out = VG.Spec.EcKey.encodePoint (.affine x y)
      | _ => r = none ⦄

/-- `vg_ecdh_p256`'s `exchangeContract`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/P256/EcdhJac/Verified.lean#L310 (`verified`),
registered at
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/EcdhP256/AArch64.lean#L114. -/
@[step]
axiom vg_p256_ecdh_spec (self : low.aarch64.p256_vg.P256) (d : Std.Array U8 32#usize)
    (peer : Std.Array U8 65#usize) :
    low.aarch64.p256_vg.P256.ecdh self d peer ⦃ r =>
      match VG.Spec.Ecdh.exchange C (ofBytes (vgBytes d)) (vgBytes peer) with
      | some z => ∃ out, r = some out ∧ vgBytes out = z
      | none => r = none ⦄

/-- `vg_ecdsa_p256_verify`'s `verifyHashContract`, for a 32-byte hash:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/AllocatedVerified.lean#L200 (`allocatedVerifyHash_verified`),
registered at
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/EcdsaP256/AArch64.lean#L168. -/
@[step]
axiom vg_p256_verify_spec (self : low.aarch64.p256_vg.P256) (pub : Std.Array U8 65#usize)
    (e : Std.Array U8 32#usize) (sig : Std.Array U8 64#usize) :
    low.aarch64.p256_vg.P256.verify self pub e sig ⦃ b =>
      b = VG.Spec.Ecdsa.verify C (vgBytes pub) (VG.Spec.Ecdsa.hashToInt C (vgBytes e)) (vgBytes sig) ⦄

end rind.aarch64
