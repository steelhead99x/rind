import Rind.Aarch64.HmacApi
import Rind.VgPbkdf2
open Aeneas Aeneas.Std Result rind.spec

/-!
# pyca/verified-garbage's PBKDF2 contracts on aarch64

`low::aarch64::pbkdf2_vg::Pbkdf2::derive` calls one of four of VG's routines,
by the hash its `Pbkdf2` names: `vg_pbkdf2_hmac_sha1_sha2` and
`vg_pbkdf2_hmac_sha256_sha2` on the crypto extension, and
`vg_pbkdf2_hmac_sha384_sha512` and `vg_pbkdf2_hmac_sha512_sha512` on the
SHA-512 instructions. Each axiom below restates VG's Lean theorem about one,
its variant's `pbkdf2F`, about the wrapper with that hash, over VG's spec,
which `Rind.VgPbkdf2` proves rind's: `vg_derive_spec` states the four as RFC
8018's PBKDF2 over `Rind.Aarch64.HmacApi`'s `hmacOf`, which is what
`Rind.Aarch64.Pbkdf2Vg` proves `Secret` derives.

Trusted: each restatement, and that the wrapper passes the routine the
password's, the salt's, and the output's pointers and lengths and the
iteration count. VG's contract (`VG.Spec.Hmac.Instance.pbkdf2Contract`, at
[`Spec/Pbkdf2/Generic.lean`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Spec/Pbkdf2/Generic.lean))
takes a positive iteration count, which the wrapper's `NonZeroU32` holds and
the translation's `U32` forgets, so each axiom takes it back as `hc`; and an
output of at most `2^32 - 1` digests, which the wrapper asserts and each axiom
takes as `hl`. It also allows an empty output, which RFC 8018 §5.2 does
not, as VG's `pbkdf2Hmac` gives the empty key for it; `Key::derive` refuses
one before any call. The rest of its precondition holds for every call safe
Rust makes: the output, which the routine writes, is a `&mut` borrow distinct
from every other argument, so it overlaps neither input; no buffer, the
password, the salt, or the output, overlaps the stack below the stack
pointer that VG reserves for the routine's frames, since each is a live Rust
object the caller holds and AAPCS64 keeps those at or above the caller's
stack pointer, while the return address is in `x30`, not memory; no slice
wraps the address space; and a `Pbkdf2` naming a hash exists only once its
constructor has found the instructions that hash's routine runs. A slice's
length is its own, which no call changes.
-/

namespace rind.aarch64

/-- `vg_pbkdf2_hmac_sha1_sha2` meets `pbkdf2Contract` of `VG.Spec.Hmac.sha1I`:
`pbkdf2F` of
[`sha1Sha2`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Variants/MdHash/AArch64.lean#L26)
([`MdHash.pbkdf2F`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Pbkdf2/Md/AArch64/Variant.lean#L1106)),
which [`Artifacts/Pbkdf2Sha1/AArch64.lean`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/Pbkdf2Sha1/AArch64.lean)
registers for the code VG emits. -/
@[step]
axiom vg_pbkdf2_hmac_sha1_sha2_spec (password salt : Slice U8) (c : U32) (out : Slice U8)
    (hc : 0 < c.val) (hl : out.length ≤ (2 ^ 32 - 1) * 20) :
    low.aarch64.pbkdf2_vg.Pbkdf2.derive .Sha1 password salt c out ⦃ r =>
      r.length = out.length ∧
      VG.Spec.Pbkdf2.pbkdf2Hmac VG.Spec.Hmac.sha1S (bv password.val) (bv salt.val) c.val
        out.length = some (bv r.val) ⦄

/-- `vg_pbkdf2_hmac_sha256_sha2` meets `pbkdf2Contract` of
`VG.Spec.Hmac.sha256I`: `pbkdf2F` of
[`sha256Sha2`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Variants/MdHash/AArch64.lean#L38)
([`MdHash.pbkdf2F`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Pbkdf2/Md/AArch64/Variant.lean#L1106)),
which [`Artifacts/Pbkdf2Sha256/AArch64.lean`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/Pbkdf2Sha256/AArch64.lean)
registers for the code VG emits. -/
@[step]
axiom vg_pbkdf2_hmac_sha256_sha2_spec (password salt : Slice U8) (c : U32) (out : Slice U8)
    (hc : 0 < c.val) (hl : out.length ≤ (2 ^ 32 - 1) * 32) :
    low.aarch64.pbkdf2_vg.Pbkdf2.derive .Sha256 password salt c out ⦃ r =>
      r.length = out.length ∧
      VG.Spec.Pbkdf2.pbkdf2Hmac VG.Spec.Hmac.sha256S (bv password.val) (bv salt.val) c.val
        out.length = some (bv r.val) ⦄

/-- `vg_pbkdf2_hmac_sha384_sha512` meets `pbkdf2Contract` of
`VG.Spec.Hmac.sha384I`: `pbkdf2F` of
[`sha384Sha3`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Variants/MdHash/AArch64.lean#L43)
([`MdHash.pbkdf2F`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Pbkdf2/Md/AArch64/Variant.lean#L1106)),
which [`Artifacts/Pbkdf2Sha384/AArch64.lean`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/Pbkdf2Sha384/AArch64.lean)
registers for the code VG emits. -/
@[step]
axiom vg_pbkdf2_hmac_sha384_sha512_spec (password salt : Slice U8) (c : U32) (out : Slice U8)
    (hc : 0 < c.val) (hl : out.length ≤ (2 ^ 32 - 1) * 48) :
    low.aarch64.pbkdf2_vg.Pbkdf2.derive .Sha384 password salt c out ⦃ r =>
      r.length = out.length ∧
      VG.Spec.Pbkdf2.pbkdf2Hmac VG.Spec.Hmac.sha384S (bv password.val) (bv salt.val) c.val
        out.length = some (bv r.val) ⦄

/-- `vg_pbkdf2_hmac_sha512_sha512` meets `pbkdf2Contract` of
`VG.Spec.Hmac.sha512I`: `pbkdf2F` of
[`sha512Sha3`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Variants/MdHash/AArch64.lean#L47)
([`MdHash.pbkdf2F`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Pbkdf2/Md/AArch64/Variant.lean#L1106)),
which [`Artifacts/Pbkdf2Sha512/AArch64.lean`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/Pbkdf2Sha512/AArch64.lean)
registers for the code VG emits. -/
@[step]
axiom vg_pbkdf2_hmac_sha512_sha512_spec (password salt : Slice U8) (c : U32) (out : Slice U8)
    (hc : 0 < c.val) (hl : out.length ≤ (2 ^ 32 - 1) * 64) :
    low.aarch64.pbkdf2_vg.Pbkdf2.derive .Sha512 password salt c out ⦃ r =>
      r.length = out.length ∧
      VG.Spec.Pbkdf2.pbkdf2Hmac VG.Spec.Hmac.sha512S (bv password.val) (bv salt.val) c.val
        out.length = some (bv r.val) ⦄

/-! ## Over rind's spec -/

/-- The routine `Pbkdf2::derive` runs for each HMAC algorithm. -/
def vgHash : high.hmac.Algorithm → low.aarch64.pbkdf2_vg.Hash
  | .HMAC_SHA1 => .Sha1
  | .HMAC_SHA256 => .Sha256
  | .HMAC_SHA384 => .Sha384
  | .HMAC_SHA512 => .Sha512

/-- VG's streaming hash for each HMAC algorithm. -/
def vgS : high.hmac.Algorithm → VG.Spec.Hmac.StreamingHash
  | .HMAC_SHA1 => VG.Spec.Hmac.sha1S
  | .HMAC_SHA256 => VG.Spec.Hmac.sha256S
  | .HMAC_SHA384 => VG.Spec.Hmac.sha384S
  | .HMAC_SHA512 => VG.Spec.Hmac.sha512S

theorem bv_ofBv (m : List Byte) : bv (ofBv m) = m := by
  simp [bv, ofBv, List.map_map, Function.comp_def]

theorem sha384Bytes_eq : VG.Spec.Sha512.sha384 = sha384Bytes := by
  funext m
  conv_lhs => rw [← bv_ofBv m]
  rw [sha384Bytes, bv, vg.sha384_eq, bv]

theorem sha512Bytes_eq : VG.Spec.Sha512.sha512 = sha512Bytes := by
  funext m
  conv_lhs => rw [← bv_ofBv m]
  rw [sha512Bytes, bv, vg.sha512_eq, bv]

theorem vgS_H (a : high.hmac.Algorithm) : (vgS a).H = ⟨hmacBlock a, hmacHash a⟩ := by
  cases a <;> simp only [vgS, VG.Spec.Hmac.sha1S, VG.Spec.Hmac.sha256S, VG.Spec.Hmac.sha384S,
    VG.Spec.Hmac.sha512S, VG.Spec.Hmac.sha1, VG.Spec.Hmac.sha256, VG.Spec.Hmac.sha384,
    VG.Spec.Hmac.sha512, hmacBlock, hmacHash, sha384Bytes_eq, sha512Bytes_eq]
  · rw [show VG.Spec.Sha1.hash = sha1.hash from funext vg.sha1_eq]
  · rw [show VG.Spec.Sha256.hash = sha256.hash from funext vg.sha256_eq]

theorem vgS_digestBytes (a : high.hmac.Algorithm) : (vgS a).digestBytes = tagLen a := by
  cases a <;> rfl

/-- VG's PBKDF2 under `a`'s hash is rind's, for an output it accepts. -/
theorem pbkdf2Hmac_eq (a : high.hmac.Algorithm) (P S : List Byte) (c L : Nat)
    (hL : L ≤ (2 ^ 32 - 1) * tagLen a) :
    VG.Spec.Pbkdf2.pbkdf2Hmac (vgS a) P S c L = some (pbkdf2 (hmacOf a) (tagLen a) P S c L) := by
  have hprf : VG.Spec.Hmac.hmac (vgS a).H = hmacOf a := by
    funext key text
    rw [vgS_H, vg.hmac_eq, hmacOf]
  rw [VG.Spec.Pbkdf2.pbkdf2Hmac, hprf, vgS_digestBytes, vg.pbkdf2_eq]
  simp only [show ¬ (2 ^ 32 - 1) * tagLen a < L by omega, ite_false]

/-- `Pbkdf2::derive` with `a`'s routine writes RFC 8018's PBKDF2 under HMAC
with `a`'s hash, and nothing for an empty output, which VG's contract allows
and RFC 8018 does not. -/
theorem vg_derive_spec (a : high.hmac.Algorithm) (password salt : Slice U8) (c : U32)
    (out : Slice U8) (hc : 0 < c.val) (hl : out.length ≤ (2 ^ 32 - 1) * tagLen a) :
    low.aarch64.pbkdf2_vg.Pbkdf2.derive (vgHash a) password salt c out ⦃ r =>
      r.length = out.length ∧
      bv r.val = pbkdf2 (hmacOf a) (tagLen a) (bv password.val) (bv salt.val) c.val out.length ⦄ := by
  have h : ∀ r : Slice U8,
      VG.Spec.Pbkdf2.pbkdf2Hmac (vgS a) (bv password.val) (bv salt.val) c.val out.length =
        some (bv r.val) →
      bv r.val = pbkdf2 (hmacOf a) (tagLen a) (bv password.val) (bv salt.val) c.val
        out.length := by
    intro r hr
    rw [pbkdf2Hmac_eq a _ _ _ _ hl] at hr
    exact (Option.some.inj hr).symm
  cases a
  · exact WP.spec_mono (vg_pbkdf2_hmac_sha1_sha2_spec password salt c out hc hl)
      fun r hr => ⟨hr.1, h r hr.2⟩
  · exact WP.spec_mono (vg_pbkdf2_hmac_sha256_sha2_spec password salt c out hc hl)
      fun r hr => ⟨hr.1, h r hr.2⟩
  · exact WP.spec_mono (vg_pbkdf2_hmac_sha384_sha512_spec password salt c out hc hl)
      fun r hr => ⟨hr.1, h r hr.2⟩
  · exact WP.spec_mono (vg_pbkdf2_hmac_sha512_sha512_spec password salt c out hc hl)
      fun r hr => ⟨hr.1, h r hr.2⟩

end rind.aarch64
