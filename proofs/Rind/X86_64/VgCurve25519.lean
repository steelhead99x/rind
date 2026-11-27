import Rind.X86_64.Funs
import Rind.VgCurve25519
import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Spec.Ed25519.KeyPair
import VerifiedGarbage.Spec.Ed25519.ExpandedSign
open Aeneas Aeneas.Std Result rind.spec

/-!
# pyca/verified-garbage's AVX-512 IFMA X25519 and Ed25519 on x86_64

Each axiom restates one of pyca/verified-garbage's (VG's) Lean theorems, at
the revision `admin/import-vg` pins (0aa40d6c), about the opaque Rust wrapper
in `low::x86_64::curve25519_ifma` that calls the routine, which
`Curve25519Ifma::check` constructs only on a CPU with the features it runs
on. VG's theorem is about its model of the routine's machine code, which
`admin/prove vg` cosimulates against the CPU, and the axiom states the
contract's postcondition (`Spec/X25519/Contract.lean`,
`Spec/Ed25519/KeyPair.lean`, `Spec/Ed25519/ExpandedSign.lean`,
`Spec/Ed25519/Contract.lean`, which `admin/import-vg-models` vendors with the
specs they state) over the wrapper's arguments and result: an array of `U8`
as the bytes VG reads, `bvs`, and an array of four `U64`, which x86_64 stores
little-endian, as the 32 bytes of the number it holds, `encodeLE 32`.

The contracts' preconditions on memory hold for every call from safe Rust:
each buffer is a distinct object, the scratch the wrapper's own, so none
overlaps another, the return address, or the stack below it, or wraps the
address space; and the token proves the CPU features. Signing's precondition,
that the digest and public key it takes are some seed's, is the axiom's
hypothesis. VG's wipe of its scratch, which rind keeps as `AGENTS.md` allows,
and what each routine may leak, are left out.

Trusted: each restatement, that the wrapper passes the routine its
arguments' memory, and VG's proofs and models, as `Rind.X86_64.VgRsa` lists.
-/

namespace rind.x86_64

open low.x86_64.curve25519_ifma (Curve25519Ifma)

/-- `vg_x25519_exchange_ifma`'s `exchangeContract`: it writes `X25519(k, u)`
over `res`, for the scalar `k` and u-coordinate `u` in the words' memory,
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/X25519/X86_64/Exchange.lean#L98
(`exchange_ifma`). Its return value, whether that is all zero, the wrapper
drops. -/
@[step]
axiom vg_x25519_exchange_spec (self : Curve25519Ifma) (res scalar point : Std.Array U64 4#usize) :
    Curve25519Ifma.x25519 self res scalar point ⦃ r =>
      VG.Spec.Ed25519.encodeLE 32 (wordsNat r.val) =
        VG.Spec.X25519.x25519 (VG.Spec.Ed25519.encodeLE 32 (wordsNat scalar.val))
          (VG.Spec.Ed25519.encodeLE 32 (wordsNat point.val)) ⦄

/-- `vg_x25519_base_ifma`'s `x25519BaseContract`: it writes `X25519(k, 9)`
over `res`, for the scalar `k` in the words' memory,
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/X25519/X86_64/Base/Ifma.lean#L50
(`x25519BaseIfma_verified`). -/
@[step]
axiom vg_x25519_base_spec (self : Curve25519Ifma) (res scalar : Std.Array U64 4#usize) :
    Curve25519Ifma.x25519_base self res scalar ⦃ r =>
      VG.Spec.Ed25519.encodeLE 32 (wordsNat r.val) =
        VG.Spec.X25519.x25519 (VG.Spec.Ed25519.encodeLE 32 (wordsNat scalar.val)) VG.Spec.X25519.basePoint ⦄

/-- `vg_ed25519_key_pair_avx2_ifma`'s `keyPairContract`, whose digest the
wrapper returns first and public key second,
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Ed25519/X86_64/KeyPair.lean#L712
(`verified`, which
[`Artifacts/Ed25519/X86_64.lean`](https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/Ed25519/X86_64.lean#L61)
registers through `keyPairWith` for the AVX2 SHA-512 and the IFMA base-point
multiplication). It holds for any seed. -/
@[step]
axiom vg_ed25519_key_pair_spec (self : Curve25519Ifma) (seed : Std.Array U8 32#usize) :
    Curve25519Ifma.ed25519_key_pair self seed ⦃ r =>
      bvs r.1.val = VG.Spec.Sha512.sha512 (bvs seed.val) ∧
        bvs r.2.val = VG.Spec.Ed25519.publicKey (bvs seed.val) ⦄

/-- `vg_ed25519_sign_expanded_avx2_ifma`'s `signExpandedContract`, for a
digest `expanded` and public key `pk` some 32-byte seed's, as its
precondition asks,
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Ed25519/X86_64/SignCached/Expanded.lean#L360
(`verifiedE`, which `signExpandedWith` registers). -/
@[step]
axiom vg_ed25519_sign_spec (self : Curve25519Ifma) (expanded : Std.Array U8 64#usize)
    (pk : Std.Array U8 32#usize) (msg : Slice U8)
    (hpre : ∃ seed : List VG.Byte, seed.length = 32 ∧ bvs expanded.val = VG.Spec.Sha512.sha512 seed ∧
      bvs pk.val = VG.Spec.Ed25519.publicKey seed) :
    Curve25519Ifma.ed25519_sign self expanded pk msg ⦃ sig =>
      ∀ seed : List VG.Byte, seed.length = 32 → bvs expanded.val = VG.Spec.Sha512.sha512 seed →
        bvs sig.val = VG.Spec.Ed25519.sign seed (bvs msg.val) ⦄

/-- `vg_ed25519_verify_avx2_ifma`'s `verifyContract`, whose 1 the wrapper
returns as `true`,
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Ed25519/X86_64/VerifyMessage/Verified.lean#L134
(`verified`, which `verifyWith` registers). It holds for any key, message,
and signature. -/
@[step]
axiom vg_ed25519_verify_spec (self : Curve25519Ifma) (pk : Std.Array U8 32#usize) (msg : Slice U8)
    (sig : Std.Array U8 64#usize) :
    Curve25519Ifma.ed25519_verify self pk msg sig ⦃ b =>
      b = VG.Spec.Ed25519.verify (bvs pk.val) (bvs msg.val) (bvs sig.val) ⦄

end rind.x86_64
