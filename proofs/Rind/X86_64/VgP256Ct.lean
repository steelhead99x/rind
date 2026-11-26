import Cosim.Progs
import VerifiedGarbage.Spec.Ecdh.P256
import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.TCB.X86_64.Target

/-!
# The leakage of VG's P-256 ECDH with AVX512_IFMA on x86_64

On a CPU with AVX512_IFMA, rind's x86_64 P-256 ECDH runs
pyca/verified-garbage's (VG's) `vg_ecdh_p256_ifma`. `Rind.X86_64.VgP256`
restates what it returns. This axiom states the other half of VG's
`Verified`: that its leakage trace, its addresses and branches, depends only
on what its contract declares public, the peer's public key
(`VG.ConstantTime`, in the vendored `VerifiedGarbage/TCB/Code.lean`). It says
nothing about rind's Rust wrapper.

The code is `Cosim.Progs.ecdhP256Ifma`: VG's `Impl.Ecdh.X86_64.exchangeP256Ifma`
with the clearing `Impl.Scrub.X86_64.scrub` that VG's registration
(`Artifacts/EcdhP256/X86_64.lean`, `withScrubAllM`) adds, written out with the
arguments its `withScrubAllF` computes for this code. `vg-print x86_64` and
`admin/vg-bytes --progs` check that its text, and that of the two functions it
calls, is VG's assembly of `vg_ecdh_p256_ifma` line for line, and rind's
machine code is checked against that text, so the link from `Prog` to bytes
rests on VG's printer and encoder, as for aarch64 ChaCha20-Poly1305.
-/

namespace rind.x86_64

open VG VG.Spec.Ecdh.Instance

/-- `vg_ecdh_p256_ifma` is constant time under `exchangeContract` for its
16 bytes of stack, whose public data are the peer's public key: the
registration's `Verified`, second conjunct, which `withScrubAllF` proves
(`Verified.scrubM`) from `ecdh_verified_ifma`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/EcdhP256/X86_64.lean#L96-L100
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Ecdh/X86_64/VerifiedIfma.lean#L218 -/
axiom vg_ecdh_p256_ifma_ct :
    ConstantTime X86_64.isa (exchangeContract Spec.EcKey.P256.inst X86_64.abi 16).pre
      (exchangeContract Spec.EcKey.P256.inst X86_64.abi 16).pub Cosim.Progs.ecdhP256Ifma

end rind.x86_64
