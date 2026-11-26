import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
import VerifiedGarbage.Impl.Ecdh.P256.X86_64.Ifma
import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.TCB.AArch64.Target

/-!
# The code of VG's routines that rind states leakage axioms about

Each is the `Prog` pyca/verified-garbage's (VG's) registration builds the
function from, written as its `Artifacts/<Routine>/<Arch>.lean` writes it, so
that `proofs/Rind/<Arch>/Vg<Routine>Ct.lean`'s axioms are about it, and
`vg-print` prints it, for `admin/vg-bytes` to check against VG's assembly
text and rind's machine code.
-/

namespace Cosim.Progs

open VG VG.Impl

/-- `Artifacts/ChaCha20Poly1305/AArch64.lean`'s `seal`, at the SVE2 variant
`Proof.ChaCha20.AArch64.XorImpl.sve2` (its callee `XorCallee.sve2`, stitched). -/
def chacha20Poly1305SealSve2 : Prog AArch64.isa :=
  StackScratch.AArch64.withStackScratchWiped 1280 .x7 96
    (ChaCha20Poly1305.AArch64.sealCode ChaCha20.AArch64.XorCallee.sve2 true)

/-- The same file's `open_zero`, `vg_chacha20_poly1305_open`, at the same variant. -/
def chacha20Poly1305OpenSve2 : Prog AArch64.isa :=
  StackScratch.AArch64.withStackScratchWiped 1312 .x7 96
    (ChaCha20Poly1305.AArch64.openInPlace ChaCha20.AArch64.XorCallee.sve2 true)

/-- `Artifacts/EcdhP256/X86_64.lean`'s `vg_ecdh_p256_ifma`, with AVX512_IFMA. -/
def ecdhP256Ifma : Prog X86_64.isa := Ecdh.X86_64.exchangeP256Ifma

end Cosim.Progs
