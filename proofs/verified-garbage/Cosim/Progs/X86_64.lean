import VerifiedGarbage.Impl.Ecdh.P256.X86_64.Ifma
import VerifiedGarbage.Impl.Scrub.X86_64

/-!
# The code of VG's x86_64 routines that rind states leakage axioms about

Each is the `Prog` pyca/verified-garbage's (VG's) registration builds the
function from, written as its `Artifacts/<Routine>/X86_64.lean` writes it, so
that `proofs/Rind/X86_64/Vg<Routine>Ct.lean`'s axioms are about it, and
`vg-print x86_64` prints it, for `admin/vg-bytes` to check against VG's
assembly text and rind's machine code.
-/

namespace Cosim.Progs

open VG VG.Impl

/-- `Artifacts/EcdhP256/X86_64.lean`'s `vg_ecdh_p256_ifma`, with AVX512_IFMA:
`exchangeP256Ifma`, then the clearing `withScrubAllM` adds, whose arguments
`withScrubAllF` computes for this code (`Proof/Framework/X86_64/ScrubOr.lean`):
at level `evex`, a 32-bit result, every SSE register (the code writes vector
registers), `r11` and every scratch register, and its 16 bytes of stack, in one
store at offset 0, with MXCSR's flags left (`f := .avx`), as its code leaves the
same MXCSR in two runs. `vg-print` checks it prints as VG's assembly. -/
def ecdhP256Ifma : Prog X86_64.isa :=
  Scrub.X86_64.scrub .evex 32 Scrub.X86_64.xregs [.r11] Scrub.X86_64.scratchRegs [0] [16]
    Ecdh.X86_64.exchangeP256Ifma (f := .avx)

end Cosim.Progs
