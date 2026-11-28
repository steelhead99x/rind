import VerifiedGarbage.Impl.Ecdh.P256.X86_64.Ifma
import VerifiedGarbage.Impl.Scrub.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr

/-!
# The code of VG's x86_64 routines that rind states leakage axioms about

Each is the `Prog` pyca/verified-garbage's (VG's) registration builds the
function from, written as its `Artifacts/<Routine>/X86_64.lean` writes it, so
that `proofs/Rind/X86_64/Vg<Routine>Ct.lean`'s axioms are about it, and
`vg-print x86_64` prints it, for `admin/vg-bytes` to check against VG's
assembly text and rind's machine code.
-/

namespace Cosim.Progs

open VG VG.Impl VG.Impl.Scrub.X86_64

/-- `Artifacts/EcdhP256/X86_64.lean`'s `vg_ecdh_p256_ifma`, with AVX512_IFMA:
`exchangeP256Ifma`, then the clearing `withScrubAllM` adds. Where its side
conditions hold, as `vg-print` finds they do for this code (it prints VG's
assembly), that is `withScrubAllF`'s `scrubRegF`, whose arguments are
computed here by VG's own functions from the code and its 16 bytes of
stack, as `withScrubAllF` computes them (`Proof/Framework/X86_64/ScrubOr.lean`):
the level `levelForE`, every granule of the stack (`Scrub.allKs`), and the
registers `xsOf`, `psOf` and `gsOf Taint.clobbers`, with MXCSR's flags left
(`f := .avx`). The result width, 32 bits, is `exchangeApi`'s. -/
def ecdhP256Ifma : Prog X86_64.isa :=
  let code := Ecdh.X86_64.exchangeP256Ifma
  let cs := chunks 16
  let ks := X86_64.Scrub.allKs cs
  scrub (X86_64.RScrub.levelForE code) 32 (xsOf code ks) (psOf ks)
    (gsOf X86_64.Taint.clobbers code) ks cs code (f := .avx)

end Cosim.Progs
