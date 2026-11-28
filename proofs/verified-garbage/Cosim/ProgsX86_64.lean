import VerifiedGarbage.Impl.MlKem.X86_64.Wipe
import VerifiedGarbage.Impl.Scrub.X86_64
import VerifiedGarbage.Impl.Zeroize.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.ScrubChecks
import VerifiedGarbage.Spec.MlKem.Contract
import VerifiedGarbage.Spec.MlKem.EncapsH
import VerifiedGarbage.TCB.X86_64.Target

/-!
# The code of VG's x86_64 routines that rind states leakage axioms about

As `Cosim/Progs.lean`, for x86_64: each is the `Prog` pyca/verified-garbage's
(VG's) `Artifacts/MlKem/X86_64.lean` registers a function as, at the
implementation of `vg_mlkem_sample_ntt4` with AVX-512 (`Callee4.avx512`,
`Sample4Impl.avx512`) and the AVX implementation of `vg_zeroize`
(`vg_zeroize_avx_core`), the one pair `Wipe.skip` leaves for it.

The registration is `RScrub.withScrubAllM` of the function that calls the
body and wipes its scratch (`Impl.MlKem.X86_64.keyGenW` and the others). That
takes `scrubRegF`'s branch for code that leaves the same MXCSR in two runs
along one trace, as these do (the code writes `zmm16` to `zmm31`, so the
level `evex`, and `mxFix`'s level `avx`): `scrub v retBits (xsOf code ks)
(psOf ks) (gsOf Taint.clobbers code) ks (chunks stack) code .avx` with
every granule of the 56 bytes of stack in `ks` (`Scrub.allKs`). Which branch
`withScrubAllM` takes is decided where VG's emitter evaluates its side
conditions, not here, so `admin/vg-bytes --progs` checks the printed text of
what this writes against VG's assembly, where a different branch would show.
-/

namespace Cosim.ProgsX86_64

open VG VG.Impl.Scrub.X86_64 VG.Impl.MlKem.X86_64

/-- `Proof.Framework.X86_64.Scrub.allKs`: every 16-byte granule of the
stack's chunks, as an offset from the bottom of the wiped stack. -/
def allKs : List Nat → List Nat
  | [] => []
  | b :: bs => bs.sum :: ((List.range (b / 16)).map fun t => bs.sum + b % 16 + 16 * t) ++ allKs bs

/-- `RScrub.scrubRegF`'s code at the level `evex`, at the stack of
`stack` bytes with every granule wiped, for a function whose contract has
the result `retBits` bits wide. -/
def scrubbed (retBits stack : Nat) (code : Prog VG.X86_64.isa) (v : VecLevel := .evex) :
    Prog VG.X86_64.isa :=
  let ks := allKs (chunks stack)
  scrub v retBits (xsOf code ks) (psOf ks) (gsOf VG.X86_64.Taint.clobbers code) ks (chunks stack)
    code .avx

/-- `vg_mlkem768_keygen_avx512`: `Spec.MlKem.keyGenApi.artifact` of the
registration over `keyGenW`, whose contract is `Spec.MlKem.keyGenContract
X86_64.abi 56`. -/
def keygenAvx512 : Prog VG.X86_64.isa :=
  scrubbed (Spec.MlKem.keyGenSig.retBits VG.X86_64.abi.ptrBits) 56
    (keyGenW Callee4.avx512 "_avx512" "vg_zeroize_avx_core" Impl.Zeroize.X86_64.zeroizeAvx)

/-- `vg_mlkem768_encaps_h_avx512`, whose contract is `Spec.MlKem.encapsHContract`. -/
def encapsHAvx512 : Prog VG.X86_64.isa :=
  scrubbed (Spec.MlKem.encapsHSig.retBits VG.X86_64.abi.ptrBits) 56
    (encapsHW Callee4.avx512 "_avx512" "vg_zeroize_avx_core" Impl.Zeroize.X86_64.zeroizeAvx)

/-- `vg_mlkem768_encaps_avx512`, whose contract is `Spec.MlKem.encapsContract`. -/
def encapsAvx512 : Prog VG.X86_64.isa :=
  scrubbed (Spec.MlKem.encapsSig.retBits VG.X86_64.abi.ptrBits) 56
    (encapsW Callee4.avx512 "_avx512" "vg_zeroize_avx_core" Impl.Zeroize.X86_64.zeroizeAvx)

/-- `vg_mlkem768_decaps_avx512`, whose contract is `Spec.MlKem.decapsContract`. -/
def decapsAvx512 : Prog VG.X86_64.isa :=
  scrubbed (Spec.MlKem.decapsSig.retBits VG.X86_64.abi.ptrBits) 56
    (decapsW Callee4.avx512 "_avx512" "vg_zeroize_avx_core" Impl.Zeroize.X86_64.zeroizeAvx)

/-! ## Encapsulation with the narrower implementations

The CPUs without AVX-512 run `encaps` and `encaps_h` with `Callee4.avx2` and
the AVX `vg_zeroize`, `Callee4.scalar` and the AVX one, or `Callee4.scalar`
and the scalar `vg_zeroize_core`. -/

def encapsWith (c : Callee4) (sfx zname : String) (z : Prog VG.X86_64.isa) (v : VecLevel) :
    Prog VG.X86_64.isa :=
  scrubbed (Spec.MlKem.encapsSig.retBits VG.X86_64.abi.ptrBits) 56 (encapsW c sfx zname z) v

def encapsHWith (c : Callee4) (sfx zname : String) (z : Prog VG.X86_64.isa) (v : VecLevel) :
    Prog VG.X86_64.isa :=
  scrubbed (Spec.MlKem.encapsHSig.retBits VG.X86_64.abi.ptrBits) 56 (encapsHW c sfx zname z) v

def encapsAvx2 := encapsWith Callee4.avx2 "_avx2" "vg_zeroize_avx_core" Impl.Zeroize.X86_64.zeroizeAvx .avx
def encapsHAvx2 := encapsHWith Callee4.avx2 "_avx2" "vg_zeroize_avx_core" Impl.Zeroize.X86_64.zeroizeAvx .avx
def encapsAvx := encapsWith Callee4.scalar "" "vg_zeroize_avx_core" Impl.Zeroize.X86_64.zeroizeAvx .avx
def encapsHAvx := encapsHWith Callee4.scalar "" "vg_zeroize_avx_core" Impl.Zeroize.X86_64.zeroizeAvx .avx
def encapsBase := encapsWith Callee4.scalar "" "vg_zeroize_core" Impl.Zeroize.X86_64.zeroize .sse
def encapsHBase := encapsHWith Callee4.scalar "" "vg_zeroize_core" Impl.Zeroize.X86_64.zeroize .sse

end Cosim.ProgsX86_64
