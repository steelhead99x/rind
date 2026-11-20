import Cosim.ProgsX86_64
import VerifiedGarbage.Spec.MlKem.Contract
import VerifiedGarbage.Spec.MlKem.EncapsH
import VerifiedGarbage.TCB.X86_64.Target

/-!
# The leakage of VG's ML-KEM-768 on x86_64

`low::x86_64::mlkem768_vg` calls pyca/verified-garbage's (VG's) routines for
ML-KEM-768's key generation (AVX-512), encapsulation (with `H(ek)` given or
not, at the widest of AVX-512, AVX2, AVX, or neither that the CPU has), and
decapsulation (AVX-512). `Rind.X86_64.VgMlKem` restates what they return.
These axioms state the other half of VG's `Verified`: that each routine's
leakage trace, its addresses and branches, depends only on what its contract
declares public (`VG.ConstantTime`, which `VG.Verified` is made of, in the
vendored `VerifiedGarbage/TCB/Code.lean`, over the vendored
`VerifiedGarbage/TCB/Artifact.lean`'s `Sig.contract`): `ρ`, which is in the
encapsulation key, and no secret. Each says nothing about rind's Rust
wrapper, nor about what its routine returns.

The code is VG's own term, `VG.Impl.*` as `admin/import-vg-models` vendors it,
written as `Cosim/ProgsX86_64.lean` writes the `Prog` VG's
`Artifacts/MlKem/X86_64.lean` registers: the function that calls the routine's
body and wipes its scratch (`Impl.MlKem.X86_64.keyGenW` and the others) and
then `scrub`, the clearing of the registers and stack that VG's
`RScrub.withScrubAllM` appends. The contracts are `Spec.MlKem.keyGenContract`,
`encapsContract`, `encapsHContract`, and `decapsContract` of VG's x86_64
calling convention for 56 bytes of stack, which `keyGenW_verified`, `encapsW_verified`,
`encapsHW_verified`, and `decapsW_verified` prove the unscrubbed code for, and
which the scrubbed code, VG's registered one, keeps (`scrubRegF`'s
`contract := r.contract`).

What these rest on: VG's Lean proof, and that rind's object code is that
`Prog`. `admin/vg-bytes` checks rind's bytes against VG's printed assembly of
the same `Prog`, so the link from `Prog` to bytes rests on VG's printer and
encoder (`TCB/X86_64/Print.lean`, `Encode.lean`), which are vendored and in the
trusted base: `admin/prove vg` checks the model of each instruction against
the CPU, not that the printer prints what a `Prog` is. That a `Prog` written
here is the registration's, and not another with the same text, rests on that
printer being injective on it, which it is not in general (it prints `frame`
and `block` alike and loses how a block is grouped).
-/

namespace rind.x86_64

open VG VG.Spec.MlKem

/-- `vg_mlkem768_keygen_avx512` is constant time under `keyGenContract`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/MlKem/X86_64.lean#L55 (the registration, `RScrub.withScrubAllM` of the code, whose `verified` is
`Verified` of the scrubbed code, by `RScrub.scrubRegF`'s proof, https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Framework/X86_64/ScrubOr.lean#L491, or
`Scrub.withScrubAll`'s) from
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CallWipe.lean#L642 (`keyGenW_verified`). -/
axiom vg_mlkem768_keygen_avx512_ct :
    ConstantTime X86_64.isa (keyGenContract X86_64.abi 56).pre (keyGenContract X86_64.abi 56).pub
      Cosim.ProgsX86_64.keygenAvx512

/-- `vg_mlkem768_encaps_h_avx512` is constant time under `encapsHContract`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/MlKem/X86_64.lean#L61 (the registration, `RScrub.withScrubAllM` of the code, whose `verified` is
`Verified` of the scrubbed code, by `RScrub.scrubRegF`'s proof, https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Framework/X86_64/ScrubOr.lean#L491, or
`Scrub.withScrubAll`'s) from
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CallWipe.lean#L700 (`encapsHW_verified`). -/
axiom vg_mlkem768_encaps_h_avx512_ct :
    ConstantTime X86_64.isa (encapsHContract X86_64.abi 56).pre (encapsHContract X86_64.abi 56).pub
      Cosim.ProgsX86_64.encapsHAvx512

/-- `vg_mlkem768_encaps_avx512` is constant time under `encapsContract`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/MlKem/X86_64.lean#L67 (the registration, `RScrub.withScrubAllM` of the code, whose `verified` is
`Verified` of the scrubbed code, by `RScrub.scrubRegF`'s proof, https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Framework/X86_64/ScrubOr.lean#L491, or
`Scrub.withScrubAll`'s) from
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CallWipe.lean#L750 (`encapsW_verified`). -/
axiom vg_mlkem768_encaps_avx512_ct :
    ConstantTime X86_64.isa (encapsContract X86_64.abi 56).pre (encapsContract X86_64.abi 56).pub
      Cosim.ProgsX86_64.encapsAvx512

/-- `vg_mlkem768_decaps_avx512` is constant time under `decapsContract`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/MlKem/X86_64.lean#L73 (the registration, `RScrub.withScrubAllM` of the code, whose `verified` is
`Verified` of the scrubbed code, by `RScrub.scrubRegF`'s proof, https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Framework/X86_64/ScrubOr.lean#L491, or
`Scrub.withScrubAll`'s) from
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CallWipe.lean#L799 (`decapsW_verified`). -/
axiom vg_mlkem768_decaps_avx512_ct :
    ConstantTime X86_64.isa (decapsContract X86_64.abi 56).pre (decapsContract X86_64.abi 56).pub
      Cosim.ProgsX86_64.decapsAvx512

/-- `vg_mlkem768_encaps_h_avx2` is constant time under `encapsHContract`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/MlKem/X86_64.lean#L61 (the registration, `RScrub.withScrubAllM` of the code, whose `verified` is
`Verified` of the scrubbed code, by `RScrub.scrubRegF`'s proof, https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Framework/X86_64/ScrubOr.lean#L491, or
`Scrub.withScrubAll`'s) from
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CallWipe.lean#L700 (`encapsHW_verified`). -/
axiom vg_mlkem768_encaps_h_avx2_ct :
    ConstantTime X86_64.isa (encapsHContract X86_64.abi 56).pre (encapsHContract X86_64.abi 56).pub
      Cosim.ProgsX86_64.encapsHAvx2

/-- `vg_mlkem768_encaps_avx2` is constant time under `encapsContract`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/MlKem/X86_64.lean#L67 (the registration, `RScrub.withScrubAllM` of the code, whose `verified` is
`Verified` of the scrubbed code, by `RScrub.scrubRegF`'s proof, https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Framework/X86_64/ScrubOr.lean#L491, or
`Scrub.withScrubAll`'s) from
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CallWipe.lean#L750 (`encapsW_verified`). -/
axiom vg_mlkem768_encaps_avx2_ct :
    ConstantTime X86_64.isa (encapsContract X86_64.abi 56).pre (encapsContract X86_64.abi 56).pub
      Cosim.ProgsX86_64.encapsAvx2

/-- `vg_mlkem768_encaps_h_avx` is constant time under `encapsHContract`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/MlKem/X86_64.lean#L61 (the registration, `RScrub.withScrubAllM` of the code, whose `verified` is
`Verified` of the scrubbed code, by `RScrub.scrubRegF`'s proof, https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Framework/X86_64/ScrubOr.lean#L491, or
`Scrub.withScrubAll`'s) from
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CallWipe.lean#L700 (`encapsHW_verified`). -/
axiom vg_mlkem768_encaps_h_avx_ct :
    ConstantTime X86_64.isa (encapsHContract X86_64.abi 56).pre (encapsHContract X86_64.abi 56).pub
      Cosim.ProgsX86_64.encapsHAvx

/-- `vg_mlkem768_encaps_avx` is constant time under `encapsContract`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/MlKem/X86_64.lean#L67 (the registration, `RScrub.withScrubAllM` of the code, whose `verified` is
`Verified` of the scrubbed code, by `RScrub.scrubRegF`'s proof, https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Framework/X86_64/ScrubOr.lean#L491, or
`Scrub.withScrubAll`'s) from
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CallWipe.lean#L750 (`encapsW_verified`). -/
axiom vg_mlkem768_encaps_avx_ct :
    ConstantTime X86_64.isa (encapsContract X86_64.abi 56).pre (encapsContract X86_64.abi 56).pub
      Cosim.ProgsX86_64.encapsAvx

/-- `vg_mlkem768_encaps_h` is constant time under `encapsHContract`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/MlKem/X86_64.lean#L61 (the registration, `RScrub.withScrubAllM` of the code, whose `verified` is
`Verified` of the scrubbed code, by `RScrub.scrubRegF`'s proof, https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Framework/X86_64/ScrubOr.lean#L491, or
`Scrub.withScrubAll`'s) from
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CallWipe.lean#L700 (`encapsHW_verified`). -/
axiom vg_mlkem768_encaps_h_ct :
    ConstantTime X86_64.isa (encapsHContract X86_64.abi 56).pre (encapsHContract X86_64.abi 56).pub
      Cosim.ProgsX86_64.encapsHBase

/-- `vg_mlkem768_encaps` is constant time under `encapsContract`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Artifacts/MlKem/X86_64.lean#L67 (the registration, `RScrub.withScrubAllM` of the code, whose `verified` is
`Verified` of the scrubbed code, by `RScrub.scrubRegF`'s proof, https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Framework/X86_64/ScrubOr.lean#L491, or
`Scrub.withScrubAll`'s) from
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CallWipe.lean#L750 (`encapsW_verified`). -/
axiom vg_mlkem768_encaps_ct :
    ConstantTime X86_64.isa (encapsContract X86_64.abi 56).pre (encapsContract X86_64.abi 56).pub
      Cosim.ProgsX86_64.encapsBase

end rind.x86_64
