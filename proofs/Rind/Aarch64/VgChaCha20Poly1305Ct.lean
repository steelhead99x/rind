import Cosim.Progs
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-!
# The leakage of VG's SVE2 ChaCha20-Poly1305 on aarch64

On a CPU with SVE2, `low::aarch64::chacha20poly1305`'s `seal` and `open` run
pyca/verified-garbage's (VG's) `vg_chacha20_poly1305_seal_sve2` and
`vg_chacha20_poly1305_open_sve2`. `Rind.Aarch64.VgChaCha20Poly1305` restates
what they return. These two axioms state the other half of VG's `Verified`:
that each routine's leakage trace, its addresses and branches, depends only
on what its contract declares public (`VG.ConstantTime`, which VG's
`VG.Verified` is made of, in the vendored `VerifiedGarbage/TCB/Code.lean`,
over the vendored `VerifiedGarbage/TCB/Artifact.lean`'s `Sig.contract`).
Each says nothing about rind's Rust wrapper.

The code is VG's own term, `VG.Impl.*` as `admin/import-vg-models` vendors
it, written as `Cosim/Progs.lean` writes the `Prog` VG registers: its `Artifacts/ChaCha20Poly1305/AArch64.lean`
builds `seal` as `withStackScratchWiped 1280 .x7 96 (sealCode v.callee
v.stitched)` and `open` as `withStackScratchWiped 1312 .x7 96 (openInPlace
v.callee v.stitched)`, at the variant `Proof.ChaCha20.AArch64.XorImpl.sve2`,
whose callee is `XorCallee.sve2` and which is stitched. The contracts are
`Spec.ChaCha20Poly1305.sealContract` and `openZeroContract` for the stack
that code uses, which VG's `seal_framed` and `open_framed` prove them for.

What these rest on: VG's Lean proof, and that rind's object code is that
`Prog`. `admin/vg-bytes` checks rind's bytes against VG's printed assembly
of the same `Prog`, so the link from `Prog` to bytes rests on VG's printer
and encoder (`TCB/AArch64/Print.lean`, `Encode.lean`), which are vendored and
in the trusted base: `admin/prove vg` checks the model of each instruction
against the CPU, not that the printer prints what a `Prog` is.
-/

namespace rind.aarch64

open VG VG.Spec.ChaCha20Poly1305

/-- `vg_chacha20_poly1305_seal_sve2` is constant time under `sealContract`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20Poly1305/AArch64/Verified.lean#L2641
(`seal_framed`, its second conjunct, at the SVE2 variant). -/
axiom vg_chacha20_poly1305_seal_sve2_ct :
    ConstantTime AArch64.isa (sealContract AArch64.abi 1280).pre (sealContract AArch64.abi 1280).pub
      Cosim.Progs.chacha20Poly1305SealSve2

/-- `vg_chacha20_poly1305_open_sve2` is constant time under `openZeroContract`,
whose public data include whether it returns 1 (`openLeak`):
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/ChaCha20Poly1305/AArch64/Verified.lean#L2658
(`open_framed`, its second conjunct, at the SVE2 variant). -/
axiom vg_chacha20_poly1305_open_sve2_ct :
    ConstantTime AArch64.isa (openZeroContract AArch64.abi 1312).pre (openZeroContract AArch64.abi 1312).pub
      Cosim.Progs.chacha20Poly1305OpenSve2

end rind.aarch64
