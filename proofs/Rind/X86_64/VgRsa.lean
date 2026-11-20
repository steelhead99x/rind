import Rind.X86_64.Funs
import Rind.Spec
import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
open Aeneas Aeneas.Std Result rind.spec

/-!
# pyca/verified-garbage's AVX-512 IFMA RSA routines on x86_64

Each axiom restates one of pyca/verified-garbage's (VG's) Lean theorems, at
the revision `admin/import-vg` pins (0aa40d6c), about the opaque Rust wrapper
in `low::x86_64::rsa_ifma` that sizes the routine's scratch and calls it.
VG's theorem is about its model of the routine's machine code, which
`admin/prove vg` cosimulates against the CPU, and the axiom states its
postcondition over the wrapper's arguments and result, as bytes and words of
`VG.Spec.Rsa`, whose definitions `admin/import-vg-models` vendors byte for
byte. The theorem's preconditions hold for every call from safe Rust: its
buffers are distinct objects, none overlapping another or the stack below the
return address, and the wrapper's token proves the CPU features. Those on the
lengths are the axiom's hypotheses.

The routines are VG's internal functions, which its padding schemes call, so
their contracts are in VG's proofs rather than its trusted `Spec`. The
restatement, and that the wrapper passes the arguments the contract names,
are trusted.
-/

namespace rind.x86_64

/-- `VG.Spec.Rsa.written`, of a routine returning `r`, 1 or 0, and leaving
`out`: the result, or zeros. -/
def Written (k : Nat) (r : Bool) (out : List U8) : Option (List VG.Byte) → Prop
  | some y => r = true ∧ out.map (·.bv) = y
  | none => r = false ∧ out.map (·.bv) = List.replicate k 0

/-- `checked_correct`, VG's registration's `ok` for
`vg_rsa_public_precomputed_checked_ifma`, against `pdChkContract`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Variants/RsaPublicPrecomputed/X86_64/Ifma.lean#L31
and
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Rsa/X86_64/PubChecked.lean#L42

For the `k`-byte `out` and `x`, `pre`, and `e`, which `pdContract`'s
precondition bounds: if `pre` holds `VG.Spec.Rsa.publicPrecompute`'s words
of a modulus `nB`, the routine returns 1 and writes
`VG.Spec.Rsa.publicOpChecked nB e x`, or returns 0 and writes zeros where
that is `none`. -/
@[step]
axiom rsa_ifma_public_spec (self : low.x86_64.rsa_ifma.RsaIfma) (out : Slice U8) (pre : Slice U64)
    (e x : Slice U8) (hk : VG.Spec.Rsa.lenValid out.length)
    (hpre : pre.length = VG.Spec.Rsa.precomputedWords out.length) (hx : x.length = out.length)
    (he1 : 1 ≤ e.length) (hek : e.length ≤ out.length) :
    low.x86_64.rsa_ifma.RsaIfma.public self out pre e x ⦃ r =>
      ∀ nB : List VG.Byte, nB.length = out.length →
        VG.Spec.Rsa.publicPrecompute nB = some (pre.val.map (·.bv)) →
        Written out.length r.1 r.2.val
          (VG.Spec.Rsa.publicOpChecked nB (e.val.map (·.bv)) (x.val.map (·.bv))) ⦄

/-- `codeP_inlined` through `crtP_call_ok`, VG's registrations' `okP` for
`vg_rsa_private_crt_precomputed_ifma` and `vg_rsa_private_crt_precomputed_ifma512`,
against `crtContractP`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Variants/RsaPrivateCrt/X86_64/Ifma.lean#L169
and
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/Bignum/X86_64/CrtContract.lean#L88

`IfmaCrt::crt` passes the routine the modulus `n`, its first `2w` words of
`pre`, as its `k = ⌈n.size / 8⌉` big-endian bytes, `p` and `q`, its first
`w` words of each, as `8w` big-endian bytes, and the first `6w` words of
`pre`, on a CPU whose check passes. If those words are
`VG.Spec.Rsa.privatePrecompute`'s of `n`, `p`, and `q`, the routine returns 1
and writes `VG.Spec.Rsa.privateCrt`, or returns 0 and writes zeros where that
is `none`. -/
@[step]
axiom ifma_crt_spec (self : low.x86_64.rsa_ifma.IfmaCrt) (out x dp dq qinv : Slice U8)
    (t : low.x86_64.cpu.HaveAvx512ForRsa) (hcpu : low.x86_64.cpu.HaveAvx512ForRsa.check = ok (some t))
    (hw : 1 ≤ self.w.val ∧ self.w.val ≤ 32)
    (hk : VG.Spec.Rsa.lenValid (((wordsNat (self.pre.val.take (2 * self.w.val))).size + 7) / 8))
    (hout : out.length = ((wordsNat (self.pre.val.take (2 * self.w.val))).size + 7) / 8)
    (hx : x.length = out.length) (hp : 8 * self.w.val < out.length)
    (hdp : dp.length = 8 * self.w.val) (hdq : dq.length = 8 * self.w.val)
    (hqinv : qinv.length = 8 * self.w.val)
    (hpre : VG.Spec.Rsa.privatePrecompute
        (VG.Spec.Rsa.i2osp (wordsNat (self.pre.val.take (2 * self.w.val))) out.length)
        (VG.Spec.Rsa.i2osp (wordsNat (self.p.val.take self.w.val)) (8 * self.w.val))
        (VG.Spec.Rsa.i2osp (wordsNat (self.q.val.take self.w.val)) (8 * self.w.val)) =
      some ((self.pre.val.take (6 * self.w.val)).map (·.bv))) :
    low.x86_64.rsa_ifma.IfmaCrt.crt self out x dp dq qinv ⦃ r =>
      Written out.length r.1 r.2.val
        (VG.Spec.Rsa.privateCrt
          (VG.Spec.Rsa.i2osp (wordsNat (self.pre.val.take (2 * self.w.val))) out.length)
          (x.val.map (·.bv))
          (VG.Spec.Rsa.i2osp (wordsNat (self.p.val.take self.w.val)) (8 * self.w.val))
          (VG.Spec.Rsa.i2osp (wordsNat (self.q.val.take self.w.val)) (8 * self.w.val))
          (dp.val.map (·.bv)) (dq.val.map (·.bv)) (qinv.val.map (·.bv))) ⦄

end rind.x86_64
