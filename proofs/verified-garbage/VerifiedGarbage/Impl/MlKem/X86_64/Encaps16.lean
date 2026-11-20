module

public import VerifiedGarbage.Impl.MlKem.X86_64.Kem16
public import VerifiedGarbage.Impl.MlKem.X86_64.Encaps

/-!
# ML-KEM on x86-64: encapsulation hashing the key, with 16-bit polynomials

`kemEncaps16 K c p b` is `kemEncaps` (`Encaps.lean`) with the fragment `b`
(an implementation's `Callee4.batchH16`), for the layout `K` (`Kem16.lean`):
`ρ` to `SB`; the state of `H`'s sponge at `HS` zeroed, in the working space
`W` of the samplers (from `oW`); for each fragment `i < nb`, the 408 bytes
of `pad(ek)` from `408 i` to `HB` (in `W`), the seeds of entries `3i` to
`3i + 3`, and `b`, which samples the first three, as 16-bit polynomials, to
`Â` (from `oA`) while absorbing the blocks; then `H(ek)` to `H`, the
remaining entries of `Â` with the samplers `p` (`ents16`), `G(m ‖ H(ek))`
(`EncapsH.hashes`), and, if every `SampleNTT` succeeded, the rest of
K-PKE.Encrypt, whose ciphertext goes straight to `ct`, and `K` to `key`.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace Encaps16

variable (K : Kem16)

/-- The state of `H`'s sponge and its blocks, in the samplers' working space `W`. -/
def oHS : Nat := K.oW + Sample4.oHS
def oHB : Nat := K.oW + Sample4.oHB

/-- The sponge's state zeroed. -/
def hzero : List Instr := .mov32 .rax (.imm 0) :: zeroSt .rbx (oHS K)

/-- The rest of the last 408 bytes of `pad(ek)`, after the `len` bytes of
`ek`: zeros, and the suffix (SHA3's `0x06`, or `d`) and the last bit of the padding. -/
def padTail (len : Nat) (d : Nat := 6) : List Instr :=
  .mov32 .rax (.imm 0) :: (List.range ((408 - len) / 8)).flatMap (fun j => [.store (at_ .rbx (oHB K + len + 8 * j)) .rax]) ++
    setB (sc (oHB K + len)) d ++ setB (sc (oHB K + 407)) 0x80

/-- Bytes `408 i` to `408 i + 407` of `pad(ek)` to `HB`. -/
def hblk (i : Nat) : Prog isa :=
  if 408 * i + 408 ≤ K.L.ekLen then copy (sc (oHB K)) (.r14, 408 * i) 408
  else .seq (copy (sc (oHB K)) (.r14, 408 * i) (K.L.ekLen - 408 * i)) (.block (padTail K (K.L.ekLen - 408 * i)))

/-- Fragment `i`: its blocks of `pad(ek)`, the seeds of entries `3i` to
`3i + 3`, and `b`, which samples entries `3i` to `3i + 2`. -/
def frag (b : Prog isa) (i : Nat) : Prog isa :=
  .seq (hblk K i) (.seq (seedAt 0 ((3 * i) / K.L.k) ((3 * i) % K.L.k))
    (.seq (seedAt 1 ((3 * i + 1) / K.L.k) ((3 * i + 1) % K.L.k))
      (.seq (seedAt 2 ((3 * i + 2) / K.L.k) ((3 * i + 2) % K.L.k))
        (.seq (seedAt 3 ((3 * i + 3) / K.L.k) ((3 * i + 3) % K.L.k))
          (Encaps.sampleHAt b (Top16.aP K (3 * i)) (sc K.oW))))))

/-- `ρ` to `SB`, `Â` and `H(ek)` to `H`. -/
def matH (p : String × Prog isa) (b : Prog isa) : Prog isa :=
  .seq (copy (sc oSB) (.r14, 384 * K.L.k) 32) (.seq (.block (hzero K)) (.seq (seqR (frag K b) 0 (Encaps.nb K.L))
    (.seq (copy (sc oH) (sc (oHS K)) 32)
      (ents16 p K.L.k K.oA (sc K.oW) (3 * Encaps.nb K.L) (K.L.k * K.L.k - 3 * Encaps.nb K.L)))))

end Encaps16

open Encaps16 in
/-- The encapsulation of the parameter set of `K`, hashing the key, with
16-bit polynomials, with the samplers `p` and the fragment `b` of the
implementation `c`: the ciphertext straight to `ct`. -/
def kemEncaps16 (K : Kem16) (c : Callee4) (p : String × Prog isa) (b : Prog isa) : Prog isa :=
  .seq (.block Encaps.pro) (.seq (matH K p b) (.seq EncapsH.hashes
    (.seq (ifOk (Top16.encRest K c (.r14, 0) (.r13, 0))) (.seq (copy (.r12, 0) (sc oG) 32) (.block topEpi)))))

/-- The encapsulation (hashing the key) of an implementation of
`vg_mlkem_sample_ntt4`: with 16-bit polynomials if it has a 16-bit sampler
and a fragment sampling them (`Callee4.s16`, `Callee4.batchH16`), with
polynomials of `u32`s otherwise. -/
def kemEncapsSel (K : Kem16) (c : Callee4) : Prog isa :=
  match c.s16, c.batchH16 with
  | some p, some b => kemEncaps16 K c p b
  | _, _ => kemEncaps K.L c

/-- `vg_mlkem768_encaps`. -/
abbrev encaps (c : Callee4) : Prog isa := kemEncapsSel kem768w c

end VG.Impl.MlKem.X86_64
