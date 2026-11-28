module

public import VerifiedGarbage.Impl.MlKem.X86_64.Encaps16

/-!
# ML-KEM on x86-64: decapsulation hashing `z ‖ c` in the matrix's fragments, with 16-bit polynomials

`kemDecapsJ16 K c p b` is the decapsulation with 16-bit polynomials, with `K̄ = J(z ‖ c)`
computed by the fragment `b` (an implementation's `Callee4.batchH16`), as
`kemEncaps16` (`Encaps16.lean`) computes `H(ek)`: after `m'` to `M`, only
`(K', r') = G(m' ‖ h)` to `G` (`hashG`); then `ρ` to `SB`, from the key's
`ek` at `dk + 384k`; the state of `J`'s sponge (SHAKE256, rate 136) at `HS`
zeroed; for each fragment `i < nb`, the 408 bytes of `pad(z ‖ c)` from
`408 i` to `HB` (`jblk`: the first from `z = dk[768k + 64 : 768k + 96]` and
`c`, the others from `c`, the last ending with the padding, suffix `0x1f`),
the seeds of entries `3i` to `3i + 3`, and `b`, which samples the first
three to `Â` while absorbing the blocks; `J(z ‖ c)` to `KB`; the remaining
entries of `Â` with the samplers `p` (`ents16`); and, if every `SampleNTT`
succeeded, the rest of the re-encryption, writing `c'` to `oCT16`, and the
choice of the key.

`J(z ‖ c)` is computed whether or not a `SampleNTT` fails, and before the
re-encryption. `z ‖ c` has as many blocks as `pad(ek)`
for both parameter sets (9 and 12), so as many fragments (`Encaps.nb`).
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace DecapsJ16

open Encaps16 (oHS oHB hzero padTail)

variable (K : Kem16)

/-- The length of `z ‖ c`. -/
def jLen : Nat := 32 + K.L.ctLen

/-- `(K', r') = G(m' ‖ h)` to `G`, with `h = dk[768k + 32 : 768k + 64]`. -/
def hashG : Prog isa := hashAt [(sc oM, 32), ((.rbp, 768 * K.L.k + 32), 32)] 72 6 (sc oG) 64

/-- Bytes `408 i` to `408 i + 407` of `pad(z ‖ c)` to `HB`: `z` and the
first 376 bytes of `c` for the first, and otherwise from `c` (byte
`408 i - 32` on), the last followed by the padding. -/
def jblk (i : Nat) : Prog isa :=
  if i = 0 then .seq (copy (sc (oHB K)) (.rbp, 768 * K.L.k + 64) 32) (copy (sc (oHB K + 32)) (.r14, 0) 376)
  else if 408 * i + 408 ≤ jLen K then copy (sc (oHB K)) (.r14, 408 * i - 32) 408
  else .seq (copy (sc (oHB K)) (.r14, 408 * i - 32) (jLen K - 408 * i)) (.block (padTail K (jLen K - 408 * i) 0x1f))

/-- Fragment `i`: its blocks of `pad(z ‖ c)`, the seeds of entries `3i` to
`3i + 3`, and `b`, which samples entries `3i` to `3i + 2`. -/
def frag (b : Prog isa) (i : Nat) : Prog isa :=
  .seq (jblk K i) (.seq (seedAt 0 ((3 * i) / K.L.k) ((3 * i) % K.L.k))
    (.seq (seedAt 1 ((3 * i + 1) / K.L.k) ((3 * i + 1) % K.L.k))
      (.seq (seedAt 2 ((3 * i + 2) / K.L.k) ((3 * i + 2) % K.L.k))
        (.seq (seedAt 3 ((3 * i + 3) / K.L.k) ((3 * i + 3) % K.L.k))
          (Encaps.sampleHAt b (Top16.aP K (3 * i)) (sc K.oW))))))

/-- `ρ` to `SB`, `Â`, and `J(z ‖ c)` to `KB`. -/
def matJ (p : String × Prog isa) (b : Prog isa) : Prog isa :=
  .seq (copy (sc oSB) (.rbp, 384 * K.L.k + 384 * K.L.k) 32) (.seq (.block (hzero K)) (.seq (seqR (frag K b) 0 (Encaps.nb K.L))
    (.seq (copy (sc oKB) (sc (oHS K)) 32)
      (ents16 p K.L.k K.oA (sc K.oW) (3 * Encaps.nb K.L) (K.L.k * K.L.k - 3 * Encaps.nb K.L)))))

end DecapsJ16

open Decaps DecapsJ16 in
/-- The decapsulation of the parameter set of `K`, hashing `z ‖ c` in the
matrix's fragments, with 16-bit polynomials, with the samplers `p` and the
fragment `b` of the implementation `c`. -/
def kemDecapsJ16 (K : Kem16) (c : Callee4) (p : String × Prog isa) (b : Prog isa) : Prog isa :=
  .seq (.block pro) (.seq (K.L.kpkeDecAt (sc oM) (.rbp, 0) (.r14, 0) (sc K.oZ)) (.seq (hashG K)
    (.seq (matJ K p b) (.seq (ifOk (Top16.encRest K c (.rbp, 384 * K.L.k) (sc oCT16)))
      (.seq (selectAt oCT16 K.L.ctLen) (.block topEpi))))))

/-- The decapsulation of an implementation of `vg_mlkem_sample_ntt4`: with
16-bit polynomials, hashing `z ‖ c` in the matrix's fragments, if it has a
16-bit sampler and a fragment sampling them (`Callee4.s16`,
`Callee4.batchH16`), with polynomials of `u32`s otherwise. -/
def kemDecapsSel (K : Kem16) (c : Callee4) : Prog isa :=
  match c.s16, c.batchH16 with
  | some p, some b => kemDecapsJ16 K c p b
  | _, _ => kemDecaps K.L c

/-- `vg_mlkem768_decaps`. -/
abbrev decaps (c : Callee4) : Prog isa := kemDecapsSel kem768w c

end VG.Impl.MlKem.X86_64
