module

public import VerifiedGarbage.Impl.MlKem.X86_64.Encaps16
public import VerifiedGarbage.Impl.MlKem.X86_64.KpkeKgRows

/-!
# ML-KEM-768 on x86-64: key generation hashing `ek` while it samples `Â`

`kemKeyGenH16 K c b` is `kemKeyGen16` (`Kem16.lean`) with the rows of `t̂`
encoded to `ek` as soon as `Â` has them, and `H(ek)` absorbed into the
fourth Keccak state of the matrix's samplers (the fragment `b`, an
implementation's `Callee4.batchHM16`, as encapsulation's `sampleH` does)
as `ek` grows:

1. the prologue, `(ρ, σ) = G(d ‖ k)` and `ρ` to `SB` (`gRho`);
2. the noise, `s` and `e`, as for `kemKeyGen16`, and
   `vg_mlkem768_kpke_keygen_ntt`: `ŝ` to `SH`, `ê` to `EH` and
   `ByteEncode₁₂(ŝ)` to `dk` (`nttAt`);
3. the state of `H`'s sponge zeroed, then for each row `i < 3`: its three
   entries of `Â` with `b (hm i).1`, which absorbs blocks `(hm i).2`, … of
   `pad(ek)` (copied to `HB` first), then, if every `SampleNTT` so far
   succeeded, `vg_mlkem768_kpke_keygen_row` (`rowAt i`): row `i` of `t̂`,
   encoded to `ek`. The blocks are those of `ek` the rows before have
   written: none before row 0, blocks 0 and 1 (bytes 0 to 272) after row 0,
   and blocks 2 to 4 (to byte 680) after row 1;
4. `ρ` to `ek`, `ek` to `dk`, `H(ek)` from the sponge's state (the last
   504 bytes of `ek` absorbed, the padding, the squeeze) to `dk`, and `z`
   to `dk` (`tail`).

The layout of `scratch` is `kem768w`'s, and `ŝ`, `ê` and the working space
of the K-PKE functions in its last 12 KiB (`oSH`, `oEH`, `oZK`), after the
samplers' working space; `PRF₂`'s outputs, which are there too, are read
before `ŝ` is written.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace KeyGenH16

variable (K : Kem16)

/-- `ŝ`, `ê` (`u32`s, 3072 bytes each) and the working space of the K-PKE
functions (4096 bytes), in `scratch`. -/
def oSH : Nat := 20480
def oEH : Nat := 23552
def oZK : Nat := 26624

/-- `vg_mlkem768_kpke_keygen_ntt(dk, SH, EH, R, ZK)`. -/
def nttAt : Prog isa := K.L.kgNttAt (.r13, 0) (sc oSH) (sc oEH) (sc K.oR) (sc oZK)

/-- `vg_mlkem768_kpke_keygen_row(ek + 384 i, Â[i], SH, EH + 1024 i, ZK)`. -/
def rowAt (i : Nat) : Prog isa :=
  K.L.kgRowAt (.r12, 384 * i) (Top16.aP K (K.L.k * i)) (sc oSH) (sc (oEH + 1024 * i)) (sc oZK)

/-- How many blocks of `pad(ek)` the fragment of row `i` absorbs, and the first. -/
def hm : Nat → Nat × Nat
  | 0 => (0, 0)
  | 1 => (2, 0)
  | _ => (3, 2)

/-- The blocks of `pad(ek)` absorbed after the rows. -/
def hDone : Nat := 5

/-- Row 0 of `Â`, with the fragment `p` (an implementation's
`Callee4.batchP16`), which samples its three entries and computes
`PRF₂(σ, 0)` and `PRF₂(σ, 1)` from `σ`, copied first to the samplers'
working space. -/
def frag0 (p : Nat → Nat → Prog isa) : Prog isa :=
  .seq (copy (sc (K.oW + Sample4.oPS)) (sc (oG + 32)) 32)
    (.seq (seedAt 0 0 0) (.seq (seedAt 1 0 1) (.seq (seedAt 2 0 2) (.seq (seedAt 3 1 0)
      (Encaps.sampleHAt (p 0 2) (Top16.aP K 0) (sc K.oW))))))

/-- Row `i` of `Â`: the blocks `(hm i).2`, … of `ek` to `HB`, the seeds of
entries `3i` to `3i + 3`, and `b (hm i).1`, which samples the first three
and absorbs the blocks. -/
def frag (b : Nat → Prog isa) (i : Nat) : Prog isa :=
  .seq (if (hm i).1 = 0 then .block [] else copy (sc (Encaps16.oHB K)) (.r12, 136 * (hm i).2) (136 * (hm i).1))
    (.seq (seedAt 0 i 0) (.seq (seedAt 1 i 1) (.seq (seedAt 2 i 2) (.seq (seedAt 3 (i + 1) 0)
      (Encaps.sampleHAt (b (hm i).1) (Top16.aP K (K.L.k * i)) (sc K.oW))))))

/-- `SamplePolyCBD₂(PRF₂(σ, N))` to polynomial `N`, for `N < 2`, from the
output of `frag0`. -/
def cbdP (A : Arith) (N : Nat) : Prog isa :=
  cbd2_16At A (sc (K.oW + Sample4.oPO + 128 * N)) (Top16.rP K N)

/-- `ρ` to `ek`, `ek` to `dk`, `H(ek)` to `dk` from the sponge's state and the
rest of `ek`, and `z` to `dk`. -/
def tail : Prog isa :=
  .seq (copy (.r12, 384 * K.L.k) (sc oG) 32) (.seq (copy (.r13, 384 * K.L.k) (.r12, 0) K.L.ekLen)
    (.seq (copy (sc 0) (sc (Encaps16.oHS K)) 200) (.seq (absAll 136 [((.r12, 136 * hDone), K.L.ekLen - 136 * hDone)] 0)
      (.seq (kpad 136 ((K.L.ekLen - 136 * hDone) % 136) 6) (.seq (ksqz 136 (.r13, 384 * K.L.k + K.L.ekLen) 32)
        (copy (.r13, 384 * K.L.k + K.L.ekLen + 32) (.rbp, 32) 32))))))

/-- Row 0, with `PRF₂(σ, 0)` and `PRF₂(σ, 1)` (`frag0 p`), the sponge's
state zeroed, the noise they give, `nttAt`, and the rows after, with the
matrix's fragments `b`, and the tail. -/
def rows (b : Nat → Prog isa) (p : Nat → Nat → Prog isa) (A : Arith) : Prog isa :=
  .seq (frag0 K p) (.seq (.block (Encaps16.hzero K)) (.seq (cbdP K A 0) (.seq (cbdP K A 1) (.seq (nttAt K)
    (.seq (ifOk (rowAt K 0)) (.seq (frag K b 1) (.seq (ifOk (rowAt K 1)) (.seq (frag K b 2)
      (ifOk (.seq (rowAt K 2) (tail K)))))))))))

end KeyGenH16

open KeyGen KeyGenH16 in
/-- ML-KEM-768's key generation with 16-bit polynomials, hashing `ek` with
the matrix's fragments `b` and computing two outputs of `PRF₂` with `p`,
of the implementation `c`: `PRF₂(σ, 2)` to `PRF₂(σ, 5)` and their
polynomials first (`c.prfs`, four at a time). -/
def kemKeyGenH16 (K : Kem16) (c : Callee4) (b : Nat → Prog isa) (p : Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block pro) (.seq (gRho K.L) (.seq (c.prfs 2 4 (K.oPR + 256) (K.oW / 32))
    (.seq (seqR (Top16.cbdN K c.arith) 2 4) (.seq (rows K b p c.arith) (.block topEpi)))))

/-- ML-KEM-768's key generation of an implementation of `vg_mlkem_sample_ntt4`:
hashing `ek` in the rows if it has the fragments (`Callee4.batchHM16`,
`Callee4.batchP16`), as `kemKeyGenSel` otherwise. -/
def kemKeyGenHSel (c : Callee4) : Prog isa :=
  match c.batchHM16, c.batchP16 with
  | some b, some p => kemKeyGenH16 kem768w c b p
  | _, _ => kemKeyGenSel kem768w c

/-- `vg_mlkem768_keygen`. -/
abbrev keyGen (c : Callee4) : Prog isa := kemKeyGenHSel c

end VG.Impl.MlKem.X86_64
