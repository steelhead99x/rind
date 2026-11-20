module

public import VerifiedGarbage.Impl.MlKem.X86_64.Kem16
public import VerifiedGarbage.Impl.MlKem.X86_64.Encaps

/-!
# ML-KEM-768 on x86-64: encapsulation with `H(ek)` given, `PRF₂` in the matrix's fragments

`kemEncapsHP16 K c p` is `kemEncapsH16` (`Kem16.lean`) with the outputs of
`PRF₂(r, N)` computed in the fourth Keccak state of the matrix's samplers
(the fragment `p`, an implementation's `Callee4.batchP16`, as key
generation's first row does), rather than four at a time after the matrix:

1. the prologue, `H(ek)` to `H`, `m` to `M` and `(K, r) = G(m ‖ H(ek))` to
   `G` (`EncapsH.hashes`);
2. `ρ` to `SB`, from the key;
3. for each row `i < k`: `r` to the samplers' working space, and its
   `k = 3` entries of `Â` with `p (pf i) (pn i)`, which computes
   `PRF₂(r, pf i)`, …, `PRF₂(r, pf i + pn i - 1)` in the squeezes of the
   three, and the polynomials of `y ‖ e₁ ‖ e₂` sampled from them with
   `SamplePolyCBD₂` (`frag`): the `2k + 1 = 7` outputs, `N` = 1 to 3 in the
   first row, 4 to 6 in the second and 0 in the last. (The fragment may
   write a fourth polynomial after its three, which for the last row is
   polynomial 0 of `y`: so that one is sampled after it.)
4. if every `SampleNTT` succeeded, the rest of K-PKE.Encrypt, whose
   ciphertext goes straight to `ct`, and `K` to `key`.

So the nine entries of `Â` and the seven outputs of `PRF₂` take nine
permutations of four Keccak states, where `kemEncapsH16` takes eight, the
three of the ninth entry's sampling on its own, and two of the four
instances of `PRF₂` at once. The outputs of `PRF₂` are computed whether or
not a `SampleNTT` fails.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace EncapsHP16

variable (K : Kem16)

/-- The first output of `PRF₂` the fragment of row `i` computes (for
`k = 3`): 1 and 4 in the first two rows, and 0 in the last. -/
def pf (i : Nat) : Nat := if i < 2 then 3 * i + 1 else 0

/-- How many outputs of `PRF₂` the fragment of row `i` computes: three in the
first two rows, one in the last. -/
def pn (i : Nat) : Nat := if i < 2 then 3 else 1

/-- `SamplePolyCBD₂(PRF₂(r, pf i + j))` to polynomial `pf i + j`, from output
`j` of the fragment of row `i`. -/
def cbdP (A : Arith) (i j : Nat) : Prog isa :=
  cbd2_16At A (sc (K.oW + Sample4.oPO + 128 * j)) (Top16.rP K (pf i + j))

/-- Row `i` of `Â`: `r` to the samplers' working space (which the fragment
before may have overwritten), the seeds of entries `3i` to `3i + 3`, and
`p (pf i) (pn i)`, which samples the first three and computes `pn i` outputs
of `PRF₂`, and the polynomials sampled from them. -/
def frag (A : Arith) (p : Nat → Nat → Prog isa) (i : Nat) : Prog isa :=
  .seq (copy (sc (K.oW + Sample4.oPS)) (sc (oG + 32)) 32)
    (.seq (seedAt 0 i 0) (.seq (seedAt 1 i 1) (.seq (seedAt 2 i 2) (.seq (seedAt 3 (i + 1) 0)
      (.seq (Encaps.sampleHAt (p (pf i) (pn i)) (Top16.aP K (3 * i)) (sc K.oW))
        (seqR (cbdP K A i) 0 (pn i)))))))

/-- K-PKE.Encrypt of the key at `E` and the message at `M`, with the
randomness at `G + 32`, to `Cp`: `ρ` to `SB`, the rows of `Â` with the
noise, and the rest if every `SampleNTT` succeeded. -/
def encrypt (c : Callee4) (p : Nat → Nat → Prog isa) (E Cp : Ptr) : Prog isa :=
  .seq (copy (sc oSB) (E.1, E.2 + 384 * K.L.k) 32)
    (.seq (seqR (frag K c.arith p) 0 K.L.k) (ifOk (K.L.kpkeEncAt Cp (sc K.oA) E (sc K.oR) (sc oM) (sc K.oZ))))

end EncapsHP16

open EncapsH in
/-- ML-KEM-768's encapsulation with `H(ek)` given, with 16-bit polynomials,
computing the outputs of `PRF₂` with the matrix's fragments `p` of the
implementation `c`: the ciphertext straight to `ct`. -/
def kemEncapsHP16 (K : Kem16) (c : Callee4) (p : Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block pro) (.seq hCopy (.seq hashes (.seq (EncapsHP16.encrypt K c p (.r14, 0) (.r13, 0))
    (.seq (copy (.r12, 0) (sc oG) 32) (.block topEpi)))))

/-- ML-KEM-768's encapsulation with `H(ek)` given of an implementation of
`vg_mlkem_sample_ntt4`: computing `PRF₂` in the matrix's fragments if it has
a 16-bit sampler and the fragments (`Callee4.s16`, `Callee4.batchP16`), as
`kemEncapsHSel` otherwise. -/
def kemEncapsHPSel (c : Callee4) : Prog isa :=
  match c.s16, c.batchP16 with
  | some _, some p => kemEncapsHP16 kem768w c p
  | _, _ => kemEncapsHSel kem768w c

/-- `vg_mlkem768_encaps_h`. -/
abbrev encapsH (c : Callee4) : Prog isa := kemEncapsHPSel c

end VG.Impl.MlKem.X86_64
