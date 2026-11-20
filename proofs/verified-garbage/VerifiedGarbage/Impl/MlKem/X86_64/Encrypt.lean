module

public import VerifiedGarbage.Impl.MlKem.X86_64.Kem

/-!
# ML-KEM on x86-64: K-PKE.Encrypt, in encapsulation and decapsulation

`K-PKE.Encrypt(ek, m, r)` (FIPS 203 Algorithm 14) of the parameter set `L`
(`Kem.lean`, rank `k`) with the encryption key `ek` at the pointer `E` (`r14`
in encapsulation, `rbp + 384k` in decapsulation), the message `m` at `M` and
the randomness `r` at `G + 32` (the second half of `G`'s output) in the
working space `scratch` at `rbx`: the ciphertext to `CT` in `scratch`. `r15`
is the AND of the results of `vg_mlkem_sample_ntt`, as in key generation.

1. `ρ` (`ek[384k : 384k + 32]`) to `SB`; `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)`.
   If one of them failed (`r15 = 0`), nothing more.
2. `PRF₂(r, N)` for `N ≤ 2k` (`c.prfs`, to `PR`), and
   `y[j] = SamplePolyCBD₂(PRF₂(r, j))` (polynomial `j`).
3. `t̂[i] = ByteDecode₁₂(ek[384i : 384i + 384])` (polynomial `k + i`).
4. `NTT⁻¹(Â^⊺ ∘ ŷ)` and `NTT⁻¹(t̂^⊺ ∘ ŷ)`, with `ŷ = NTT(y)`, to the `k + 1`
   polynomials from `pU` (`vg_mlkem*_encrypt_mul`).
5. `u[i] = NTT⁻¹(Â^⊺ ∘ ŷ)[i] + e₁[i]` (polynomial `pU + i`), with
   `e₁[i] = SamplePolyCBD₂(PRF₂(r, k + i))` (polynomial 15), and
   `ByteEncode_{d_u}(Compress_{d_u}(u[i]))` to `CT + 32 d_u i`.
6. `v = NTT⁻¹(t̂^⊺ ∘ ŷ) + e₂ + μ` (polynomial `pU + k`), with
   `e₂ = SamplePolyCBD₂(PRF₂(r, 2k))` and `μ = Decompress₁(ByteDecode₁(m))`,
   and `ByteEncode_{d_v}(Compress_{d_v}(v))` to `CT + 32 d_u k`.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace Encrypt

variable (L : Kem)

/-- `PRF₂(r, N)`. -/
abbrev prfO (N : Nat) : Ptr := sc (L.oPR + 128 * N)

/-- `ρ` to `SB`, and `Â`. -/
def mat (c : Callee4) (E : Ptr) : Prog isa := .seq (copy (sc oSB) (E.1, E.2 + 384 * L.k) 32) (L.samples c)

/-- `y[j]`. -/
def y (A : Arith) (j : Nat) : Prog isa := cbd2At A (prfO L j) (pS j)

/-- `t̂[i]`. -/
def t (A : Arith) (E : Ptr) (i : Nat) : Prog isa := dec12At A (E.1, E.2 + 384 * i) (pS (L.k + i))

/-- The products. -/
def mul (A : Arith) : Prog isa := L.encMulAt A (pS L.pU) (pS L.pA) (pS L.k) (pS 0) (pS L.pZ)

/-- `u[i]`, compressed and encoded to the ciphertext. -/
def u (A : Arith) (i : Nat) : Prog isa :=
  .seq (cbd2At A (prfO L (L.k + i)) (pS 15)) (.seq (addAt A (pS (L.pU + i)) (pS 15))
    (L.ceAt A.codecs (pS (L.pU + i)) L.du (sc (L.oCT + 32 * L.du * i))))

/-- `v`, compressed and encoded to the ciphertext. -/
def v (A : Arith) : Prog isa :=
  .seq (cbd2At A (prfO L (2 * L.k)) (pS 15)) (.seq (addAt A (pS (L.pU + L.k)) (pS 15))
    (.seq (ddAt A.codecs (sc oM) 1 (pS 15)) (.seq (addAt A (pS (L.pU + L.k)) (pS 15))
      (L.ceAt A.codecs (pS (L.pU + L.k)) L.dv (sc (L.oCT + 32 * L.du * L.k))))))

def rest (c : Callee4) (E : Ptr) : Prog isa :=
  .seq (c.prfs 0 (2 * L.k + 1) L.oPR L.lPW) (.seq (seqR (y L c.arith) 0 L.k) (.seq (seqR (t L c.arith E) 0 L.k)
    (.seq (mul L c.arith) (.seq (seqR (u L c.arith) 0 L.k) (v L c.arith)))))

end Encrypt

open Encrypt in
def encrypt (L : Kem) (c : Callee4) (E : Ptr) : Prog isa := .seq (mat L c E) (ifOk (rest L c E))

end VG.Impl.MlKem.X86_64
