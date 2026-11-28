module

public import VerifiedGarbage.Impl.MlKem.X86_64.Kem

/-!
# ML-KEM on x86-64: key generation (`vg_mlkem768_keygen`, `vg_mlkem1024_keygen`)

`kemKeyGen L (seed = rdi, ek = rsi, dk = rdx, scratch = rcx) -> eax`:
`ML-KEM.KeyGen_internal(d, z)` (FIPS 203 Algorithms 16 and 13) of the
parameter set `L` (`Kem.lean`, rank `k`) with `d ‖ z` at `seed`, as calls of
the verified primitives and sponge functions (`Frag.lean`). It keeps
`scratch` in `rbx`, `seed` in `rbp`, `ek` in `r12` and `dk` in `r13`, and the
AND of the results of `vg_mlkem_sample_ntt` in `r15`, and saves its caller's
values of them (and of `r14`) in `scratch`.

1. `(ρ, σ) = G(d ‖ k)` to `G`, and `ρ` to `SB`, the seed of `SampleNTT`.
2. `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` for the `k²` entries `(i, j)`
   (`samples`). If one of them failed (`r15 = 0`), it returns 0 at once.
3. `PRF₂(σ, N)` for `N < 2k` (`c.prfs`, to `PR`), and `s[j]` (polynomial
   `j`) and `e[i]` (polynomial `k + i`): `SamplePolyCBD₂(PRF₂(σ, N))`.
4. `ŝ = NTT(s)` in place and `t̂ = Â ∘ ŝ + NTT(e)` to polynomials `pU`, …
   (`vg_mlkem*_keygen_mul`, with `pZ` as its working space), and
   `ByteEncode₁₂(t̂[i])` to `ek`; `ByteEncode₁₂(ŝ[j])` to `dk`.
5. `ρ` to `ek`, `ek` to `dk`, `H(ek)` to `dk`, and `z` to `dk`.

Only the calls of `vg_mlkem_sample_ntt`, and the branch on their results,
depend on `ρ` (which the contract declares that the function may leak);
every other address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace KeyGen

variable (L : Kem)

def pro : List Instr := topPro .rcx [(.rbp, .rdi), (.r12, .rsi), (.r13, .rdx)]

/-- `G(d ‖ k)`, and `ρ` to `SB`. -/
def gRho : Prog isa :=
  .seq (.block (setB (sc oNB) L.k)) (.seq (hashAt [((.rbp, 0), 32), (sc oNB, 1)] 72 6 (sc oG) 64)
    (copy (sc oSB) (sc oG) 32))

/-- `s[N]` or `e[N - k]`, from `PRF₂(σ, N)`. -/
def se (A : Arith) (N : Nat) : Prog isa := cbd2At A (sc (L.oPR + 128 * N)) (pS N)

/-- `t̂[i]`, encoded to `ek`. -/
def encT (A : Arith) (i : Nat) : Prog isa := enc12At A (pS (L.pU + i)) (.r12, 384 * i)

/-- `ŝ[j]`, encoded to `dk`. -/
def encS (A : Arith) (j : Nat) : Prog isa := enc12At A (pS j) (.r13, 384 * j)

/-- `ρ` to `ek`, `ek` to `dk`, `H(ek)` and `z` to `dk`. -/
def fin : Prog isa :=
  .seq (copy (.r12, 384 * L.k) (sc oG) 32) (.seq (copy (.r13, 384 * L.k) (.r12, 0) L.ekLen)
    (.seq (hashAt [((.r12, 0), L.ekLen)] 136 6 (.r13, 384 * L.k + L.ekLen) 32)
      (copy (.r13, 384 * L.k + L.ekLen + 32) (.rbp, 32) 32)))

def rest (c : Callee4) : Prog isa :=
  .seq (c.prfs 0 (2 * L.k) L.oPR L.lPW) (.seq (seqR (se L c.arith) 0 (2 * L.k))
    (.seq (L.kgMulAt c.arith (pS L.pU) (pS 0) (pS L.pA) (pS L.k) (pS L.pZ))
      (.seq (seqR (encT L c.arith) 0 L.k) (.seq (seqR (encS c.arith) 0 L.k) (fin L)))))

end KeyGen

open KeyGen in
/-- The key generation of the parameter set `L`. -/
def kemKeyGen (L : Kem) (c : Callee4) : Prog isa :=
  .seq (.block pro) (.seq (gRho L) (.seq (L.samples c) (.seq (ifOk (rest L c)) (.block topEpi))))


end VG.Impl.MlKem.X86_64
