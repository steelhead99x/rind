module

public import VerifiedGarbage.Impl.MlKem.X86_64.Frag

/-!
# ML-KEM on x86-64: the calls of the samplers with 16-bit coefficients

The fragments of `Frag.lean` that sample, for polynomials of 16-bit
coefficients (512 bytes): `SamplePolyCBD₂` (`cbd2_16At`, with the
arithmetic's `cbd16`), `SampleNTT` of the seed at `SB` (`sampleAt16`,
`sampleIJ16`), of the four seeds at `scratch` (`sample4At16`, `quad16`, with
an implementation's `Callee4.s16`), and the entries of a matrix (`ents16`), each
with the working space `scr` of the sampler it calls: 2048 bytes for
`vg_mlkem16_sample_ntt`, 8192 for `vg_mlkem16_sample_ntt4`.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `SamplePolyCBD₂` of the 128 bytes at `b` to the 16-bit coefficients at `f`. -/
def cbd2_16At (A : Arith) (b f : Ptr) : Prog isa := .seq (.block (lea .rdi b ++ lea .rsi f)) (.call A.cbd16N A.cbd16)

/-- `SampleNTT` of the seed at `SB` to the 16-bit coefficients at `a`, with
the working space `scr`, and `r15 ← r15 ∧ result`. -/
def sampleAt16 (a scr : Ptr) : Prog isa :=
  .seq (.block (lea .rdi (sc oSB) ++ lea .rsi a ++ lea .rdx scr))
    (.seq (.call "vg_mlkem16_sample_ntt" sampleNTT16) (.block [.alu32 .and .r15 (.reg .rax)]))

/-- `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` to `a`, with `ρ` at `SB`. -/
def sampleIJ16 (a : Ptr) (i j : Nat) (scr : Ptr) : Prog isa :=
  .seq (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i)) (sampleAt16 a scr)

/-- `SampleNTT` of the four seeds at `scratch` to the four polynomials of
16-bit coefficients from `a`, with the working space `scr`, and
`r15 ← r15 ∧ result`, by the function `p` (symbol and code: an
implementation's `Callee4.s16`). -/
def sample4At16 (p : String × Prog isa) (a scr : Ptr) : Prog isa :=
  .seq (.block (lea .rdi (sc 0) ++ lea .rsi a ++ lea .rdx scr))
    (.seq (.call p.1 p.2) (.block [.alu32 .and .r15 (.reg .rax)]))

/-- Entries `e₀, …, e₀ + 3` of a matrix of `n` columns (entry `e = n i + j`),
from polynomial `a`, with `SampleNTT` on the four seeds at once. -/
def quad16 (p : String × Prog isa) (n e₀ : Nat) (a scr : Ptr) : Prog isa :=
  .seq (seedAt 0 (e₀ / n) (e₀ % n)) (.seq (seedAt 1 ((e₀ + 1) / n) ((e₀ + 1) % n))
    (.seq (seedAt 2 ((e₀ + 2) / n) ((e₀ + 2) % n)) (.seq (seedAt 3 ((e₀ + 3) / n) ((e₀ + 3) % n))
      (sample4At16 p a scr))))

/-- Entries `e, …, e + n - 1` of the `k × k` matrix whose entry `e = k i + j`
is at `sc (oa + 512 e)`, four at a time and the last `n mod 4` one at a
time, with the working space `scr` for either. -/
def ents16 (p : String × Prog isa) (k oa : Nat) (scr : Ptr) : Nat → Nat → Prog isa
  | e, n + 5 => .seq (quad16 p k e (sc (oa + 512 * e)) scr) (ents16 p k oa scr (e + 4) (n + 1))
  | e, 4 => quad16 p k e (sc (oa + 512 * e)) scr
  | e, n + 2 => .seq (sampleIJ16 (sc (oa + 512 * e)) (e / k) (e % k) scr) (ents16 p k oa scr (e + 1) (n + 1))
  | e, 1 => sampleIJ16 (sc (oa + 512 * e)) (e / k) (e % k) scr
  | _, 0 => .block []

/-- The `k²` entries of the matrix. -/
def samples16 (p : String × Prog isa) (k oa : Nat) (scr : Ptr) : Prog isa := ents16 p k oa scr 0 (k * k)

end VG.Impl.MlKem.X86_64
