module

public import VerifiedGarbage.Impl.MlKem.X86_64.EncapsH

/-!
# ML-KEM on x86-64: encapsulation hashing the key (`vg_mlkem768_encaps`, `vg_mlkem1024_encaps`)

`kemEncaps L c (ek = rdi, m = rsi, key = rdx, ct = rcx, scratch = r8) -> eax`:
`ML-KEM.Encaps_internal(ek, m)` (FIPS 203 Algorithm 17) of the parameter
set `L`, computing `H(ek)` itself (`VG.Spec.MlKem.encapsContract`). It keeps
the pointers in the registers `kemEncapsH` (`EncapsH.lean`) keeps them in
(`scratch` in `rbx`, `m` in `rbp`, `key` in `r12`, `ct` in `r13` and `ek`
in `r14`), and is `kemEncapsH` but for `H(ek)`, which it computes with the
sponge functions to `H` first (`hashEk`). With 16-bit polynomials, the
matrix's sampling absorbs `pad(ek)` instead (`kemEncaps16`, `Encaps16.lean`),
with `nb` fragments, each sampling three entries with `sampleHAt`.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace Encaps

/-- Save the callee-saved registers, keep the pointers, and `r15 ← 1`. -/
def pro : List Instr := topPro .r8 [(.rbp, .rsi), (.r12, .rdx), (.r13, .rcx), (.r14, .rdi)]

variable (L : Kem)

/-- `H(ek)` to `H`, with the sponge functions. -/
def hashEk : Prog isa := hashAt [((.r14, 0), L.ekLen)] 136 6 (sc oH) 32

/-- The number of fragments: `|pad(ek)| / 408`. -/
def nb : Nat := (L.ekLen / 136 + 1) / 3

/-- The fragment `b` on the four seeds at `scratch` and the polynomials from
`a`, with the working space `scr`, and `r15 ← r15 ∧ result`. -/
def sampleHAt (b : Prog isa) (a scr : Ptr) : Prog isa :=
  .seq (.block (lea .rdi (sc 0) ++ lea .rsi a ++ lea .rdx scr)) (.seq b (.block [.alu32 .and .r15 (.reg .rax)]))

end Encaps

open Encaps in
/-- The encapsulation of the parameter set `L`. -/
def kemEncaps (L : Kem) (c : Callee4) : Prog isa :=
  .seq (.block pro) (.seq (hashEk L) (.seq EncapsH.hashes (.seq (encrypt L c (.r14, 0))
    (.seq (EncapsH.out L) (.block topEpi)))))

end VG.Impl.MlKem.X86_64
