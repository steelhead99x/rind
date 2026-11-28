module

public import VerifiedGarbage.Impl.MlKem.X86_64.Encrypt

/-!
# ML-KEM on x86-64: encapsulation (`vg_mlkem768_encaps_h`, `vg_mlkem1024_encaps_h`)

`kemEncapsH L (ek = rdi, h = rsi, m = rdx, key = rcx, ct = r8, scratch = r9) -> eax`:
`ML-KEM.Encaps_internal(ek, m)` (FIPS 203 Algorithm 17) of the parameter
set `L`, with `H(ek)` given at `h` (`VG.Spec.MlKem.encapsHContract`). It
keeps `scratch` in `rbx`, `m` in `rbp`, `key` in `r12`, `ct` in `r13` and
`ek` in `r14`, and saves its caller's values of them (and of `r15`) in
`scratch`.

1. `h` to `H` (through `rsi`, which still holds `h`); `m` to `M`;
   `(K, r) = G(m ‖ H(ek))` to `G`.
2. `c = K-PKE.Encrypt(ek, m, r)` to `CT` (`Encrypt.lean`).
3. `K` to `key` and `c` to `ct`.

It returns `r15`: 0 if a `SampleNTT` failed (when `key` and `ct` are
unspecified), and 1 otherwise.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace EncapsH

def pro : List Instr := topPro .r9 [(.rbp, .rdx), (.r12, .rcx), (.r13, .r8), (.r14, .rdi)]

/-- `h` to `H`. -/
def hCopy : Prog isa := copy (sc oH) (.rsi, 0) 32

/-- `m` to `M`, and `G(m ‖ H(ek))`. -/
def hashes : Prog isa :=
  .seq (copy (sc oM) (.rbp, 0) 32) (hashAt [(sc oM, 32), (sc oH, 32)] 72 6 (sc oG) 64)

/-- `K` to `key` and `c` to `ct`. -/
def out (L : Kem) : Prog isa := .seq (copy (.r12, 0) (sc oG) 32) (copy (.r13, 0) (sc L.oCT) L.ctLen)

end EncapsH

open EncapsH in
/-- The encapsulation of the parameter set `L`, with `H(ek)` given. -/
def kemEncapsH (L : Kem) (c : Callee4) : Prog isa :=
  .seq (.block pro) (.seq hCopy (.seq hashes (.seq (encrypt L c (.r14, 0)) (.seq (out L)
    (.block topEpi)))))


end VG.Impl.MlKem.X86_64
