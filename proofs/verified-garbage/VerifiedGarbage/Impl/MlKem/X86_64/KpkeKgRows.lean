module

public import VerifiedGarbage.Impl.MlKem.X86_64.Kpke16

/-!
# ML-KEM on x86-64: K-PKE key generation a row at a time, with 16-bit polynomials

The two halves of `vg_mlkem*_kpke_keygen` (`Kpke16.lean`), from the code of
`vg_mlkem*_keygen_mul` with AVX2 (`keygenMul16Y`), for a caller that
encodes each row of `t̂` as soon as it has the row of `Â`
(`Proof/MlKem/KpkeKgRowsContract.lean`). Each saves its caller's callee-saved
registers at `scratch + 3072` (`KpkeMul.slots`), as `keygen_mul` does, and
keeps `scratch` in `rbx`; its products run in the MXCSR region at
`scratch + 768` (`oMx`).

* `kgNtt`, `vg_mlkem*_kpke_keygen_ntt(dk = rdi, s = rsi, e = rdx, se = rcx, scratch = r8)`:
  `s` (the first `k` polynomials of `se`) widened to `u32`s in `s`; the
  first loop of `keygen_mul` (`nttK16`): `NTT(s[j])` in place and `NTT(e[j])`
  of the `u16`s from `se + 512k` to `e`; then `ByteEncode₁₂(ŝ[j])` to `dk`.
* `kgRow`, `vg_mlkem*_kpke_keygen_row(ek = rdi, a = rsi, s = rdx, e = rcx, scratch = r8)`:
  the table of the products, then a row of `keygen_mul` (`rowY16`): the
  products of the row `Â[i]` at `a` and `ŝ` at `s` added to `ê[i]` at `e`;
  then `ByteEncode₁₂` of that to `ek`.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace KpkeKgRows

open KpkeMul Kpke16

variable (L : Kem) (A : Prims)

/-- Save the callee-saved registers, `scratch` to `rbx` and the arguments of
`kgNtt` to `r13` (`dk`), `r12` (`s`), `rbp` (`e`) and `r15` (`se`). -/
def proN : List Instr :=
  saveE ++ [.mov .rbx (.reg .r8), .mov .r13 (.reg .rdi), .mov .r12 (.reg .rsi), .mov .rbp (.reg .rdx),
    .mov .r15 (.reg .rcx)]

/-- `s[j]` (`u16`s at `se + 512 j`) as `u32`s at `s + 1024 j`. -/
def wideS (j : Nat) : Prog isa := widenIn (.r15, 512 * j) (.r12, 1024 * j)

/-- `ByteEncode₁₂(ŝ[j])` to `dk + 384 j`. -/
def encS (j : Nat) : Prog isa := .seq (.block (lea .rdi (.r12, 1024 * j) ++ lea .rsi (.r13, 384 * j))) A.enc12

/-- The products of `kgNtt`: `NTT(s[j])` in place and `NTT(e[j])` to `e`, for
each `j < k` (`keygen_mul`'s first loop, from `e`'s `u16`s at `se + 512k`). -/
def nttsN : Prog isa :=
  .seq (.block [.alu .add .r15 (.imm (BitVec.ofNat 32 (512 * L.k))), .mov32 .r14 (.imm (BitVec.ofNat 32 L.k))])
    (.loop nttK16 .ne)

/-- `vg_mlkem*_kpke_keygen_ntt` of the parameter set `L`, with the arithmetic of `A`. -/
def kgNtt : Prog isa :=
  .seq (.block proN) (.seq (seqR wideS 0 L.k) (.seq (nttsN L)
    (.seq (.block [.alu .sub .r12 (.imm (BitVec.ofNat 32 (1024 * L.k)))]) (.seq (seqR (encS A) 0 L.k)
      (.block restore)))))

/-- Save the callee-saved registers, `scratch` to `rbx` and the arguments of
`kgRow` to `r12` (`ek`), `rbp` (`a`), `r15` (`s`) and `r13` (`e`). -/
def proR : List Instr :=
  saveE ++ [.mov .rbx (.reg .r8), .mov .r12 (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r15 (.reg .rdx),
    .mov .r13 (.reg .rcx)]

/-- The table of the products in `scratch`, then the
products of the row at `a` and `ŝ` at `s` added to `e` (`rowY16`). -/
def rowR : Prog isa :=
  .seq (.block ([.mov .rcx (.reg .rbx)] ++ Bodies.avx2.tab))
    (.seq (.block [.mov .rdi (.reg .r13), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
      .mov .rcx (.reg .rbx)]) (rowY16 L.k))

/-- `vg_mlkem*_kpke_keygen_row` of the parameter set `L`, with the arithmetic of `A`. -/
def kgRow : Prog isa :=
  .seq (.block proR) (.seq (rowR L) (.seq (.seq (.block (lea .rdi (.r13, 0) ++ lea .rsi (.r12, 0))) A.enc12)
    (.block restore)))

end KpkeKgRows

/-- `vg_mlkem*_kpke_keygen_ntt(dk, s, e, se, scratch)`. -/
def Kem.kgNttAt (L : Kem) (dk s e se z : Ptr) : Prog isa :=
  .seq (.block (lea .rdi dk ++ lea .rsi s ++ lea .rdx e ++ lea .rcx se ++ lea .r8 z))
    (.call (L.p.fn "kpke_keygen_ntt") (KpkeKgRows.kgNtt L .avx2))

/-- `vg_mlkem*_kpke_keygen_row(ek, a, s, e, scratch)`. -/
def Kem.kgRowAt (L : Kem) (ek a s e z : Ptr) : Prog isa :=
  .seq (.block (lea .rdi ek ++ lea .rsi a ++ lea .rdx s ++ lea .rcx e ++ lea .r8 z))
    (.call (L.p.fn "kpke_keygen_row") (KpkeKgRows.kgRow L .avx2))

end VG.Impl.MlKem.X86_64
