module

public import VerifiedGarbage.Impl.MlKem.X86_64.Compress

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_compress_encode` and `vg_mlkem1024_decode_decompress`

The widths of ML-KEM-1024 (`d = 5` or `11`, a public argument: the code
branches on it), as `vg_mlkem_compress_encode` and
`vg_mlkem_decode_decompress` do the widths of ML-KEM-768
(`Impl/MlKem/X86_64/Compress.lean`): a group of 8 coefficients is `d`
bytes, and the loop runs over the 32 groups with `rcx` counting down. The
values of a group are the base-`2ᵈ` digits of a number whose bytes are the
group's bytes; the code handles it in segments that fit in the 64 bits of
`r10`: a segment is the number whose digits are some consecutive values of
the group (accumulated from the last), shifted right by `s` bits, whose
bytes are some consecutive bytes of the group.

* `d = 5`: one segment, the 8 values (40 bits) and the 5 bytes.
* `d = 11`: values 0–4 (55 bits), whose low 6 bytes are bytes 0–5; and
  values 4–7 (44 bits) shifted right by 4, whose 5 bytes are bytes 6–10.
  Value 4 is in both (compressed twice; its bytes read twice to decode).

The pieces of a group are those of ML-KEM-768's (`ceAcc`, `ceSt`, `ddLd`,
`ddVals`), with the rounding constant 261888.

`compressEncode(f = rdi, d = esi, out = rdx, len = rcx)` (`out` moved to
`r8`) compresses each coefficient `x` with a multiplication,
`Compress_d(x) = ((x · M_d + 261888) >> 19) mod 2ᵈ` (`M_d` in `r9`), and
`decodeDecompress(b = rdi, len = rsi, d = edx, f = rcx)` (`f` moved to
`rsi`) decompresses each value `y` with a multiplication by `q` (in `r9`),
`(q · y + 2ᵈ⁻¹) >> d`.

Every address and branch depends only on the pointers and `d`.
-/

@[expose] public section

namespace VG.Impl.MlKem1024.X86_64

open VG.X86_64 VG.Impl.MlKem.X86_64

/-- `M_d`, the multiplier of `Compress_d`. -/
def ceMul1024 (d : Nat) : Nat := if d = 5 then 5040 else 322542

def ceBody5 : List Instr := ceAcc 261888 5 0 8 ++ ceSt 0 5 ++ ceTail 8 5

def ceBody11 : List Instr :=
  ceAcc 261888 11 0 5 ++ ceSt 0 6 ++ ceAcc 261888 11 4 4 ++ ([.shift .shr .r10 4] : List Instr) ++ ceSt 6 5 ++
    ceTail 8 11

def compressEncode1024 : Prog isa :=
  .seq (.block [.mov32 .rsi (.reg .rsi), .mov .r8 (.reg .rdx), .alu32 .cmp .rsi (.imm 5)])
    (.ite .e (ceLoopW (ceMul1024 5) 32 ceBody5) (ceLoopW (ceMul1024 11) 32 ceBody11))

def ddBody5 : List Instr := ddLd 0 5 ++ ddVals 5 0 8 ++ ddTail 8 5

def ddBody11 : List Instr :=
  ddLd 0 6 ++ ddVals 11 0 4 ++ ddLd 5 6 ++ ([.shift .shr .r10 4] : List Instr) ++ ddVals 11 4 4 ++ ddTail 8 11

def decodeDecompress1024 : Prog isa :=
  .seq (.block [.mov32 .rdx (.reg .rdx), .mov .rsi (.reg .rcx), .alu32 .cmp .rdx (.imm 5)])
    (.ite .e (ddLoopW 32 ddBody5) (ddLoopW 32 ddBody11))

end VG.Impl.MlKem1024.X86_64
