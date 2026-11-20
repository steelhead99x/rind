module

public import VerifiedGarbage.Impl.MlKem.X86_64.Vec
public import VerifiedGarbage.Spec.MlKem

/-!
# ML-KEM on x86-64: `vg_mlkem_ntt` and `vg_mlkem_inv_ntt`

`ntt(f = rdi, scratch = rsi)` and `nttInv(f = rdi, scratch = rsi)` compute
on eight coefficients at a time, as words of SSE registers (see
`Vec.lean`). `scratch` holds the 128 words `ζ^BitRev7(k) · 2¹⁶ mod q` at 0
(`zmTab`, stored with immediates: the code has no other memory), the
polynomial as 256 words at 256 (`S`).

The prologue stores the table and the constants, and
packs `f` into `S` (`vpack`); the epilogue unpacks `S` into `f`
(`vunpack`). In between, the layers, each a pass over `S` with `rdx`
pointing at the words it loads, `r8` at the zetas of the table:

* `NTT` (Algorithm 9): the layers with `len` = 128, 64, 32, 16 and 8
  (`vlay`) run their blocks (counted in `rax`), each its zeta in the words of
  `xmm13` and `len / 8` times the butterflies of eight words `f[j]` and of
  the eight `f[j + len]` (`vbfly`, counted in `rcx`). The layer with
  `len = 4` (`vlay4`) loads the 16 coefficients of two blocks, gathers their
  lower and upper halves into `xmm0` and `xmm1` (`punpcklqdq`,
  `punpckhqdq`), with the two zetas in the halves of `xmm13`; the layer
  with `len = 2` (`vlay2`) those of four blocks, their pairs gathered (with
  `pshufd` first), with the four zetas in the pairs of words of `xmm13`.
* `NTT⁻¹` (Algorithm 10): the same layers in the opposite order, with the
  zetas from `k = 127` down and the inverse butterflies (`vibfly`); then
  every coefficient is multiplied by `3303 = 128⁻¹ mod q` (`vscale`, with
  `vmont` by `3303 · 2¹⁶ mod q = 512`).

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `ζ^BitRev7(k) · 2¹⁶ mod q`. -/
def zmTab (k : Nat) : Nat := 17 ^ Spec.MlKem.bitRev7 k * 2 ^ 16 % 3329

/-- The offset of the polynomial's words in `scratch`. -/
def oS : Nat := 256

/-- The offset of MXCSR's words in `scratch`. -/
def oMx : Nat := 768

/-- `d ← r + off`. -/
def leaR (d r : Reg) (off : Nat) : List Instr := [.mov d (.reg r), .alu .add d (.imm (BitVec.ofNat 32 off))]

/-- The zeta at `[r8]` in the words of `xmm13`, arranged by `pshufd` with `o`. -/
def vzeta (o : BitVec 8) : List Instr :=
  [.movdquLoad .xmm13 (at_ .r8 0), xb .punpcklwd .xmm13 .xmm13, .xop (.pshufd .xmm13 .xmm13 o)]

/-- A layer with `len ≥ 8` and butterflies `bf`: its `128 / len` blocks, the
first with the zeta `k`, the zeta pointer moving by `dz` bytes. -/
def vlay (bf : List Instr) (len k : Nat) (dz : BitVec 32) : Prog isa :=
  .seq (.block (leaR .rdx .rsi oS ++ leaR .r8 .rsi (2 * k) ++
    [.mov32 .rax (.imm (BitVec.ofNat 32 (128 / len)))])) <|
  .loop (.seq (.block (vzeta 0 ++ [.alu .add .r8 (.imm dz)]))
    (.seq (rcxLoop (len / 8) ([.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm1 (at_ .rdx (2 * len))] ++
        bf ++ [.movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx (2 * len)) .xmm3,
          .alu .add .rdx (.imm 16)]))
      (.block [.alu .add .rdx (.imm (BitVec.ofNat 32 (2 * len))), .alu .sub .rax (.imm 1)]))) .ne

/-- The layer with `len = 4`, two blocks at a time: the zetas at `[r8]`
arranged by `pshufd` with `o`, the zeta pointer moving by `dz` bytes. -/
def vlay4 (bf : List Instr) (k : Nat) (o : BitVec 8) (dz : BitVec 32) : Prog isa :=
  .seq (.block (leaR .rdx .rsi oS ++ leaR .r8 .rsi (2 * k))) <|
  rcxLoop 16 ([.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm1 (at_ .rdx 16)] ++ vzeta o ++
    [.alu .add .r8 (.imm dz), xmov .xmm2 .xmm0, xb .punpcklqdq .xmm0 .xmm1, xb .punpckhqdq .xmm2 .xmm1,
      xmov .xmm1 .xmm2] ++ bf ++
    [xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm3, xb .punpckhqdq .xmm1 .xmm3,
      .movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32)])

/-- The layer with `len = 2`, four blocks at a time: the zetas at `[r8]`,
their pairs of words arranged by `pshufd` with `o`, the zeta pointer moving
by `dz` bytes. -/
def vlay2 (bf : List Instr) (k : Nat) (o : BitVec 8) (dz : BitVec 32) : Prog isa :=
  .seq (.block (leaR .rdx .rsi oS ++ leaR .r8 .rsi (2 * k))) <|
  rcxLoop 16 ([.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm2 (at_ .rdx 16)] ++ vzeta o ++
    [.alu .add .r8 (.imm dz), .xop (.pshufd .xmm0 .xmm0 0xD8), .xop (.pshufd .xmm2 .xmm2 0xD8),
      xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm2, xb .punpckhqdq .xmm1 .xmm2] ++ bf ++
    [xmov .xmm1 .xmm0, xb .punpckldq .xmm0 .xmm3, xb .punpckhdq .xmm1 .xmm3,
      .movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32)])

/-- Every word of `S` times `3303`, reduced. -/
def vscale : Prog isa :=
  .seq (.block (leaR .rdx .rsi oS ++ [.mov32 .rax (.imm 0x02000200), .xop (.movq .xmm13 .rax),
      .xop (.pshufd .xmm13 .xmm13 0)]))
    (rcxLoop 32 ([.movdquLoad .xmm3 (at_ .rdx 0)] ++ vmont .xmm3 .xmm13 .xmm2 ++ vcadd .xmm3 .xmm2 ++
      [.movdquStore (at_ .rdx 0) .xmm3, .alu .add .rdx (.imm 16)]))

/-- The table, the constants, and `f` packed into `S`. -/
def vpro : Prog isa :=
  .seq (.block (wordTab zmTab 128 .rsi 0 ++ vconsts ++ [.mov .r9 (.reg .rdi)] ++ leaR .rdx .rsi oS)) vpack

/-- `S` unpacked into `f`. -/
def vepi : Prog isa :=
  .seq (.block ([.mov .r9 (.reg .rdi)] ++ leaR .rdx .rsi oS)) vunpack

def ntt : Prog isa :=
  .seq vpro (.seq (vlay vbfly 128 1 2) (.seq (vlay vbfly 64 2 2) (.seq (vlay vbfly 32 4 2)
    (.seq (vlay vbfly 16 8 2) (.seq (vlay vbfly 8 16 2) (.seq (vlay4 vbfly 32 0x50 4)
      (.seq (vlay2 vbfly 64 0xE4 8) vepi)))))))

def nttInv : Prog isa :=
  .seq vpro (.seq (vlay2 vibfly 124 0x1B (-8)) (.seq (vlay4 vibfly 62 0x05 (-4))
    (.seq (vlay vibfly 8 31 (-2)) (.seq (vlay vibfly 16 15 (-2)) (.seq (vlay vibfly 32 7 (-2))
      (.seq (vlay vibfly 64 3 (-2)) (.seq (vlay vibfly 128 1 (-2)) (.seq vscale vepi))))))))

end VG.Impl.MlKem.X86_64
