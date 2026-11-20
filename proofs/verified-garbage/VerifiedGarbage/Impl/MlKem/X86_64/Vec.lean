module

public import VerifiedGarbage.Impl.MlKem.X86_64.Common

/-!
# ML-KEM on x86-64: arithmetic modulo `q` in the words of SSE registers

The NTT, its inverse and `MultiplyNTTs` compute on eight coefficients at a
time, as signed 16-bit words of SSE2 registers, with `q` in the words of
`xmm15` and `q⁻¹ mod 2¹⁶ = 62209` in those of `xmm14` (`vconsts`).

* `vmont d z t`: `d ← d · z · 2⁻¹⁶ mod q`, in `(-q, q)`, for words with
  `|d · z| < q · 2¹⁵` (a Montgomery reduction: `t = d · z · q⁻¹ mod 2¹⁶`,
  so that `d · z - t · q` is a multiple of `2¹⁶`, and `d ← ⌊d · z / 2¹⁶⌋ -
  ⌊t · q / 2¹⁶⌋`, which is `(d · z - t · q) / 2¹⁶`). A coefficient `x` is
  multiplied by `ζ` as `vmont` with `ζ · 2¹⁶ mod q`, which the tables hold.
* `vcadd d t`: `d ← d + q` for the words of `d` that are negative (with
  `psraw` by 15, a mask), from `(-q, q)` to `[0, q)`; `vcsub d t`: `d ← d - q`,
  then `vcadd`, from `[0, 2q)` to `[0, q)`.

`pmullw` and `pmulhw` have data-dependent timing on processors with MCDT
unless MXCSR is `0x1FBF` (see `TCB/X86_64/Isa.lean`): ML-KEM's code sets no
MXCSR of its own, as the dispatcher of every x86-64 ML-KEM function runs
`vg_mcdt_enter` first, which leaves MXCSR `0x1FBF` for the whole call
("Dispatchers" in `TCB/Rust.lean`).

A polynomial is stored as 256 `u32`s, and in the working space as 256
words (`vpack`, `vunpack`): 32 bytes of the former at `[a]` are the 16 bytes
of the latter at `[b]`.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `op d, r` -/
def xb (op : XBinOp) (d r : XReg) : Instr := .xop (.bin op d r)

/-- `d ← r` -/
def xmov (d r : XReg) : Instr := xb .movdqa d r

/-- `q` in the words of `xmm15` and `q⁻¹ mod 2¹⁶ = 62209` in those of
`xmm14`, through `rax`. -/
def vconsts : List Instr :=
  [.mov32 .rax (.imm 0x0D010D01), .xop (.movq .xmm15 .rax), .xop (.pshufd .xmm15 .xmm15 0),
    .mov32 .rax (.imm 0xF301F301), .xop (.movq .xmm14 .rax), .xop (.pshufd .xmm14 .xmm14 0)]

/-- `d ← d · z · 2⁻¹⁶ mod q`, in `(-q, q)`, with a temporary `t`. -/
def vmont (d z t : XReg) : List Instr :=
  [xmov t d, xb .pmullw t z, xb .pmullw t .xmm14, xb .pmulhw d z, xb .pmulhw t .xmm15,
    xb .psubw d t]

/-- `d ← d + q` for the negative words of `d`, with a temporary `t`. -/
def vcadd (d t : XReg) : List Instr :=
  [xmov t d, .xop (.shift .psraw t 15), xb .pand t .xmm15, xb .paddw d t]

/-- `d ← d mod q` for words in `[0, 2q)`, with a temporary `t`. -/
def vcsub (d t : XReg) : List Instr := xb .psubw d .xmm15 :: vcadd d t

/-- The butterflies of Algorithm 9 on the words of `xmm0` (`f[j]`) and
`xmm1` (`f[j + len]`) with the zetas `ζ · 2¹⁶ mod q` in `xmm13`:
`xmm0 ← xmm0 + ζ · xmm1` and `xmm3 ← xmm0 - ζ · xmm1`. -/
def vbfly : List Instr :=
  vmont .xmm1 .xmm13 .xmm2 ++ vcadd .xmm1 .xmm2 ++ (xmov .xmm3 .xmm0 :: xb .paddw .xmm0 .xmm1 ::
    vcsub .xmm0 .xmm2) ++ (xb .psubw .xmm3 .xmm1 :: vcadd .xmm3 .xmm2)

/-- The butterflies of Algorithm 10 on the words of `xmm0` (`f[j]`) and
`xmm1` (`f[j + len]`) with the zetas in `xmm13`: `xmm0 ← xmm0 + xmm1` and
`xmm3 ← ζ · (xmm1 - xmm0)`. -/
def vibfly : List Instr :=
  (xmov .xmm3 .xmm1 :: xb .psubw .xmm3 .xmm0 :: xb .paddw .xmm0 .xmm1 :: vcsub .xmm0 .xmm2) ++
    vmont .xmm3 .xmm13 .xmm2 ++ vcadd .xmm3 .xmm2

/-! ## Tables and polynomials -/

/-- The words `t 0, …, t (n - 1)` at `[r + off]`, four at a time, through `r9`. -/
def wordTab (t : Nat → Nat) (n : Nat) (r : Reg) (off : Nat) : List Instr :=
  (List.range (n / 4)).flatMap fun i =>
    [.movImm64 .r9 (BitVec.ofNat 64 (t (4 * i) + 2 ^ 16 * t (4 * i + 1) + 2 ^ 32 * t (4 * i + 2) +
      2 ^ 48 * t (4 * i + 3))), .store (at_ r (off + 8 * i)) .r9]

/-- A loop of `n` iterations of `body`, counted down in `rcx`. -/
def rcxLoop (n : Nat) (body : List Instr) : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm (BitVec.ofNat 32 n))])
    (.loop (.block (body ++ [.alu .sub .rcx (.imm 1)])) .ne)

/-- The 256 `u32`s at `[r9]` to words at `[rdx]`, eight at a time. -/
def vpack : Prog isa :=
  rcxLoop 32 [.movdquLoad .xmm0 (at_ .r9 0), .movdquLoad .xmm1 (at_ .r9 16), xb .packssdw .xmm0 .xmm1,
    .movdquStore (at_ .rdx 0) .xmm0, .alu .add .r9 (.imm 32), .alu .add .rdx (.imm 16)]

/-- The 256 words at `[rdx]` to `u32`s at `[r9]`, eight at a time. -/
def vunpack : Prog isa :=
  .seq (.block [xb .pxor .xmm4 .xmm4])
    (rcxLoop 32 [.movdquLoad .xmm0 (at_ .rdx 0), xmov .xmm1 .xmm0, xb .punpcklwd .xmm0 .xmm4,
      xb .punpckhwd .xmm1 .xmm4, .movdquStore (at_ .r9 0) .xmm0, .movdquStore (at_ .r9 16) .xmm1,
      .alu .add .r9 (.imm 32), .alu .add .rdx (.imm 16)])

end VG.Impl.MlKem.X86_64
