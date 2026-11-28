import RindIsa.X86_64.Sqrx8x

/-!
# rind's structured copy of aws-lc's `bn_sqr8x_mont`, by `bn_sqrx8x_internal`

rind's naked function `low::x86_64::mont::bn_sqrx8x_mont`, aws-lc's
`bn_sqr8x_mont` (`crypto/fipsmodule/bn/asm/x86_64-mont.pl`) for CPUs with
BMI2 and ADX, in rind's model of x86_64: `bn_sqrx8x_mont(rp = rdi, ap = rsi,
np = rcx, n0 = r8, num = r9)`, the Montgomery square `rp = ap^2 / 2^(64 num)
mod np` of `num`-word operands, `num` a multiple of eight from eight, given
the word at `n0` is `-np^-1 mod 2^64`; it ignores `rdx`, where aws-lc reads
whether to square by `mulx`. It saves the callee-saved registers and the
stack pointer, moves `rsp` down to a frame of `2 num + 8` words 64-byte
aligned, nudged a page lower if it would share `ap`'s offset within a page,
probing each page; stores `n0` and the old stack pointer in the frame, zeroes
`t`'s last two words, and calls `bn_sqrx8x_internal` (`Sqrx8x.prog`), which
leaves `t`'s upper half and a carry; subtracts `np` from them into `rp`; and
selects the difference or `t`'s upper half by the borrow, zeroing `t`.

`rind/src/low/x86_64/sqrx8x_mont.s` is aws-lc's text without its test of
`rdx` and its branch to `bn_sqr8x_internal`, its other loops already of the
structure `layout` lays out; the frame's alternative bound `4096 - 64 + 2
r9` is `lea r10, [r9 + r9 + 4032]` rather than aws-lc's `lea r10, [r9 * 2 +
4032]`, which has no base, the same value in as many bytes. `admin/prove
lean` checks that `function prog` is the function's bytes as rind's Linux
release build emits it, with the call's relocation to `bn_sqrx8x_internal`.
-/

namespace Rind.X86_64.Sqrx8xMont

open VG VG.X86_64 Rind.X86_64.Mul4x

/-- Save the callee-saved registers and the stack pointer, zero-extend `num`, load `n0`, and test whether the
frame below `rsp` would share `ap`'s offset within a page. -/
def prologue : List Instr :=
  [.vg (.mov32 .r9 (.reg .r9)),
   .vg (.mov .rax (.reg .rsp)),
   .push .rbx,
   .push .rbp,
   .push .r12,
   .push .r13,
   .push .r14,
   .push .r15,
   .vg (.mov32 .r10 (.reg .r9)),
   .vg (.shift32 .shl .r9 3),
   .vg (.shift .shl .r10 5),
   .neg .r9,
   .lea .r11 (mx .rsp .r9 2 (-64)),
   .vg (.mov .rbp (.reg .rsp)),
   .vg (.mov .r8 (.mem (m .r8 0))),
   .vg (.alu .sub .r11 (.reg .rsi)),
   .vg (.alu .and .r11 (.imm 4095)),
   .vg (.alu .cmp .r10 (.reg .r11))]

/-- The frame's bottom, `2 num + 8` words below `rsp`, moved below `ap`'s offset within the page. -/
def spNear : List Instr :=
  [.vg (.alu .sub .rbp (.reg .r11)),
   .lea .rbp (mx .rbp .r9 2 (-64))]

/-- The frame's bottom, moved down by what `ap`'s offset within the page exceeds the frame by, if it does. -/
def spAlt : List Instr :=
  [.lea .r10 (mx .r9 .r9 1 4032),
   .lea .rbp (mx .rbp .r9 2 (-64)),
   .vg (.alu .sub .r11 (.reg .r10)),
   .vg (.mov .r10 (.imm 0)),
   .vg (.cmov .b .r11 (.reg .r10)),
   .vg (.alu .sub .rbp (.reg .r11))]

/-- Align the frame's bottom to 64 bytes, and move `rsp` down to it, at most a page from where it was, probing
it. -/
def frame : List Instr :=
  [.vg (.alu .and .rbp (.imm (-64))),
   .vg (.mov .r11 (.reg .rsp)),
   .vg (.alu .sub .r11 (.reg .rbp)),
   .vg (.alu .and .r11 (.imm (-4096))),
   .leaRsp (mx .r11 .rbp 1 0),
   .vg (.mov .r10 (.mem (m .rsp 0))),
   .vg (.alu .cmp .rsp (.reg .rbp))]

/-- Move `rsp` down a page more, probing it. -/
def walk : List Instr :=
  [.leaRsp (m .rsp (-4096)),
   .vg (.mov .r10 (.mem (m .rsp 0))),
   .vg (.alu .cmp .rsp (.reg .rbp))]

/-- Save `n0` and the old stack pointer, pass `np`, `rp`, `-8 num`, and zero in XMM registers, and zero `t`'s last
two words. -/
def setup : List Instr :=
  [.vg (.mov .r10 (.reg .r9)),
   .neg .r9,
   .vg (.store (m .rsp 32) .r8),
   .vg (.store (m .rsp 40) .rax),
   .vg (.xop (.movq .xmm2 .rcx)),
   .vg (.xop (.bin .pxor .xmm0 .xmm0)),
   .vg (.xop (.movq .xmm1 .rdi)),
   .vg (.xop (.movq .xmm3 .r10)),
   .vg (.movdquStore (mx .rsp .r9 2 48) .xmm0)]

/-- Point `rbx` at `t`'s upper half and `rdi` at `rp`, and count the subtraction's four-word steps in `rcx`,
whose shift leaves CF clear. -/
def post : List Instr :=
  [.lea .rbx (mx .r8 .rcx 1 0),
   .vg (.mov .r9 (.reg .rcx)),
   .vg (.mov .rdx (.reg .rcx)),
   .vg (.movqR .rdi .xmm1),
   .sar .rcx 5,
   .jmpAlign 32]

/-- Four words of `t`'s upper half less `np`'s, with the borrow, into `rp`. -/
def sub : List Instr :=
  [.vg (.mov .r12 (.mem (m .rbx 0))),
   .vg (.mov .r13 (.mem (m .rbx 8))),
   .vg (.mov .r14 (.mem (m .rbx 16))),
   .vg (.mov .r15 (.mem (m .rbx 24))),
   .lea .rbx (m .rbx 32),
   .vg (.alu .sbb .r12 (.mem (m .rbp 0))),
   .vg (.alu .sbb .r13 (.mem (m .rbp 8))),
   .vg (.alu .sbb .r14 (.mem (m .rbp 16))),
   .vg (.alu .sbb .r15 (.mem (m .rbp 24))),
   .lea .rbp (m .rbp 32),
   .vg (.store (m .rdi 0) .r12),
   .vg (.store (m .rdi 8) .r13),
   .vg (.store (m .rdi 16) .r14),
   .vg (.store (m .rdi 24) .r15),
   .lea .rdi (m .rdi 32),
   .inc .rcx]

/-- The borrow out of `t`'s carry word as a mask in every lane of `xmm1`, `rbx` and `rdi` back at the starts of
`t`'s upper half and `rp`, and the old stack pointer in `rsi`. -/
def subTail : List Instr :=
  [.vg (.alu .sbb .rax (.imm 0)),
   .lea .rbx (mx .rbx .r9 1 0),
   .lea .rdi (mx .rdi .r9 1 0),
   .vg (.xop (.movq .xmm1 .rax)),
   .vg (.xop (.bin .pxor .xmm0 .xmm0)),
   .vg (.xop (.pshufd .xmm1 .xmm1 0)),
   .vg (.mov .rsi (.mem (m .rsp 40))),
   .jmpAlign 32]

/-- Four words of `rp`: `t`'s upper half where the mask is set, the difference already there where it is clear;
zeroing those words of `t` and the four `num` words below. -/
def copy : List Instr :=
  [.movdqaLoad .xmm2 (m .rbx 0),
   .movdqaLoad .xmm3 (m .rbx 16),
   .lea .rbx (m .rbx 32),
   .vg (.movdquLoad .xmm4 (m .rdi 0)),
   .vg (.movdquLoad .xmm5 (m .rdi 16)),
   .lea .rdi (m .rdi 32),
   .movdqaStore (m .rbx (-32)) .xmm0,
   .movdqaStore (m .rbx (-16)) .xmm0,
   .movdqaStore (mx .rbx .rdx 1 (-32)) .xmm0,
   .movdqaStore (mx .rbx .rdx 1 (-16)) .xmm0,
   .vg (.xop (.bin .pcmpeqd .xmm0 .xmm1)),
   .vg (.xop (.bin .pand .xmm2 .xmm1)),
   .vg (.xop (.bin .pand .xmm3 .xmm1)),
   .vg (.xop (.bin .pand .xmm4 .xmm0)),
   .vg (.xop (.bin .pand .xmm5 .xmm0)),
   .vg (.xop (.bin .pxor .xmm0 .xmm0)),
   .vg (.xop (.bin .por .xmm4 .xmm2)),
   .vg (.xop (.bin .por .xmm5 .xmm3)),
   .vg (.movdquStore (m .rdi (-32)) .xmm4),
   .vg (.movdquStore (m .rdi (-16)) .xmm5),
   .vg (.alu .add .r9 (.imm 32))]

/-- Return 1, restoring the callee-saved registers and the stack pointer. -/
def epilogue : List Instr :=
  [.vg (.mov .rax (.imm 1)),
   .vg (.mov .r15 (.mem (m .rsi (-48)))),
   .vg (.mov .r14 (.mem (m .rsi (-40)))),
   .vg (.mov .r13 (.mem (m .rsi (-32)))),
   .vg (.mov .r12 (.mem (m .rsi (-24)))),
   .vg (.mov .rbp (.mem (m .rsi (-16)))),
   .vg (.mov .rbx (.mem (m .rsi (-8)))),
   .leaRsp (m .rsi 0)]

/-- The Rust path of the function the routine calls, as `RindIsa/Proven.lean` names it. -/
def internal : String := "rind::low::x86_64::mont::bn_sqrx8x_internal"

def prog : Prog isa :=
  .seq (.block prologue) <|
  .seq (.ite (.vg .b) (.seq (.block [.align 32]) (.block spAlt)) (.block spNear)) <|
  .seq (.block frame) <|
  .seq (.ite .a (.loop (.seq (.block [.align 16]) (.block walk)) .a) (.block [])) <|
  .seq (.block setup) <|
  .seq (.call internal Sqrx8x.prog) <|
  .seq (.block post) <|
  .seq (.loop (.block sub) (.vg .ne)) <|
  .seq (.block subTail) <|
  .seq (.loop (.block copy) (.vg .ne)) <|
  .block epilogue

end Rind.X86_64.Sqrx8xMont
