import RindIsa.X86_64

/-!
# aws-lc's `bn_mul4x_mont`

rind's naked function `low::x86_64::mont::bn_mul4x_mont`, aws-lc's
`bn_mul4x_mont` (`crypto/fipsmodule/bn/asm/x86_64-mont.pl`), in rind's model
of x86_64: `bn_mul4x_mont(rp = rdi, ap = rsi, bp = rdx, np = rcx, n0 = r8,
num = r9)`, the Montgomery product `rp = ap * bp / 2^(64 num) mod np` of
`num`-word operands, `num` a multiple of four from eight, given the word at
`n0` is `-np^-1 mod 2^64`. Word-serial, as `bn_mul_mont_nohw`, four words a
loop: each pass adds `ap * bp[i] + q * np` to the `num + 1` words `t` at the
stack pointer, with `q` the word that zeroes its low word, and shifts it down
a word; the last subtracts `np` from `t` into `rp`, and selects `t` or the
difference by the borrow, zeroing `t`.

`admin/prove lean` checks that `function prog repRet` is the function's
bytes as rind's Linux release build emits it, from aws-lc's text, which the
blocks below follow line for line.
-/

namespace Rind.X86_64.Mul4x

open VG VG.X86_64

/-- `[b + d]` -/
def m (b : Reg) (d : Int) : MemOp := { base := b, disp := d }
/-- `[b + i * s + d]` -/
def mx (b i : Reg) (s : Nat) (d : Int) : MemOp := { base := b, index := some i, scale := s, disp := d }

/-- Save the callee-saved registers and the stack pointer, and move `rsp` down to the scratch space, at most a page from where it was, probing it. -/
def prologue : List Instr :=
  [.vg (.mov32 .r9 (.reg .r9)),
   .vg (.mov .rax (.reg .rsp)),
   .push .rbx,
   .push .rbp,
   .push .r12,
   .push .r13,
   .push .r14,
   .push .r15,
   .neg .r9,
   .vg (.mov .r11 (.reg .rsp)),
   .lea .r10 (mx .rsp .r9 8 (-32)),
   .neg .r9,
   .vg (.alu .and .r10 (.imm (-1024))),
   .vg (.alu .sub .r11 (.reg .r10)),
   .vg (.alu .and .r11 (.imm (-4096))),
   .leaRsp (mx .r10 .r11 1 0),
   .vg (.mov .r11 (.mem (m .rsp 0))),
   .vg (.alu .cmp .rsp (.reg .r10))]

/-- Move `rsp` down a page more, probing it. -/
def walk : List Instr :=
  [.leaRsp (m .rsp (-4096)),
   .vg (.mov .r11 (.mem (m .rsp 0))),
   .vg (.alu .cmp .rsp (.reg .r10))]

/-- Save the old stack pointer and `rp`, load `n0`, `b[0]`, and `a[0]`, and run the first pass's first two words. -/
def body0 : List Instr :=
  [.vg (.store (mx .rsp .r9 8 8) .rax),
   .vg (.store (mx .rsp .r9 8 16) .rdi),
   .vg (.mov .r12 (.reg .rdx)),
   .vg (.mov .r8 (.mem (m .r8 0))),
   .vg (.mov .rbx (.mem (m .r12 0))),
   .vg (.mov .rax (.mem (m .rsi 0))),
   .vg (.alu .xor .r14 (.reg .r14)),
   .vg (.alu .xor .r15 (.reg .r15)),
   .vg (.mov .rbp (.reg .r8)),
   .vg (.mul .rbx),
   .vg (.mov .r10 (.reg .rax)),
   .vg (.mov .rax (.mem (m .rcx 0))),
   .vg (.imul .rbp .r10),
   .vg (.mov .r11 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .r10 (.reg .rax)),
   .vg (.mov .rax (.mem (m .rsi 8))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.mov .rdi (.reg .rdx)),
   .vg (.mul .rbx),
   .vg (.alu .add .r11 (.reg .rax)),
   .vg (.mov .rax (.mem (m .rcx 8))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.mov .r10 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .rdi (.reg .rax)),
   .vg (.mov .rax (.mem (m .rsi 16))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .rdi (.reg .r11)),
   .lea .r15 (m .r15 4),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.store (m .rsp 0) .rdi),
   .vg (.mov .r13 (.reg .rdx)),
   .jmpAlign 16]

/-- Four words of the first pass: `t = (a * b[0] + q * n) / 2^64`. -/
def first : List Instr :=
  [.vg (.mul .rbx),
   .vg (.alu .add .r10 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rcx .r15 8 (-16)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.mov .r11 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .r13 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rsi .r15 8 (-8)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .r13 (.reg .r10)),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.store (mx .rsp .r15 8 (-24)) .r13),
   .vg (.mov .rdi (.reg .rdx)),
   .vg (.mul .rbx),
   .vg (.alu .add .r11 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rcx .r15 8 (-8)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.mov .r10 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .rdi (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rsi .r15 8 0))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .rdi (.reg .r11)),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.store (mx .rsp .r15 8 (-16)) .rdi),
   .vg (.mov .r13 (.reg .rdx)),
   .vg (.mul .rbx),
   .vg (.alu .add .r10 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rcx .r15 8 0))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.mov .r11 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .r13 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rsi .r15 8 8))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .r13 (.reg .r10)),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.store (mx .rsp .r15 8 (-8)) .r13),
   .vg (.mov .rdi (.reg .rdx)),
   .vg (.mul .rbx),
   .vg (.alu .add .r11 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rcx .r15 8 8))),
   .vg (.alu .adc .rdx (.imm 0)),
   .lea .r15 (m .r15 4),
   .vg (.mov .r10 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .rdi (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rsi .r15 8 (-16)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .rdi (.reg .r11)),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.store (mx .rsp .r15 8 (-32)) .rdi),
   .vg (.mov .r13 (.reg .rdx)),
   .vg (.alu .cmp .r15 (.reg .r9))]

/-- The first pass's last two words and its top word. -/
def firstTail : List Instr :=
  [.vg (.mul .rbx),
   .vg (.alu .add .r10 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rcx .r15 8 (-16)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.mov .r11 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .r13 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rsi .r15 8 (-8)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .r13 (.reg .r10)),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.store (mx .rsp .r15 8 (-24)) .r13),
   .vg (.mov .rdi (.reg .rdx)),
   .vg (.mul .rbx),
   .vg (.alu .add .r11 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rcx .r15 8 (-8)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.mov .r10 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .rdi (.reg .rax)),
   .vg (.mov .rax (.mem (m .rsi 0))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .rdi (.reg .r11)),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.store (mx .rsp .r15 8 (-16)) .rdi),
   .vg (.mov .r13 (.reg .rdx)),
   .vg (.alu .xor .rdi (.reg .rdi)),
   .vg (.alu .add .r13 (.reg .r10)),
   .vg (.alu .adc .rdi (.imm 0)),
   .vg (.store (mx .rsp .r15 8 (-8)) .r13),
   .vg (.store (mx .rsp .r15 8 0) .rdi),
   .lea .r14 (m .r14 1)]

/-- An outer pass's first two words, for `b[i]`. -/
def outerHead : List Instr :=
  [.align 4,
   .vg (.mov .rbx (.mem (mx .r12 .r14 8 0))),
   .vg (.alu .xor .r15 (.reg .r15)),
   .vg (.mov .r10 (.mem (m .rsp 0))),
   .vg (.mov .rbp (.reg .r8)),
   .vg (.mul .rbx),
   .vg (.alu .add .r10 (.reg .rax)),
   .vg (.mov .rax (.mem (m .rcx 0))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.imul .rbp .r10),
   .vg (.mov .r11 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .r10 (.reg .rax)),
   .vg (.mov .rax (.mem (m .rsi 8))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.mov .rdi (.reg .rdx)),
   .vg (.mul .rbx),
   .vg (.alu .add .r11 (.reg .rax)),
   .vg (.mov .rax (.mem (m .rcx 8))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .r11 (.mem (m .rsp 8))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.mov .r10 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .rdi (.reg .rax)),
   .vg (.mov .rax (.mem (m .rsi 16))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .rdi (.reg .r11)),
   .lea .r15 (m .r15 4),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.store (m .rsp 0) .rdi),
   .vg (.mov .r13 (.reg .rdx)),
   .jmpAlign 16]

/-- Four words of an outer pass: `t = (t + a * b[i] + q * n) / 2^64`. -/
def inner : List Instr :=
  [.vg (.mul .rbx),
   .vg (.alu .add .r10 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rcx .r15 8 (-16)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .r10 (.mem (mx .rsp .r15 8 (-16)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.mov .r11 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .r13 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rsi .r15 8 (-8)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .r13 (.reg .r10)),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.store (mx .rsp .r15 8 (-24)) .r13),
   .vg (.mov .rdi (.reg .rdx)),
   .vg (.mul .rbx),
   .vg (.alu .add .r11 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rcx .r15 8 (-8)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .r11 (.mem (mx .rsp .r15 8 (-8)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.mov .r10 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .rdi (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rsi .r15 8 0))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .rdi (.reg .r11)),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.store (mx .rsp .r15 8 (-16)) .rdi),
   .vg (.mov .r13 (.reg .rdx)),
   .vg (.mul .rbx),
   .vg (.alu .add .r10 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rcx .r15 8 0))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .r10 (.mem (mx .rsp .r15 8 0))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.mov .r11 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .r13 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rsi .r15 8 8))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .r13 (.reg .r10)),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.store (mx .rsp .r15 8 (-8)) .r13),
   .vg (.mov .rdi (.reg .rdx)),
   .vg (.mul .rbx),
   .vg (.alu .add .r11 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rcx .r15 8 8))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .r11 (.mem (mx .rsp .r15 8 8))),
   .vg (.alu .adc .rdx (.imm 0)),
   .lea .r15 (m .r15 4),
   .vg (.mov .r10 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .rdi (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rsi .r15 8 (-16)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .rdi (.reg .r11)),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.store (mx .rsp .r15 8 (-32)) .rdi),
   .vg (.mov .r13 (.reg .rdx)),
   .vg (.alu .cmp .r15 (.reg .r9))]

/-- An outer pass's last two words and its top word. -/
def outerTail : List Instr :=
  [.vg (.mul .rbx),
   .vg (.alu .add .r10 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rcx .r15 8 (-16)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .r10 (.mem (mx .rsp .r15 8 (-16)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.mov .r11 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .r13 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rsi .r15 8 (-8)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .r13 (.reg .r10)),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.store (mx .rsp .r15 8 (-24)) .r13),
   .vg (.mov .rdi (.reg .rdx)),
   .vg (.mul .rbx),
   .vg (.alu .add .r11 (.reg .rax)),
   .vg (.mov .rax (.mem (mx .rcx .r15 8 (-8)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .r11 (.mem (mx .rsp .r15 8 (-8)))),
   .vg (.alu .adc .rdx (.imm 0)),
   .lea .r14 (m .r14 1),
   .vg (.mov .r10 (.reg .rdx)),
   .vg (.mul .rbp),
   .vg (.alu .add .rdi (.reg .rax)),
   .vg (.mov .rax (.mem (m .rsi 0))),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.alu .add .rdi (.reg .r11)),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.store (mx .rsp .r15 8 (-16)) .rdi),
   .vg (.mov .r13 (.reg .rdx)),
   .vg (.alu .xor .rdi (.reg .rdi)),
   .vg (.alu .add .r13 (.reg .r10)),
   .vg (.alu .adc .rdi (.imm 0)),
   .vg (.alu .add .r13 (.mem (mx .rsp .r9 8 0))),
   .vg (.alu .adc .rdi (.imm 0)),
   .vg (.store (mx .rsp .r15 8 (-8)) .r13),
   .vg (.store (mx .rsp .r15 8 0) .rdi),
   .vg (.alu .cmp .r14 (.reg .r9))]

/-- Start subtracting `n` from `t` into `rp`. -/
def final : List Instr :=
  [.vg (.mov .rdi (.mem (mx .rsp .r9 8 16))),
   .lea .r15 (m .r9 (-4)),
   .vg (.mov .rax (.mem (m .rsp 0))),
   .vg (.mov .rdx (.mem (m .rsp 8))),
   .vg (.shift .shr .r15 2),
   .lea .rsi (m .rsp 0),
   .vg (.alu .xor .r14 (.reg .r14)),
   .vg (.alu .sub .rax (.mem (m .rcx 0))),
   .vg (.mov .rbx (.mem (m .rsi 16))),
   .vg (.mov .rbp (.mem (m .rsi 24))),
   .vg (.alu .sbb .rdx (.mem (m .rcx 8)))]

/-- Four words of the subtraction. -/
def sub : List Instr :=
  [.vg (.store (mx .rdi .r14 8 0) .rax),
   .vg (.store (mx .rdi .r14 8 8) .rdx),
   .vg (.alu .sbb .rbx (.mem (mx .rcx .r14 8 16))),
   .vg (.mov .rax (.mem (mx .rsi .r14 8 32))),
   .vg (.mov .rdx (.mem (mx .rsi .r14 8 40))),
   .vg (.alu .sbb .rbp (.mem (mx .rcx .r14 8 24))),
   .vg (.store (mx .rdi .r14 8 16) .rbx),
   .vg (.store (mx .rdi .r14 8 24) .rbp),
   .vg (.alu .sbb .rax (.mem (mx .rcx .r14 8 32))),
   .vg (.mov .rbx (.mem (mx .rsi .r14 8 48))),
   .vg (.mov .rbp (.mem (mx .rsi .r14 8 56))),
   .vg (.alu .sbb .rdx (.mem (mx .rcx .r14 8 40))),
   .lea .r14 (m .r14 4),
   .dec .r15]

/-- The subtraction's last words, and the masks that select `t` where it borrowed. -/
def subTail : List Instr :=
  [.vg (.store (mx .rdi .r14 8 0) .rax),
   .vg (.mov .rax (.mem (mx .rsi .r14 8 32))),
   .vg (.alu .sbb .rbx (.mem (mx .rcx .r14 8 16))),
   .vg (.store (mx .rdi .r14 8 8) .rdx),
   .vg (.alu .sbb .rbp (.mem (mx .rcx .r14 8 24))),
   .vg (.store (mx .rdi .r14 8 16) .rbx),
   .vg (.alu .sbb .rax (.imm 0)),
   .vg (.store (mx .rdi .r14 8 24) .rbp),
   .vg (.xop (.bin .pxor .xmm0 .xmm0)),
   .vg (.xop (.movq .xmm4 .rax)),
   .vg (.xop (.bin .pcmpeqd .xmm5 .xmm5)),
   .vg (.xop (.pshufd .xmm4 .xmm4 0)),
   .vg (.mov .r15 (.reg .r9)),
   .vg (.xop (.bin .pxor .xmm5 .xmm4)),
   .vg (.shift .shr .r15 2),
   .vg (.alu32 .xor .rax (.reg .rax)),
   .jmpAlign 16]

/-- Four words of the selection into `rp`, zeroing `t`. -/
def copy : List Instr :=
  [.movdqaLoad .xmm1 (mx .rsp .rax 1 0),
   .vg (.movdquLoad .xmm2 (mx .rdi .rax 1 0)),
   .vg (.xop (.bin .pand .xmm1 .xmm4)),
   .vg (.xop (.bin .pand .xmm2 .xmm5)),
   .movdqaLoad .xmm3 (mx .rsp .rax 1 16),
   .movdqaStore (mx .rsp .rax 1 0) .xmm0,
   .vg (.xop (.bin .por .xmm1 .xmm2)),
   .vg (.movdquLoad .xmm2 (mx .rdi .rax 1 16)),
   .vg (.movdquStore (mx .rdi .rax 1 0) .xmm1),
   .vg (.xop (.bin .pand .xmm3 .xmm4)),
   .vg (.xop (.bin .pand .xmm2 .xmm5)),
   .movdqaStore (mx .rsp .rax 1 16) .xmm0,
   .vg (.xop (.bin .por .xmm3 .xmm2)),
   .vg (.movdquStore (mx .rdi .rax 1 16) .xmm3),
   .lea .rax (m .rax 32),
   .dec .r15]

/-- Restore the callee-saved registers and the stack pointer, and return 1. -/
def epilogue : List Instr :=
  [.vg (.mov .rsi (.mem (mx .rsp .r9 8 8))),
   .vg (.mov .rax (.imm 1)),
   .vg (.mov .r15 (.mem (m .rsi (-48)))),
   .vg (.mov .r14 (.mem (m .rsi (-40)))),
   .vg (.mov .r13 (.mem (m .rsi (-32)))),
   .vg (.mov .r12 (.mem (m .rsi (-24)))),
   .vg (.mov .rbp (.mem (m .rsi (-16)))),
   .vg (.mov .rbx (.mem (m .rsi (-8)))),
   .leaRsp (m .rsi 0)]
/-- The function's body, before its `rep ret`. -/
def prog : Prog isa :=
  .seq (.block prologue) <|
  .seq (.ite .a (.loop (.block walk) .a) (.block [])) <|
  .seq (.block body0) <|
  .seq (.loop (.block first) (.vg .b)) <|
  .seq (.block firstTail) <|
  .seq (.loop (.seq (.block outerHead) (.seq (.loop (.block inner) (.vg .b)) (.block outerTail))) (.vg .b)) <|
  .seq (.block final) <|
  .seq (.loop (.block sub) (.vg .ne)) <|
  .seq (.block subTail) <|
  .seq (.loop (.block copy) (.vg .ne)) <|
  .block epilogue

end Rind.X86_64.Mul4x
