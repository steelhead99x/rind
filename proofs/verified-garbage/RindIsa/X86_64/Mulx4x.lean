import RindIsa.X86_64.Mul4x

/-!
# aws-lc's `bn_mulx4x_mont`

rind's naked function `low::x86_64::mont::bn_mulx4x_mont`, aws-lc's
`bn_mulx4x_mont` (`crypto/fipsmodule/bn/asm/x86_64-mont.pl`), in rind's
model of x86_64: `bn_mulx4x_mont(rp = rdi, ap = rsi, bp = rdx, np = rcx,
n0 = r8, num = r9)`, the Montgomery product `rp = ap * bp / 2^(64 num) mod
np` of `num`-word operands, `num` a multiple of four from eight, given the
word at `n0` is `-np^-1 mod 2^64`, by BMI2's `mulx` and ADX's `adcx` and
`adox`. Word-serial, as `bn_mul4x_mont`, four words a loop: each pass adds
`ap * bp[i] + q * np` to the `num + 1` words `t` 64 bytes above the stack
pointer, with `q` the word that zeroes its low word, and shifts it down a
word, carrying the top word as its negation; the last subtracts `np` from
`t` into `rp`, and selects `t` or the difference by the borrow, zeroing `t`.
Below `t` it keeps `8 num`, `bp`'s next word's address, `bp`'s end, `n0`,
`rp`, the stack pointer it was called with, and the inner loops' count.

`admin/prove lean` checks that `function prog` is the function's bytes as
rind's Linux release build emits it, from aws-lc's text, which the blocks
below follow line for line.
-/

namespace Rind.X86_64.Mulx4x

open VG VG.X86_64 Rind.X86_64.Mul4x

/-- Save the callee-saved registers and the stack pointer, load `n0`, and
move `rsp` down to the scratch space, at most a page from where it was,
probing it. -/
def prologue : List Instr :=
  [.vg (.mov .rax (.reg .rsp)),
   .push .rbx,
   .push .rbp,
   .push .r12,
   .push .r13,
   .push .r14,
   .push .r15,
   .vg (.shift32 .shl .r9 3),
   .vg (.alu .xor .r10 (.reg .r10)),
   .vg (.alu .sub .r10 (.reg .r9)),
   .vg (.mov .r8 (.mem (m .r8 0))),
   .lea .rbp (mx .rsp .r10 1 (-72)),
   .vg (.alu .and .rbp (.imm (-128))),
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

/-- Save `8 num`, `bp`'s end, `n0`, `rp`, the old stack pointer, and the inner loops' count. -/
def setup : List Instr :=
  [.lea .r10 (mx .rdx .r9 1 0),
   .vg (.store (m .rsp 0) .r9),
   .vg (.shift .shr .r9 5),
   .vg (.store (m .rsp 16) .r10),
   .vg (.alu .sub .r9 (.imm 1)),
   .vg (.store (m .rsp 24) .r8),
   .vg (.store (m .rsp 32) .rdi),
   .vg (.store (m .rsp 40) .rax),
   .vg (.store (m .rsp 48) .r9),
   .jmpAlign 32]

/-- Load `b[0]`, and run the first pass's first four words. -/
def body0 : List Instr :=
  [.lea .rdi (m .rdx 8),
   .vg (.mov .rdx (.mem (m .rdx 0))),
   .lea .rbx (m .rsp 96),
   .vg (.mov .r9 (.reg .rdx)),
   .vg (.mulx .rax .r8 (.mem (m .rsi 0))),
   .vg (.mulx .r14 .r11 (.mem (m .rsi 8))),
   .vg (.alu .add .r11 (.reg .rax)),
   .vg (.store (m .rsp 8) .rdi),
   .vg (.mulx .r13 .r12 (.mem (m .rsi 16))),
   .vg (.alu .adc .r12 (.reg .r14)),
   .vg (.alu .adc .r13 (.imm 0)),
   .vg (.mov .rdi (.reg .r8)),
   .imulMem .r8 (m .rsp 24),
   .vg (.alu .xor .rbp (.reg .rbp)),
   .vg (.mulx .r14 .rax (.mem (m .rsi 24))),
   .vg (.mov .rdx (.reg .r8)),
   .lea .rsi (m .rsi 32),
   .vg (.adcx .r13 (.reg .rax)),
   .vg (.adcx .r14 (.reg .rbp)),
   .vg (.mulx .r10 .rax (.mem (m .rcx 0))),
   .vg (.adcx .rdi (.reg .rax)),
   .vg (.adox .r10 (.reg .r11)),
   .vg (.mulx .r11 .rax (.mem (m .rcx 8))),
   .vg (.adcx .r10 (.reg .rax)),
   .vg (.adox .r11 (.reg .r12)),
   .mulxD32 .r12 .rax (m .rcx 16),
   .vg (.mov .rdi (.mem (m .rsp 48))),
   .vg (.store (m .rbx (-32)) .r10),
   .vg (.adcx .r11 (.reg .rax)),
   .vg (.adox .r12 (.reg .r13)),
   .vg (.mulx .r15 .rax (.mem (m .rcx 24))),
   .vg (.mov .rdx (.reg .r9)),
   .vg (.store (m .rbx (-24)) .r11),
   .vg (.adcx .r12 (.reg .rax)),
   .vg (.adox .r15 (.reg .rbp)),
   .lea .rcx (m .rcx 32),
   .vg (.store (m .rbx (-16)) .r12),
   .jmpAlign 32]

/-- Four words of the first pass: `t = (a * b[0] + q * n) / 2^64`. -/
def first : List Instr :=
  [.vg (.adcx .r15 (.reg .rbp)),
   .vg (.mulx .rax .r10 (.mem (m .rsi 0))),
   .vg (.adcx .r10 (.reg .r14)),
   .vg (.mulx .r14 .r11 (.mem (m .rsi 8))),
   .vg (.adcx .r11 (.reg .rax)),
   .vg (.mulx .rax .r12 (.mem (m .rsi 16))),
   .vg (.adcx .r12 (.reg .r14)),
   .vg (.mulx .r14 .r13 (.mem (m .rsi 24))),
   .movPad 2 .rdx .r8,
   .vg (.adcx .r13 (.reg .rax)),
   .vg (.adcx .r14 (.reg .rbp)),
   .lea .rsi (m .rsi 32),
   .lea .rbx (m .rbx 32),
   .vg (.adox .r10 (.reg .r15)),
   .vg (.mulx .r15 .rax (.mem (m .rcx 0))),
   .vg (.adcx .r10 (.reg .rax)),
   .vg (.adox .r11 (.reg .r15)),
   .vg (.mulx .r15 .rax (.mem (m .rcx 8))),
   .vg (.adcx .r11 (.reg .rax)),
   .vg (.adox .r12 (.reg .r15)),
   .vg (.mulx .r15 .rax (.mem (m .rcx 16))),
   .vg (.store (m .rbx (-40)) .r10),
   .vg (.adcx .r12 (.reg .rax)),
   .vg (.store (m .rbx (-32)) .r11),
   .vg (.adox .r13 (.reg .r15)),
   .vg (.mulx .r15 .rax (.mem (m .rcx 24))),
   .vg (.mov .rdx (.reg .r9)),
   .vg (.store (m .rbx (-24)) .r12),
   .vg (.adcx .r13 (.reg .rax)),
   .vg (.adox .r15 (.reg .rbp)),
   .lea .rcx (m .rcx 32),
   .vg (.store (m .rbx (-16)) .r13),
   .dec .rdi]

/-- The first pass's top two words. -/
def firstTail : List Instr :=
  [.vg (.mov .rax (.mem (m .rsp 0))),
   .vg (.mov .rdi (.mem (m .rsp 8))),
   .vg (.alu .adc .r15 (.reg .rbp)),
   .vg (.alu .add .r14 (.reg .r15)),
   .vg (.alu .sbb .r15 (.reg .r15)),
   .vg (.store (m .rbx (-8)) .r14),
   .jmpAlign 32]

/-- An outer pass's first four words, for `b[i]`. -/
def outerHead : List Instr :=
  [.vg (.mov .rdx (.mem (m .rdi 0))),
   .lea .rdi (m .rdi 8),
   .vg (.alu .sub .rsi (.reg .rax)),
   .vg (.store (m .rbx 0) .r15),
   .lea .rbx (m .rsp 96),
   .vg (.alu .sub .rcx (.reg .rax)),
   .vg (.mulx .r11 .r8 (.mem (m .rsi 0))),
   .vg (.alu32 .xor .rbp (.reg .rbp)),
   .vg (.mov .r9 (.reg .rdx)),
   .vg (.mulx .r12 .r14 (.mem (m .rsi 8))),
   .vg (.adox .r8 (.mem (m .rbx (-32)))),
   .vg (.adcx .r11 (.reg .r14)),
   .vg (.mulx .r13 .r15 (.mem (m .rsi 16))),
   .vg (.adox .r11 (.mem (m .rbx (-24)))),
   .vg (.adcx .r12 (.reg .r15)),
   .vg (.adox .r12 (.mem (m .rbx (-16)))),
   .vg (.adcx .r13 (.reg .rbp)),
   .vg (.adox .r13 (.reg .rbp)),
   .vg (.store (m .rsp 8) .rdi),
   .vg (.mov .r15 (.reg .r8)),
   .imulMem .r8 (m .rsp 24),
   .vg (.alu32 .xor .rbp (.reg .rbp)),
   .vg (.mulx .r14 .rax (.mem (m .rsi 24))),
   .vg (.mov .rdx (.reg .r8)),
   .vg (.adcx .r13 (.reg .rax)),
   .vg (.adox .r13 (.mem (m .rbx (-8)))),
   .vg (.adcx .r14 (.reg .rbp)),
   .lea .rsi (m .rsi 32),
   .vg (.adox .r14 (.reg .rbp)),
   .vg (.mulx .r10 .rax (.mem (m .rcx 0))),
   .vg (.adcx .r15 (.reg .rax)),
   .vg (.adox .r10 (.reg .r11)),
   .vg (.mulx .r11 .rax (.mem (m .rcx 8))),
   .vg (.adcx .r10 (.reg .rax)),
   .vg (.adox .r11 (.reg .r12)),
   .vg (.mulx .r12 .rax (.mem (m .rcx 16))),
   .vg (.store (m .rbx (-32)) .r10),
   .vg (.adcx .r11 (.reg .rax)),
   .vg (.adox .r12 (.reg .r13)),
   .vg (.mulx .r15 .rax (.mem (m .rcx 24))),
   .vg (.mov .rdx (.reg .r9)),
   .vg (.store (m .rbx (-24)) .r11),
   .lea .rcx (m .rcx 32),
   .vg (.adcx .r12 (.reg .rax)),
   .vg (.adox .r15 (.reg .rbp)),
   .vg (.mov .rdi (.mem (m .rsp 48))),
   .vg (.store (m .rbx (-16)) .r12),
   .jmpAlign 32]

/-- Four words of an outer pass: `t = (t + a * b[i] + q * n) / 2^64`. -/
def inner : List Instr :=
  [.vg (.mulx .rax .r10 (.mem (m .rsi 0))),
   .vg (.adcx .r15 (.reg .rbp)),
   .vg (.adox .r10 (.reg .r14)),
   .vg (.mulx .r14 .r11 (.mem (m .rsi 8))),
   .vg (.adcx .r10 (.mem (m .rbx 0))),
   .vg (.adox .r11 (.reg .rax)),
   .vg (.mulx .rax .r12 (.mem (m .rsi 16))),
   .vg (.adcx .r11 (.mem (m .rbx 8))),
   .vg (.adox .r12 (.reg .r14)),
   .vg (.mulx .r14 .r13 (.mem (m .rsi 24))),
   .vg (.mov .rdx (.reg .r8)),
   .vg (.adcx .r12 (.mem (m .rbx 16))),
   .vg (.adox .r13 (.reg .rax)),
   .vg (.adcx .r13 (.mem (m .rbx 24))),
   .vg (.adox .r14 (.reg .rbp)),
   .lea .rsi (m .rsi 32),
   .lea .rbx (m .rbx 32),
   .vg (.adcx .r14 (.reg .rbp)),
   .vg (.adox .r10 (.reg .r15)),
   .vg (.mulx .r15 .rax (.mem (m .rcx 0))),
   .vg (.adcx .r10 (.reg .rax)),
   .vg (.adox .r11 (.reg .r15)),
   .vg (.mulx .r15 .rax (.mem (m .rcx 8))),
   .vg (.adcx .r11 (.reg .rax)),
   .vg (.adox .r12 (.reg .r15)),
   .vg (.mulx .r15 .rax (.mem (m .rcx 16))),
   .vg (.store (m .rbx (-40)) .r10),
   .vg (.adcx .r12 (.reg .rax)),
   .vg (.adox .r13 (.reg .r15)),
   .vg (.mulx .r15 .rax (.mem (m .rcx 24))),
   .vg (.mov .rdx (.reg .r9)),
   .vg (.store (m .rbx (-32)) .r11),
   .vg (.store (m .rbx (-24)) .r12),
   .vg (.adcx .r13 (.reg .rax)),
   .vg (.adox .r15 (.reg .rbp)),
   .lea .rcx (m .rcx 32),
   .vg (.store (m .rbx (-16)) .r13),
   .dec .rdi]

/-- An outer pass's top two words, and whether `b` has words left. -/
def outerTail : List Instr :=
  [.vg (.mov .rax (.mem (m .rsp 0))),
   .vg (.mov .rdi (.mem (m .rsp 8))),
   .vg (.alu .adc .r15 (.reg .rbp)),
   .vg (.alu .sub .rbp (.mem (m .rbx 0))),
   .vg (.alu .adc .r14 (.reg .r15)),
   .vg (.alu .sbb .r15 (.reg .r15)),
   .vg (.store (m .rbx (-8)) .r14),
   .vg (.alu .cmp .rdi (.mem (m .rsp 16)))]

/-- Rewind `np`, take the top word's carry, and start subtracting `n` from `t` into `rp`. -/
def final : List Instr :=
  [.lea .rbx (m .rsp 64),
   .vg (.alu .sub .rcx (.reg .rax)),
   .neg .r15,
   .vg (.mov .rdx (.reg .rax)),
   .vg (.shift .shr .rax 5),
   .vg (.mov .rdi (.mem (m .rsp 32))),
   .jmpAlign 32]

/-- Four words of the subtraction. -/
def sub : List Instr :=
  [.vg (.mov .r11 (.mem (m .rbx 0))),
   .vg (.mov .r12 (.mem (m .rbx 8))),
   .vg (.mov .r13 (.mem (m .rbx 16))),
   .vg (.mov .r14 (.mem (m .rbx 24))),
   .lea .rbx (m .rbx 32),
   .vg (.alu .sbb .r11 (.mem (m .rcx 0))),
   .vg (.alu .sbb .r12 (.mem (m .rcx 8))),
   .vg (.alu .sbb .r13 (.mem (m .rcx 16))),
   .vg (.alu .sbb .r14 (.mem (m .rcx 24))),
   .lea .rcx (m .rcx 32),
   .vg (.store (m .rdi 0) .r11),
   .vg (.store (m .rdi 8) .r12),
   .vg (.store (m .rdi 16) .r13),
   .vg (.store (m .rdi 24) .r14),
   .lea .rdi (m .rdi 32),
   .dec .rax]

/-- The mask that selects `t` where the subtraction borrowed past the top word. -/
def subTail : List Instr :=
  [.vg (.alu .sbb .r15 (.imm 0)),
   .lea .rbx (m .rsp 64),
   .vg (.alu .sub .rdi (.reg .rdx)),
   .vg (.xop (.movq .xmm1 .r15)),
   .vg (.xop (.bin .pxor .xmm0 .xmm0)),
   .vg (.xop (.pshufd .xmm1 .xmm1 0)),
   .vg (.mov .rsi (.mem (m .rsp 40))),
   .jmpAlign 32]

/-- Four words of the selection into `rp`, zeroing `t`. -/
def copy : List Instr :=
  [.movdqaLoad .xmm2 (m .rbx 0),
   .movdqaLoad .xmm3 (m .rbx 16),
   .lea .rbx (m .rbx 32),
   .vg (.movdquLoad .xmm4 (m .rdi 0)),
   .vg (.movdquLoad .xmm5 (m .rdi 16)),
   .lea .rdi (m .rdi 32),
   .movdqaStore (m .rbx (-32)) .xmm0,
   .movdqaStore (m .rbx (-16)) .xmm0,
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
   .vg (.alu .sub .rdx (.imm 32))]

/-- Zero `t`'s top word, restore the callee-saved registers and the stack pointer, and return 1. -/
def epilogue : List Instr :=
  [.vg (.store (m .rbx 0) .rdx),
   .vg (.mov .rax (.imm 1)),
   .vg (.mov .r15 (.mem (m .rsi (-48)))),
   .vg (.mov .r14 (.mem (m .rsi (-40)))),
   .vg (.mov .r13 (.mem (m .rsi (-32)))),
   .vg (.mov .r12 (.mem (m .rsi (-24)))),
   .vg (.mov .rbp (.mem (m .rsi (-16)))),
   .vg (.mov .rbx (.mem (m .rsi (-8)))),
   .leaRsp (m .rsi 0)]

/-- An outer pass. -/
def pass : Prog isa :=
  .seq (.block outerHead) (.seq (.loop (.block inner) (.vg .ne)) (.block outerTail))

/-- The function's body, before its `rep ret`. -/
def prog : Prog isa :=
  .seq (.block prologue) <|
  .seq (.ite .a (.loop (.seq (.block [.align 16]) (.block walk)) .a) (.block [])) <|
  .seq (.block setup) <|
  .seq (.block body0) <|
  .seq (.loop (.block first) (.vg .ne)) <|
  .seq (.block firstTail) <|
  .seq (.loop pass (.vg .ne)) <|
  .seq (.block final) <|
  .seq (.loop (.block sub) (.vg .ne)) <|
  .seq (.block subTail) <|
  .seq (.loop (.block copy) (.vg .ne)) <|
  .block epilogue

end Rind.X86_64.Mulx4x
