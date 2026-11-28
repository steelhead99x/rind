import RindIsa.X86_64.Mul4x

/-!
# rind's structured copy of aws-lc's `bn_sqrx8x_internal`

rind's naked function `low::x86_64::mont::bn_sqrx8x_internal`, the squaring
and Montgomery reduction aws-lc's `bn_sqr8x_mont` and `bn_powerx5` call with
BMI2 and ADX (`crypto/fipsmodule/bn/asm/x86_64-mont5.pl`), in rind's model of
x86_64. It takes its arguments in registers and in its caller's frame: `rsi`
is `ap`, `num` words; `r9` is `8 num`; `xmm2` holds `np`, `xmm3` `-8 num`,
and `xmm0` zero; the caller's frame, from 8 bytes above the stack pointer
(the return address below it), holds `n0` at 40 and `t`, the `2 num + 2`
words from 56, whose last two the caller has zeroed. It squares `a` into
`t`: the products of distinct words, eight rows at a time, doubled, plus
the squares; then reduces `t` modulo `np` eight words at a time, each
round's eight multipliers kept in the frame from 64 (`a·a + q·n`, `q` making
its low `num` words zero), leaving the top `num` words in `t`'s upper half
with the final carry in `rax`, and returns `rdi` at the upper half, `rsi`
`np`'s last word, `rbp` `np`, and `rcx` `-8 num`, from which its caller
subtracts `np` and selects.

aws-lc's text jumps into its zeroing loop and leaves its other loops from
their middles, which VG's structured `Code` cannot. This copy,
`rind/src/low/x86_64/sqrx8x_internal.s`, is aws-lc's instructions in this
structure, which `layout` lays out: each loop tests at its bottom, running
its head once before it where aws-lc leaves it from its middle (`tri`,
`inner`, `tail`), and the shift-and-add loop tests `rcx` again there by
`jrcxz` over a `jmp`. Its zeroing loop clears all of `t`, where aws-lc's
skips its first eight words, which the squaring writes before it reads.
Instructions aws-lc writes as bytes are spelled out, and its padding
prefixes and NOPs dropped. `admin/prove lean` checks that `function prog` is
its bytes as rind's Linux release build emits it.
-/

namespace Rind.X86_64.Sqrx8x

open VG VG.X86_64 Rind.X86_64.Mul4x

/-- Point `rdi` at `t`, the `2 num` words 56 bytes above the stack pointer, and save `8 num` and `ap`'s end in the caller's frame slots. -/
def entry : List Instr :=
  [.lea .rdi (m .rsp 56),
   .lea .rbp (mx .rsi .r9 1 0),
   .vg (.store (m .rsp 8) .r9),
   .vg (.store (m .rsp 16) .rbp)]

/-- Zero 128 bytes of `t`: two of its words for each of `ap`'s. -/
def zero : List Instr :=
  [.movdqaStore (m .rdi 0) .xmm0,
   .movdqaStore (m .rdi 16) .xmm0,
   .movdqaStore (m .rdi 32) .xmm0,
   .movdqaStore (m .rdi 48) .xmm0,
   .movdqaStore (m .rdi 64) .xmm0,
   .movdqaStore (m .rdi 80) .xmm0,
   .movdqaStore (m .rdi 96) .xmm0,
   .movdqaStore (m .rdi 112) .xmm0,
   .lea .rdi (m .rdi 128),
   .vg (.alu .sub .r9 (.imm 64))]

/-- Load `a[0]` and clear the carries. -/
def init : List Instr :=
  [.vg (.mov .rdx (.mem (m .rsi 0))),
   .vg (.alu .xor .r10 (.reg .r10)),
   .vg (.alu .xor .r11 (.reg .r11)),
   .vg (.alu .xor .r12 (.reg .r12)),
   .vg (.alu .xor .r13 (.reg .r13)),
   .vg (.alu .xor .r14 (.reg .r14)),
   .vg (.alu .xor .r15 (.reg .r15)),
   .lea .rdi (m .rsp 56),
   .vg (.alu .xor .rbp (.reg .rbp))]

/-- The products of eight words of `a` with one another, added into `t`, and whether `a` has words left. -/
def tri : List Instr :=
  [.vg (.mulx .rax .r8 (.mem (m .rsi 8))),
   .vg (.adcx .r8 (.reg .r9)),
   .vg (.adox .r10 (.reg .rax)),
   .vg (.mulx .rax .r9 (.mem (m .rsi 16))),
   .vg (.adcx .r9 (.reg .r10)),
   .vg (.adox .r11 (.reg .rax)),
   .vg (.mulx .rax .r10 (.mem (m .rsi 24))),
   .vg (.adcx .r10 (.reg .r11)),
   .vg (.adox .r12 (.reg .rax)),
   .vg (.mulx .rax .r11 (.mem (m .rsi 32))),
   .vg (.adcx .r11 (.reg .r12)),
   .vg (.adox .r13 (.reg .rax)),
   .vg (.mulx .rax .r12 (.mem (m .rsi 40))),
   .vg (.adcx .r12 (.reg .r13)),
   .vg (.adox .r14 (.reg .rax)),
   .vg (.mulx .rax .r13 (.mem (m .rsi 48))),
   .vg (.adcx .r13 (.reg .r14)),
   .vg (.adox .rax (.reg .r15)),
   .vg (.mulx .r15 .r14 (.mem (m .rsi 56))),
   .vg (.mov .rdx (.mem (m .rsi 8))),
   .vg (.adcx .r14 (.reg .rax)),
   .vg (.adox .r15 (.reg .rbp)),
   .vg (.alu .adc .r15 (.mem (m .rdi 64))),
   .vg (.store (m .rdi 8) .r8),
   .vg (.store (m .rdi 16) .r9),
   .vg (.alu .sbb .rcx (.reg .rcx)),
   .vg (.alu .xor .rbp (.reg .rbp)),
   .vg (.mulx .rbx .r8 (.mem (m .rsi 16))),
   .vg (.mulx .rax .r9 (.mem (m .rsi 24))),
   .vg (.adcx .r8 (.reg .r10)),
   .vg (.adox .r9 (.reg .rbx)),
   .vg (.mulx .rbx .r10 (.mem (m .rsi 32))),
   .vg (.adcx .r9 (.reg .r11)),
   .vg (.adox .r10 (.reg .rax)),
   .vg (.mulx .rax .r11 (.mem (m .rsi 40))),
   .vg (.adcx .r10 (.reg .r12)),
   .vg (.adox .r11 (.reg .rbx)),
   .vg (.mulx .rbx .r12 (.mem (m .rsi 48))),
   .vg (.adcx .r11 (.reg .r13)),
   .vg (.adox .r12 (.reg .r14)),
   .vg (.mulx .r14 .r13 (.mem (m .rsi 56))),
   .vg (.mov .rdx (.mem (m .rsi 16))),
   .vg (.adcx .r12 (.reg .rax)),
   .vg (.adox .r13 (.reg .rbx)),
   .vg (.adcx .r13 (.reg .r15)),
   .vg (.adox .r14 (.reg .rbp)),
   .vg (.adcx .r14 (.reg .rbp)),
   .vg (.store (m .rdi 24) .r8),
   .vg (.store (m .rdi 32) .r9),
   .vg (.mulx .rbx .r8 (.mem (m .rsi 24))),
   .vg (.mulx .rax .r9 (.mem (m .rsi 32))),
   .vg (.adcx .r8 (.reg .r10)),
   .vg (.adox .r9 (.reg .rbx)),
   .vg (.mulx .rbx .r10 (.mem (m .rsi 40))),
   .vg (.adcx .r9 (.reg .r11)),
   .vg (.adox .r10 (.reg .rax)),
   .vg (.mulx .rax .r11 (.mem (m .rsi 48))),
   .vg (.adcx .r10 (.reg .r12)),
   .vg (.adox .r11 (.reg .r13)),
   .vg (.mulx .r13 .r12 (.mem (m .rsi 56))),
   .vg (.mov .rdx (.mem (m .rsi 24))),
   .vg (.adcx .r11 (.reg .rbx)),
   .vg (.adox .r12 (.reg .rax)),
   .vg (.adcx .r12 (.reg .r14)),
   .vg (.store (m .rdi 40) .r8),
   .vg (.store (m .rdi 48) .r9),
   .vg (.mulx .rax .r8 (.mem (m .rsi 32))),
   .vg (.adox .r13 (.reg .rbp)),
   .vg (.adcx .r13 (.reg .rbp)),
   .vg (.mulx .rbx .r9 (.mem (m .rsi 40))),
   .vg (.adcx .r8 (.reg .r10)),
   .vg (.adox .r9 (.reg .rax)),
   .vg (.mulx .rax .r10 (.mem (m .rsi 48))),
   .vg (.adcx .r9 (.reg .r11)),
   .vg (.adox .r10 (.reg .r12)),
   .vg (.mulx .r12 .r11 (.mem (m .rsi 56))),
   .vg (.mov .rdx (.mem (m .rsi 32))),
   .vg (.mov .r14 (.mem (m .rsi 40))),
   .vg (.adcx .r10 (.reg .rbx)),
   .vg (.adox .r11 (.reg .rax)),
   .vg (.mov .r15 (.mem (m .rsi 48))),
   .vg (.adcx .r11 (.reg .r13)),
   .vg (.adox .r12 (.reg .rbp)),
   .vg (.adcx .r12 (.reg .rbp)),
   .vg (.store (m .rdi 56) .r8),
   .vg (.store (m .rdi 64) .r9),
   .vg (.mulx .rax .r9 (.reg .r14)),
   .vg (.mov .r8 (.mem (m .rsi 56))),
   .vg (.adcx .r9 (.reg .r10)),
   .vg (.mulx .rbx .r10 (.reg .r15)),
   .vg (.adox .r10 (.reg .rax)),
   .vg (.adcx .r10 (.reg .r11)),
   .vg (.mulx .rax .r11 (.reg .r8)),
   .vg (.mov .rdx (.reg .r14)),
   .vg (.adox .r11 (.reg .rbx)),
   .vg (.adcx .r11 (.reg .r12)),
   .vg (.adcx .rax (.reg .rbp)),
   .vg (.mulx .rbx .r14 (.reg .r15)),
   .vg (.mulx .r13 .r12 (.reg .r8)),
   .vg (.mov .rdx (.reg .r15)),
   .lea .rsi (m .rsi 64),
   .vg (.adcx .r11 (.reg .r14)),
   .vg (.adox .r12 (.reg .rbx)),
   .vg (.adcx .r12 (.reg .rax)),
   .vg (.adox .r13 (.reg .rbp)),
   .vg (.mulx .r14 .r8 (.reg .r8)),
   .vg (.adcx .r13 (.reg .r8)),
   .vg (.adcx .r14 (.reg .rbp)),
   .vg (.alu .cmp .rsi (.mem (m .rsp 16)))]

/-- Take the carry into the next eight words of `t`, and start multiplying the eight words just squared by the next eight of `a`. -/
def pre : List Instr :=
  [.neg .rcx,
   .vg (.mov .rcx (.imm (-8))),
   .vg (.mov .r15 (.reg .rbp)),
   .vg (.mov .r8 (.mem (m .rdi 64))),
   .vg (.adcx .r9 (.mem (m .rdi 72))),
   .vg (.adcx .r10 (.mem (m .rdi 80))),
   .vg (.adcx .r11 (.mem (m .rdi 88))),
   .vg (.alu .adc .r12 (.mem (m .rdi 96))),
   .vg (.alu .adc .r13 (.mem (m .rdi 104))),
   .vg (.alu .adc .r14 (.mem (m .rdi 112))),
   .vg (.alu .adc .r15 (.mem (m .rdi 120))),
   .lea .rbp (m .rsi 0),
   .lea .rdi (m .rdi 128),
   .vg (.alu .sbb .rax (.reg .rax)),
   .vg (.mov .rdx (.mem (m .rsi (-64)))),
   .vg (.store (m .rsp 24) .rax),
   .vg (.store (m .rsp 32) .rdi),
   .vg (.alu32 .xor .rax (.reg .rax)),
   .jmpAlign 32]

/-- One word of `a` times the eight words just squared, added into `t`. -/
def inner : List Instr :=
  [.vg (.mov .rbx (.reg .r8)),
   .vg (.mulx .r8 .rax (.mem (m .rbp 0))),
   .vg (.adcx .rbx (.reg .rax)),
   .vg (.adox .r8 (.reg .r9)),
   .vg (.mulx .r9 .rax (.mem (m .rbp 8))),
   .vg (.adcx .r8 (.reg .rax)),
   .vg (.adox .r9 (.reg .r10)),
   .vg (.mulx .r10 .rax (.mem (m .rbp 16))),
   .vg (.adcx .r9 (.reg .rax)),
   .vg (.adox .r10 (.reg .r11)),
   .vg (.mulx .r11 .rax (.mem (m .rbp 24))),
   .vg (.adcx .r10 (.reg .rax)),
   .vg (.adox .r11 (.reg .r12)),
   .vg (.mulx .r12 .rax (.mem (m .rbp 32))),
   .vg (.adcx .r11 (.reg .rax)),
   .vg (.adox .r12 (.reg .r13)),
   .vg (.mulx .r13 .rax (.mem (m .rbp 40))),
   .vg (.adcx .r12 (.reg .rax)),
   .vg (.adox .r13 (.reg .r14)),
   .vg (.mulx .r14 .rax (.mem (m .rbp 48))),
   .vg (.store (mx .rdi .rcx 8 0) .rbx),
   .vg (.mov32 .rbx (.imm 0)),
   .vg (.adcx .r13 (.reg .rax)),
   .vg (.adox .r14 (.reg .r15)),
   .vg (.mulx .r15 .rax (.mem (m .rbp 56))),
   .vg (.mov .rdx (.mem (mx .rsi .rcx 8 8))),
   .vg (.adcx .r14 (.reg .rax)),
   .vg (.adox .r15 (.reg .rbx)),
   .vg (.adcx .r15 (.reg .rbx)),
   .inc .rcx]

/-- Step to the next eight words of `a`, and whether it has words left. -/
def innerEnd : List Instr :=
  [.lea .rbp (m .rbp 64),
   .vg (.mov .rcx (.imm (-8))),
   .vg (.alu .cmp .rbp (.mem (m .rsp 16)))]

/-- Add the next eight words of `t` into the accumulator, keeping their carry. -/
def reload : List Instr :=
  [.vg (.alu .sub .rbx (.mem (m .rsp 24))),
   .vg (.mov .rdx (.mem (m .rsi (-64)))),
   .vg (.adcx .r8 (.mem (m .rdi 0))),
   .vg (.adcx .r9 (.mem (m .rdi 8))),
   .vg (.alu .adc .r10 (.mem (m .rdi 16))),
   .vg (.alu .adc .r11 (.mem (m .rdi 24))),
   .vg (.alu .adc .r12 (.mem (m .rdi 32))),
   .vg (.alu .adc .r13 (.mem (m .rdi 40))),
   .vg (.alu .adc .r14 (.mem (m .rdi 48))),
   .vg (.alu .adc .r15 (.mem (m .rdi 56))),
   .lea .rdi (m .rdi 64),
   .vg (.alu .sbb .rax (.reg .rax)),
   .vg (.alu32 .xor .rbx (.reg .rbx)),
   .vg (.store (m .rsp 24) .rax),
   .jmpAlign 32]

/-- Fold in the last carry, and whether the row reached the next eight words to square. -/
def brk : List Instr :=
  [.vg (.alu .xor .rbp (.reg .rbp)),
   .vg (.alu .sub .rbx (.mem (m .rsp 24))),
   .vg (.adcx .r8 (.reg .rbp)),
   .vg (.mov .rcx (.mem (m .rsp 32))),
   .vg (.adcx .r9 (.reg .rbp)),
   .vg (.mov .rdx (.mem (m .rsi 0))),
   .vg (.alu .adc .r10 (.imm 0)),
   .vg (.store (m .rdi 0) .r8),
   .vg (.alu .adc .r11 (.imm 0)),
   .vg (.alu .adc .r12 (.imm 0)),
   .vg (.alu .adc .r13 (.imm 0)),
   .vg (.alu .adc .r14 (.imm 0)),
   .vg (.alu .adc .r15 (.imm 0)),
   .vg (.alu .cmp .rdi (.reg .rcx))]

/-- Store the accumulator into `t`, and reload the eight words the next row starts from. -/
def spill : List Instr :=
  [.vg (.store (m .rdi 8) .r9),
   .vg (.mov .r9 (.mem (m .rcx 8))),
   .vg (.store (m .rdi 16) .r10),
   .vg (.mov .r10 (.mem (m .rcx 16))),
   .vg (.store (m .rdi 24) .r11),
   .vg (.mov .r11 (.mem (m .rcx 24))),
   .vg (.store (m .rdi 32) .r12),
   .vg (.mov .r12 (.mem (m .rcx 32))),
   .vg (.store (m .rdi 40) .r13),
   .vg (.mov .r13 (.mem (m .rcx 40))),
   .vg (.store (m .rdi 48) .r14),
   .vg (.mov .r14 (.mem (m .rcx 48))),
   .vg (.store (m .rdi 56) .r15),
   .vg (.mov .r15 (.mem (m .rcx 56))),
   .vg (.mov .rdi (.reg .rcx))]

/-- Store the last products, and start doubling `t` and adding the squares of `a`'s words. -/
def outerBreak : List Instr :=
  [.vg (.store (m .rdi 72) .r9),
   .vg (.movqR .rcx .xmm3),
   .vg (.store (m .rdi 80) .r10),
   .vg (.store (m .rdi 88) .r11),
   .vg (.store (m .rdi 96) .r12),
   .vg (.store (m .rdi 104) .r13),
   .vg (.store (m .rdi 112) .r14),
   .lea .rdi (m .rsp 56),
   .vg (.mov .rdx (.mem (mx .rsi .rcx 1 0))),
   .vg (.mov .r11 (.mem (m .rdi 8))),
   .vg (.alu .xor .r10 (.reg .r10)),
   .vg (.mov .r9 (.mem (m .rsp 8))),
   .vg (.adox .r11 (.reg .r11)),
   .vg (.mov .r12 (.mem (m .rdi 16))),
   .vg (.mov .r13 (.mem (m .rdi 24)))]

/-- `t`'s next eight words doubled, plus the squares of four of `a`'s words, but the last two words' carry. -/
def shift : List Instr :=
  [.vg (.mulx .rbx .rax (.reg .rdx)),
   .vg (.adox .r12 (.reg .r12)),
   .vg (.adcx .rax (.reg .r10)),
   .vg (.mov .rdx (.mem (mx .rsi .rcx 1 8))),
   .vg (.mov .r10 (.mem (m .rdi 32))),
   .vg (.adox .r13 (.reg .r13)),
   .vg (.adcx .rbx (.reg .r11)),
   .vg (.mov .r11 (.mem (m .rdi 40))),
   .vg (.store (m .rdi 0) .rax),
   .vg (.store (m .rdi 8) .rbx),
   .vg (.mulx .rbx .rax (.reg .rdx)),
   .vg (.adox .r10 (.reg .r10)),
   .vg (.adcx .rax (.reg .r12)),
   .vg (.mov .rdx (.mem (mx .rsi .rcx 1 16))),
   .vg (.mov .r12 (.mem (m .rdi 48))),
   .vg (.adox .r11 (.reg .r11)),
   .vg (.adcx .rbx (.reg .r13)),
   .vg (.mov .r13 (.mem (m .rdi 56))),
   .vg (.store (m .rdi 16) .rax),
   .vg (.store (m .rdi 24) .rbx),
   .vg (.mulx .rbx .rax (.reg .rdx)),
   .vg (.adox .r12 (.reg .r12)),
   .vg (.adcx .rax (.reg .r10)),
   .vg (.mov .rdx (.mem (mx .rsi .rcx 1 24))),
   .lea .rcx (m .rcx 32),
   .vg (.mov .r10 (.mem (m .rdi 64))),
   .vg (.adox .r13 (.reg .r13)),
   .vg (.adcx .rbx (.reg .r11)),
   .vg (.mov .r11 (.mem (m .rdi 72))),
   .vg (.store (m .rdi 32) .rax),
   .vg (.store (m .rdi 40) .rbx),
   .vg (.mulx .rbx .rax (.reg .rdx)),
   .vg (.adox .r10 (.reg .r10)),
   .vg (.adcx .rax (.reg .r12))]

/-- Load the next words of `a` and `t` while `a` has words left. -/
def shiftNext : List Instr :=
  [.vg (.mov .rdx (.mem (mx .rsi .rcx 1 0))),
   .vg (.adox .r11 (.reg .r11)),
   .vg (.adcx .rbx (.reg .r13)),
   .vg (.mov .r12 (.mem (m .rdi 80))),
   .vg (.mov .r13 (.mem (m .rdi 88))),
   .vg (.store (m .rdi 48) .rax),
   .vg (.store (m .rdi 56) .rbx),
   .lea .rdi (m .rdi 64)]

/-- Store the last two words, and set up the reduction: `np` in `rbp`, `n0` in `rbx`, and the frame's slots for `np`'s last eight words and `t`'s end. -/
def shiftEnd : List Instr :=
  [.vg (.adcx .rbx (.reg .r13)),
   .vg (.store (m .rdi 48) .rax),
   .vg (.store (m .rdi 56) .rbx),
   .lea .rdi (m .rdi 64),
   .vg (.movqR .rbp .xmm2),
   .vg (.alu32 .xor .rax (.reg .rax)),
   .vg (.mov .rbx (.mem (m .rsp 40))),
   .vg (.mov .rdx (.mem (m .rsp 56))),
   .lea .rcx (mx .rbp .r9 1 (-64)),
   .vg (.store (m .rsp 8) .rcx),
   .vg (.store (m .rsp 16) .rdi),
   .lea .rdi (m .rsp 56)]

/-- Load eight words of `t` and the first multiplier. -/
def redHead : List Instr :=
  [.vg (.mov .r9 (.mem (m .rdi 8))),
   .vg (.mov .r10 (.mem (m .rdi 16))),
   .vg (.mov .r11 (.mem (m .rdi 24))),
   .vg (.mov .r12 (.mem (m .rdi 32))),
   .vg (.mov .r8 (.reg .rdx)),
   .vg (.imul .rdx .rbx),
   .vg (.mov .r13 (.mem (m .rdi 40))),
   .vg (.mov .r14 (.mem (m .rdi 48))),
   .vg (.mov .r15 (.mem (m .rdi 56))),
   .vg (.store (m .rsp 32) .rax),
   .lea .rdi (m .rdi 64),
   .vg (.alu .xor .rsi (.reg .rsi)),
   .vg (.mov .rcx (.imm (-8))),
   .jmpAlign 32]

/-- One Montgomery step: the multiplier that zeroes `t`'s low word, saved in the frame, times `np`'s eight words, added into the eight words. -/
def red : List Instr :=
  [.vg (.mov .rbx (.reg .r8)),
   .vg (.mulx .r8 .rax (.mem (m .rbp 0))),
   .vg (.adcx .rax (.reg .rbx)),
   .vg (.adox .r8 (.reg .r9)),
   .vg (.mulx .r9 .rbx (.mem (m .rbp 8))),
   .vg (.adcx .r8 (.reg .rbx)),
   .vg (.adox .r9 (.reg .r10)),
   .vg (.mulx .r10 .rbx (.mem (m .rbp 16))),
   .vg (.adcx .r9 (.reg .rbx)),
   .vg (.adox .r10 (.reg .r11)),
   .vg (.mulx .r11 .rbx (.mem (m .rbp 24))),
   .vg (.adcx .r10 (.reg .rbx)),
   .vg (.adox .r11 (.reg .r12)),
   .vg (.mulx .r12 .rbx (.mem (m .rbp 32))),
   .vg (.mov .rax (.reg .rdx)),
   .vg (.mov .rdx (.reg .r8)),
   .vg (.adcx .r11 (.reg .rbx)),
   .vg (.adox .r12 (.reg .r13)),
   .vg (.mulx .rdx .rbx (.mem (m .rsp 40))),
   .vg (.mov .rdx (.reg .rax)),
   .vg (.store (mx .rsp .rcx 8 120) .rax),
   .vg (.mulx .r13 .rax (.mem (m .rbp 40))),
   .vg (.adcx .r12 (.reg .rax)),
   .vg (.adox .r13 (.reg .r14)),
   .vg (.mulx .r14 .rax (.mem (m .rbp 48))),
   .vg (.adcx .r13 (.reg .rax)),
   .vg (.adox .r14 (.reg .r15)),
   .vg (.mulx .r15 .rax (.mem (m .rbp 56))),
   .vg (.mov .rdx (.reg .rbx)),
   .vg (.adcx .r14 (.reg .rax)),
   .vg (.adox .r15 (.reg .rsi)),
   .vg (.adcx .r15 (.reg .rsi)),
   .inc .rcx]

/-- Whether `np` has words left past these eight. -/
def redEnd : List Instr :=
  [.vg (.mov .rax (.reg .rsi)),
   .vg (.alu .cmp .rbp (.mem (m .rsp 8)))]

/-- Add the next eight words of `t`, keeping their carry, and start multiplying `np`'s next eight words by the saved multipliers. -/
def tailHead : List Instr :=
  [.vg (.mov .rdx (.mem (m .rsp 56))),
   .vg (.alu .add .r8 (.mem (m .rdi 0))),
   .lea .rbp (m .rbp 64),
   .vg (.mov .rcx (.imm (-8))),
   .vg (.adcx .r9 (.mem (m .rdi 8))),
   .vg (.adcx .r10 (.mem (m .rdi 16))),
   .vg (.alu .adc .r11 (.mem (m .rdi 24))),
   .vg (.alu .adc .r12 (.mem (m .rdi 32))),
   .vg (.alu .adc .r13 (.mem (m .rdi 40))),
   .vg (.alu .adc .r14 (.mem (m .rdi 48))),
   .vg (.alu .adc .r15 (.mem (m .rdi 56))),
   .lea .rdi (m .rdi 64),
   .vg (.alu .sbb .rax (.reg .rax)),
   .vg (.alu .xor .rsi (.reg .rsi)),
   .vg (.store (m .rsp 24) .rax),
   .jmpAlign 32]

/-- One saved multiplier times `np`'s next eight words, added into `t`. -/
def tail : List Instr :=
  [.vg (.mov .rbx (.reg .r8)),
   .vg (.mulx .r8 .rax (.mem (m .rbp 0))),
   .vg (.adcx .rbx (.reg .rax)),
   .vg (.adox .r8 (.reg .r9)),
   .vg (.mulx .r9 .rax (.mem (m .rbp 8))),
   .vg (.adcx .r8 (.reg .rax)),
   .vg (.adox .r9 (.reg .r10)),
   .vg (.mulx .r10 .rax (.mem (m .rbp 16))),
   .vg (.adcx .r9 (.reg .rax)),
   .vg (.adox .r10 (.reg .r11)),
   .vg (.mulx .r11 .rax (.mem (m .rbp 24))),
   .vg (.adcx .r10 (.reg .rax)),
   .vg (.adox .r11 (.reg .r12)),
   .vg (.mulx .r12 .rax (.mem (m .rbp 32))),
   .vg (.adcx .r11 (.reg .rax)),
   .vg (.adox .r12 (.reg .r13)),
   .vg (.mulx .r13 .rax (.mem (m .rbp 40))),
   .vg (.adcx .r12 (.reg .rax)),
   .vg (.adox .r13 (.reg .r14)),
   .vg (.mulx .r14 .rax (.mem (m .rbp 48))),
   .vg (.adcx .r13 (.reg .rax)),
   .vg (.adox .r14 (.reg .r15)),
   .vg (.mulx .r15 .rax (.mem (m .rbp 56))),
   .vg (.mov .rdx (.mem (mx .rsp .rcx 8 128))),
   .vg (.adcx .r14 (.reg .rax)),
   .vg (.adox .r15 (.reg .rsi)),
   .vg (.store (mx .rdi .rcx 8 0) .rbx),
   .vg (.mov .rbx (.reg .r8)),
   .vg (.adcx .r15 (.reg .rsi)),
   .inc .rcx]

/-- Whether `np` has words left. -/
def tailEnd : List Instr :=
  [.vg (.alu .cmp .rbp (.mem (m .rsp 8)))]

/-- Add the next eight words of `t`, keeping their carry, for `np`'s next eight words. -/
def tailNext : List Instr :=
  [.vg (.alu .sub .rsi (.mem (m .rsp 24))),
   .vg (.mov .rdx (.mem (m .rsp 56))),
   .lea .rbp (m .rbp 64),
   .vg (.alu .adc .r8 (.mem (m .rdi 0))),
   .vg (.alu .adc .r9 (.mem (m .rdi 8))),
   .vg (.alu .adc .r10 (.mem (m .rdi 16))),
   .vg (.alu .adc .r11 (.mem (m .rdi 24))),
   .vg (.alu .adc .r12 (.mem (m .rdi 32))),
   .vg (.alu .adc .r13 (.mem (m .rdi 40))),
   .vg (.alu .adc .r14 (.mem (m .rdi 48))),
   .vg (.alu .adc .r15 (.mem (m .rdi 56))),
   .lea .rdi (m .rdi 64),
   .vg (.alu .sbb .rax (.reg .rax)),
   .vg (.alu .sub .rcx (.imm 8)),
   .vg (.alu .xor .rsi (.reg .rsi)),
   .vg (.store (m .rsp 24) .rax),
   .jmpAlign 32]

/-- Fold in the top carry. -/
def tailDone : List Instr :=
  [.vg (.alu .xor .rax (.reg .rax)),
   .vg (.alu .add .r8 (.mem (m .rsp 32))),
   .vg (.alu .adc .r9 (.imm 0)),
   .vg (.alu .adc .r10 (.imm 0)),
   .vg (.alu .adc .r11 (.imm 0)),
   .vg (.alu .adc .r12 (.imm 0)),
   .vg (.alu .adc .r13 (.imm 0)),
   .vg (.alu .adc .r14 (.imm 0)),
   .vg (.alu .adc .r15 (.imm 0)),
   .vg (.alu .adc .rax (.imm 0)),
   .vg (.alu .sub .rsi (.mem (m .rsp 24)))]

/-- Add `t`'s next eight words, store the eight reduced words, and whether `t` has words left to reduce. -/
def noTail : List Instr :=
  [.vg (.alu .adc .r8 (.mem (m .rdi 0))),
   .vg (.movqR .rcx .xmm3),
   .vg (.alu .adc .r9 (.mem (m .rdi 8))),
   .vg (.mov .rsi (.mem (m .rbp 56))),
   .vg (.movqR .rbp .xmm2),
   .vg (.alu .adc .r10 (.mem (m .rdi 16))),
   .vg (.alu .adc .r11 (.mem (m .rdi 24))),
   .vg (.alu .adc .r12 (.mem (m .rdi 32))),
   .vg (.alu .adc .r13 (.mem (m .rdi 40))),
   .vg (.alu .adc .r14 (.mem (m .rdi 48))),
   .vg (.alu .adc .r15 (.mem (m .rdi 56))),
   .vg (.alu .adc .rax (.imm 0)),
   .vg (.mov .rbx (.mem (m .rsp 40))),
   .vg (.mov .rdx (.mem (mx .rdi .rcx 1 64))),
   .vg (.store (m .rdi 0) .r8),
   .lea .r8 (m .rdi 64),
   .vg (.store (m .rdi 8) .r9),
   .vg (.store (m .rdi 16) .r10),
   .vg (.store (m .rdi 24) .r11),
   .vg (.store (m .rdi 32) .r12),
   .vg (.store (m .rdi 40) .r13),
   .vg (.store (m .rdi 48) .r14),
   .vg (.store (m .rdi 56) .r15),
   .lea .rdi (mx .rdi .rcx 1 64),
   .vg (.alu .cmp .r8 (.mem (m .rsp 16)))]

/-- A row of the products: the eight words just squared times each later
eight of `a`, then the next eight squared. -/
def outerPass : Prog isa :=
  .seq (.block pre) <|
  .seq (.loop (.block inner) (.vg .ne)) <|
  .seq (.block innerEnd) <|
  .seq (.ite (.vg .e) (.block [])
    (.loop (.seq (.block reload) (.seq (.loop (.block inner) (.vg .ne)) (.block innerEnd))) (.vg .ne))) <|
  .seq (.block brk) <|
  .seq (.ite (.vg .e) (.block []) (.block spill)) <|
  .block tri

/-- The rest of a reduction round: `np`'s next eight words times the saved multipliers. -/
def tailPass : Prog isa :=
  .seq (.block tailNext) <|
  .seq (.loop (.block tail) (.vg .ne)) <|
  .block tailEnd

/-- A reduction round: eight multipliers, then their products with the rest of `np`. -/
def redPass : Prog isa :=
  .seq (.block [.align 32]) <|
  .seq (.block redHead) <|
  .seq (.loop (.block red) (.vg .ne)) <|
  .seq (.block redEnd) <|
  .seq (.ite (.vg .ae) (.block [])
    (.seq (.block tailHead) <|
     .seq (.loop (.block tail) (.vg .ne)) <|
     .seq (.block tailEnd) <|
     .seq (.ite (.vg .ae) (.block []) (.loop tailPass (.vg .b))) <|
     .block tailDone)) <|
  .block noTail

/-- The function's body, before its `rep ret`. -/
def prog : Prog isa :=
  .seq (.block entry) <|
  .seq (.loop (.seq (.block [.align 32]) (.block zero)) (.vg .ne)) <|
  .seq (.block init) <|
  .seq (.block tri) <|
  .seq (.ite (.vg .e) (.block []) (.loop outerPass (.vg .ne))) <|
  .seq (.block outerBreak) <|
  .seq (.loop (.seq (.block [.align 32]) (.seq (.block shift) (.ite .rcxz (.block []) (.block shiftNext)))) .rcxnz) <|
  .seq (.block shiftEnd) <|
  .loop redPass (.vg .b)

end Rind.X86_64.Sqrx8x
