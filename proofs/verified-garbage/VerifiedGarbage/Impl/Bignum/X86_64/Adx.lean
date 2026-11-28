module

public import VerifiedGarbage.Impl.Bignum.X86_64

/-!
# Multiword arithmetic on x86-64: Montgomery multiplication with BMI2 and ADX

Its parts (`row`, `finish`, `fused`) compute what `mm o a b` does (`[o] = [a] [b] R⁻¹ mod m`,
with `m` in array `aN` and the arrays `aAcc` and `aTmp` as working space) by
coarsely integrated operand scanning in one pass per word of `a`, four words
at a time, with `mulx` and the two carry chains of `adcx` (CF) and `adox`
(OF), for a number of words `w` that is a multiple of 4 with
`4 ≤ w < 2³⁰ + 4`; otherwise it is the baseline `montMul`.

Each row `i` adds `a_i b + u m` to a window of `w + 2` words of the
accumulator, `u = (T₀ + a_i b₀)(-m⁻¹) mod 2⁶⁴` making its low word zero; the
window then moves up a word (instead of the accumulator moving down), so
the window is `aAcc + 16 + 8 i`, and spans the arrays `aAcc` and `aTmp`
(which are adjacent), ending, after the `w` rows, at `aTmp`. The two words
below the window hold `a_i` and `u` (the words `aAcc + 8 i` and
`aAcc + 8 i + 8`, whose values the rows no longer need).

A block of four words `j … j + 3` (`r14 = j`) first adds `a_i b_{j…j+3}` to
the window's words (CF: their low halves and the window's words; OF: the
high halves one word up), carrying the high half of the last product, with
both chains' carries, into the next block (`rcx`); then `u m_{j…j+3}` in the
same way (`rbp`). A chain ends in its carry register, which the block's
bound keeps below 2⁶⁴, so the flags are clear between the two halves, and
`xor esi, esi` clears them at each block.

The registers: `rdi` the working space; `r8` the window, `r9` `b`, `r10` `m`,
`rbx` `w`, `r14` the word; `rdx` the multiplier (`a_i` or `u`); `r11`, `r12`,
`r13`, `r15` the block's words; `rcx`, `rbp` the carries; `rax`, `rsi`
temporaries.
-/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.Adx

open VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

/-- `[r8 - 16]`, `[r8 - 8]`: the row's `a_i` and `u`. -/
def xSlot : MemOp := { base := .r8, disp := -16 }
def uSlot : MemOp := { base := .r8, disp := -8 }

/-- Word `k` of the block, `a_i b`: `hi:col := rdx · b_{j+k}`,
`col += T_{j+k}` (CF), `col += prev` (OF). -/
def wordA (k : Nat) (hi col prev : Reg) : List Instr :=
  [.mulx hi col (.mem (ix .r9 .r14 (8 * k))), .adcx col (.mem (ix .r8 .r14 (8 * k))), .adox col (.reg prev)]

/-- Word `k` of the block, `u m`: `hi:rsi := rdx · m_{j+k}`, `col += rsi`
(CF), `col += prev` (OF). -/
def wordB (k : Nat) (hi col prev : Reg) : List Instr :=
  [.mulx hi .rsi (.mem (ix .r10 .r14 (8 * k))), .adcx col (.reg .rsi), .adox col (.reg prev)]

/-- Both carries into `h`. -/
def close (h : Reg) : List Instr := [.mov32 .rsi (.imm 0), .adox h (.reg .rsi), .adcx h (.reg .rsi)]

/-- A block of four words. -/
def block : List Instr :=
  ([.alu32 .xor .rsi (.reg .rsi), .mov .rdx (.mem xSlot)] : List Instr) ++
  wordA 0 .rax .r11 .rcx ++ wordA 1 .rsi .r12 .rax ++ wordA 2 .rax .r13 .rsi ++ wordA 3 .rcx .r15 .rax ++
  close .rcx ++ ([.mov .rdx (.mem uSlot)] : List Instr) ++
  wordB 0 .rax .r11 .rbp ++ wordB 1 .rbp .r12 .rax ++ wordB 2 .rax .r13 .rbp ++ wordB 3 .rbp .r15 .rax ++
  close .rbp ++
  ([.store (ix .r8 .r14) .r11, .store (ix .r8 .r14 8) .r12, .store (ix .r8 .r14 16) .r13,
    .store (ix .r8 .r14 24) .r15, .alu .add .r14 (.imm 4), .alu .cmp .r14 (.reg .rbx)] : List Instr)

/-- `a - (aAcc + 16)` into `rax`: with the window `r8 = aAcc + 16 + 8 i`,
`[rax + r8]` is `a_i`. -/
def rowBase (a : Nat) : List Instr :=
  [.mov .rax (.mem (hdr (sArr a))), .mov .rdx (.mem (hdr (sArr aAcc))), .alu .add .rdx (.imm 16),
    .alu .sub .rax (.reg .rdx)]

/-- `a_i` and `u` below the window, the carries 0 and the word 0. -/
def rowHead : List Instr :=
  [.mov .rdx (.mem { base := .rax, index := some .r8 }), .store xSlot .rdx,
    .mulx .rsi .rax (.mem (at0 .r9)), .alu .add .rax (.mem (at0 .r8)), .mov .rdx (.reg .rax),
    .mulx .rsi .rdx (.mem (hdr sMinv)), .store uSlot .rdx,
    .mov32 .rcx (.imm 0), .mov32 .rbp (.imm 0), .mov32 .r14 (.imm 0)]

/-- The carries into the window's words `w` and `w + 1`, and the window up a
word. -/
def rowTail : List Instr :=
  [.mov .rax (.mem (ix .r8 .r14)), .mov .rsi (.mem (ix .r8 .r14 8)), .alu .add .rax (.reg .rcx),
    .alu .adc .rsi (.imm 0), .alu .add .rax (.reg .rbp), .alu .adc .rsi (.imm 0),
    .store (ix .r8 .r14) .rax, .store (ix .r8 .r14 8) .rsi, .alu .add .r8 (.imm 8)]

/-- ZF set when the window has reached `aTmp`, after the last row. -/
def rowEnd : List Instr := [.mov .rax (.mem (hdr (sArr aTmp))), .alu .cmp .r8 (.reg .rax)]

/-- Row `i`. -/
def row (a : Nat) : Prog isa :=
  .seq (.block (rowBase a)) (.seq (.block rowHead) (.seq (.loop (.block block) .ne)
    (.seq (.block rowTail) (.block rowEnd))))

/-- `b`, `m`, the first window and `w`; then its `2 w + 2` words zeroed. -/
def setup (b : Nat) : List Instr :=
  [.mov .r9 (.mem (hdr (sArr b))), .mov .r10 (.mem (hdr (sArr aN))), .mov .r8 (.mem (hdr (sArr aAcc))),
    .alu .add .r8 (.imm 16), .mov .rbx (.mem (hdr sW))]

def zeroWin : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .mov .rcx (.reg .rbx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.imm 2),
      .mov32 .r14 (.imm 0)])
    (.loop (.block [.store (ix .r8 .r14) .rax, .alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .rcx)]) .ne)

/-- The result (`T < 2m`, at `aTmp`) less `m` into `aAcc`, and the one below
`m` into `o`, as `montMul` does. -/
def finishBases (o : Nat) : List Instr :=
  [.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aTmp))), .mov .rsi (.mem (hdr (sArr aAcc))),
    .mov .rbx (.mem (hdr (sArr o)))]

def finish (o : Nat) : Prog isa :=
  .seq (.block (finishBases o)) (.seq subMod selectAcc)

/-- The rows, for `w` a multiple of 4. -/
def fused (o a b : Nat) : Prog isa :=
  .seq (.block (setup b)) (.seq zeroWin (.seq (.loop (row a) .ne) (finish o)))

/-- ZF set when `v = w - 4` (modulo `2⁶⁴`) is a multiple of 4 below `2³⁰`:
rotated right by 2, its low bits are on top, and the rest below `2²⁸`. -/
def sizeTest : List Instr :=
  [.mov .rax (.mem (hdr sW)), .alu .sub .rax (.imm 4), .shift .ror .rax 2, .shift .shr .rax 28]

end VG.Impl.Bignum.X86_64.Adx
