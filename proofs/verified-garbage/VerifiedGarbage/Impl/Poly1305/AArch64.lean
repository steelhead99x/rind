module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Poly1305: AArch64 implementation

The model has no carry flag and no multiply-high (`umulh`), so the
arithmetic is in radix `2²⁶`, as in poly1305-donna-32: the accumulator `h`
and the clamped `r` are five 26-bit limbs (`h = h0 + 2²⁶ h1 + … + 2¹⁰⁴ h4`),
their products are 64-bit `mul`/`madd`, and carries are shifts and masks.

The state (`x0`, 128 bytes, see `VG.Spec.Poly1305.Buffered`):

* `[0, 24)`: the accumulator `h = w0 + 2⁶⁴ w1 + 2¹²⁸ w2`, fully reduced
  (`h < p`) between calls, in three 64-bit words;
* `[24, 56)`: the key: `r` (`[24, 40)`) and `s` (`[40, 56)`);
* `[56, 72)`: the buffer: the message's last bytes that do not fill a block,
  padded in place in `Radix64.finalize`;
* `[72, 108)`: the limbs `r0, …, r4` and `s1, …, s4` (`sj = 5 rj`) of the
  clamped `r`, as 32-bit words, computed on entry.

`Radix64.update` and `Radix64.finalize` do not use their working space (`scratch`).

Registers: `x4`–`x8` hold the limbs of `h`, `x9`–`x13` the sums of products
`d0, …, d4` (and other limbs in between), `x14`–`x16` are temporaries and
`x17` holds the mask `2²⁶ - 1`. Only caller-saved registers are used, so
nothing is saved.

Each call converts `h` into limbs (`loadH`). A block `m` is absorbed as in
poly1305-donna-32: `h += m + pad · 2¹²⁸`, then `dk = Σ_{i+j=k} hi rj +
Σ_{i+j=k+5} hi sj` (as `2¹³⁰ ≡ 5` modulo `p = 2¹³⁰ - 5`), with the
coefficients loaded from the state, then the carries are propagated from
`d0` to `d4` and the carry out of `d4` is added, times 5, to `h0`. Between
blocks, `h1 < 2²⁷` and the other limbs are less than `2²⁶`.

Before `h` is stored, it is reduced fully (`reduce`): its limbs are
normalized (except that `h4` may be `2²⁶`), `g = h + 5` is computed with
carries, and `g - 2¹³⁰` is selected, with a mask and without a branch, if
`g ≥ 2¹³⁰`. The limbs are then packed into 64-bit words (`pack`).

The only branches are on the block count, the number of bytes buffered
(`count mod 16`) and the lengths, and every address is a pointer plus a
constant, or plus a count, so only the pointers, `count` and the lengths can
affect timing.
-/

@[expose] public section

namespace VG.Impl.Poly1305.AArch64

open VG.AArch64

/-- The limbs of `h`. -/
def H : List Reg := [.x4, .x5, .x6, .x7, .x8]
/-- The sums of products, and other limbs. -/
def D : List Reg := [.x9, .x10, .x11, .x12, .x13]

/-- `2²⁶ - 1` into `x17`. -/
def mask : List Instr := [.movz .x .x17 0xffff 0, .movk .x .x17 0x3ff 1]

/-- The 64-bit constant `c` into `d`. -/
def const64 (d : Reg) (c : BitVec 64) : List Instr :=
  [.movz .x d (c.extractLsb' 0 16) 0, .movk .x d (c.extractLsb' 16 16) 1,
    .movk .x d (c.extractLsb' 32 16) 2, .movk .x d (c.extractLsb' 48 16) 3]

/-- The 128-bit number at `[n + off]` into `x14` (low word) and `x15`. -/
def load2 (n : Reg) (off : Nat) : List Instr := [.ldr .x .x14 n off, .ldr .x .x15 n (off + 8)]

/-- The five 26-bit limbs of the 128-bit `x14 + 2⁶⁴ x15` into `x9`–`x13`
(the last less than `2²⁴`), using `x16`. -/
def split : List Instr := [
  .logic .and .x .x9 .x14 .x17,
  .lsr .x .x10 .x14 26, .logic .and .x .x10 .x10 .x17,
  .lsr .x .x11 .x14 52, .lsl .x .x16 .x15 12, .add .x .x11 .x11 .x16,
  .logic .and .x .x11 .x11 .x17,
  .lsr .x .x12 .x15 14, .logic .and .x .x12 .x12 .x17,
  .lsr .x .x13 .x15 40]

/-- The offsets of the limbs `rj` and `sj` in the state. -/
def rOff (j : Nat) : Nat := 72 + 4 * j
def sOff (j : Nat) : Nat := 88 + 4 * j

/-- `r` clamped, in `x14, x15`. -/
def clampR : List Instr :=
  const64 .x16 0x0ffffffc0fffffff ++ ([.logic .and .x .x14 .x14 .x16] : List Instr) ++
  const64 .x16 0x0ffffffc0ffffffc ++ ([.logic .and .x .x15 .x15 .x16] : List Instr)

/-- `sj = 5 rj` into `x4`–`x7`, from `rj` in `x10`–`x13`. -/
def times5 : List Instr :=
  [.lsl .x .x4 .x10 2, .add .x .x4 .x4 .x10, .lsl .x .x5 .x11 2, .add .x .x5 .x5 .x11,
    .lsl .x .x6 .x12 2, .add .x .x6 .x6 .x12, .lsl .x .x7 .x13 2, .add .x .x7 .x7 .x13]

/-- `r0, …, r4` (in `x9`–`x13`) and `s1, …, s4` (in `x4`–`x7`) stored. -/
def storeCoefs : List Instr :=
  [.str .w .x9 .x0 (rOff 0), .str .w .x10 .x0 (rOff 1), .str .w .x11 .x0 (rOff 2),
    .str .w .x12 .x0 (rOff 3), .str .w .x13 .x0 (rOff 4),
    .str .w .x4 .x0 (sOff 1), .str .w .x5 .x0 (sOff 2), .str .w .x6 .x0 (sOff 3),
    .str .w .x7 .x0 (sOff 4)]

/-- The limbs of the clamped `r` and `sj = 5 rj`, stored in the state. -/
def coeffs : List Instr := load2 .x0 24 ++ clampR ++ split ++ times5 ++ storeCoefs

/-- The limbs of the stored `h = w0 + 2⁶⁴ w1 + 2¹²⁸ w2` into `x4`–`x8`: those of
`w0 + 2⁶⁴ w1`, with `2²⁴ w2` added to the last. -/
def moveH : List Instr :=
  [.ldr .x .x16 .x0 16, .lsl .x .x16 .x16 24, .addImm .x .x4 .x9 0, .addImm .x .x5 .x10 0,
    .addImm .x .x6 .x11 0, .addImm .x .x7 .x12 0, .add .x .x8 .x13 .x16]

def loadH : List Instr := load2 .x0 0 ++ split ++ moveH

/-- Everything `blocks` does first. -/
def setup : List Instr := mask ++ coeffs ++ loadH

/-! ## Absorbing a block -/

/-- `hi += xi` for the limbs `xi` in `x9`–`x13`. -/
def addLimbs : List Instr :=
  [.add .x .x4 .x4 .x9, .add .x .x5 .x5 .x10, .add .x .x6 .x6 .x11, .add .x .x7 .x7 .x12,
    .add .x .x8 .x8 .x13]

/-- `h += 2¹²⁸`. -/
def padBit : List Instr := [.movz .x .x16 0x100 1, .add .x .x8 .x8 .x16]

/-- `h += m` for the block `m` at `x1`, and `h += 2¹²⁸` if `pad`. -/
def addBlock (pad : Bool) : List Instr :=
  load2 .x1 0 ++ split ++ addLimbs ++ (if pad then padBit else [])

/-- The offset of the coefficient of `hi` in `dk`: `r(k-i)`, or `s(k+5-i)`. -/
def coef (k i : Nat) : Nat := if i ≤ k then rOff (k - i) else sOff (k + 5 - i)

/-- `d += h · c`, with the coefficient `c` loaded from `[x0 + off]` into `x14`. -/
def mac (d h : Reg) (off : Nat) : List Instr := [.ldr .w .x14 .x0 off, .madd .x d h .x14 d]

/-- `dk = Σ hi · coef k i`, into `x(9+k)`. -/
def dsum (k : Nat) : List Instr :=
  ([.ldr .w .x14 .x0 (coef k 0), .mul .x (D.getD k .x9) .x4 .x14] : List Instr) ++
    (List.range 4).flatMap fun i => mac (D.getD k .x9) (H.getD (i + 1) .x4) (coef k (i + 1))

def products : List Instr := (List.range 5).flatMap dsum

/-- The carry out of `d` into `d'`, leaving the low 26 bits in `h`. -/
def carryStep (d h d' : Reg) : List Instr :=
  [.lsr .x .x14 d 26, .logic .and .x h d .x17, .add .x d' d' .x14]

/-- The carries from `d0` to `d4`, the carry out of `d4` added, times 5, to
`h0`, and the carry out of `h0` into `h1`. -/
def carry : List Instr :=
  carryStep .x9 .x4 .x10 ++ carryStep .x10 .x5 .x11 ++ carryStep .x11 .x6 .x12 ++
  carryStep .x12 .x7 .x13 ++
  ([.lsr .x .x14 .x13 26, .logic .and .x .x8 .x13 .x17, .lsl .x .x15 .x14 2,
    .add .x .x14 .x14 .x15, .add .x .x4 .x4 .x14] : List Instr) ++
  carryStep .x4 .x4 .x5

/-- Absorbing the block at `x1`, with `pad` for a whole block (the `0x01`
byte appended to it is `2¹²⁸`), without for a padded last block (whose
`0x01` byte is inside it). -/
def absorb (pad : Bool) : List Instr := addBlock pad ++ products ++ carry

/-! ## The final reduction -/

/-- The limbs `h1, h2, h3` normalized, carrying into `h4`. -/
def normalize : List Instr := carryStep .x5 .x5 .x6 ++ carryStep .x6 .x6 .x7 ++ carryStep .x7 .x7 .x8

/-- `g = h + 5`, normalized, in `x9`–`x13`, and the mask `⌊g / 2¹³⁰⌋ - 1` in
`x14`. -/
def plus5 : List Instr := [
  .addImm .x .x9 .x4 5,
  .lsr .x .x14 .x9 26, .logic .and .x .x9 .x9 .x17, .add .x .x10 .x5 .x14,
  .lsr .x .x14 .x10 26, .logic .and .x .x10 .x10 .x17, .add .x .x11 .x6 .x14,
  .lsr .x .x14 .x11 26, .logic .and .x .x11 .x11 .x17, .add .x .x12 .x7 .x14,
  .lsr .x .x14 .x12 26, .logic .and .x .x12 .x12 .x17, .add .x .x13 .x8 .x14,
  .lsr .x .x14 .x13 26, .logic .and .x .x13 .x13 .x17, .subImm .x .x14 .x14 1]

/-- `h := g ^ ((h ^ g) & mask)`: `h` if the mask is all ones, `g` if it is zero. -/
def selectLimb (h g : Reg) : List Instr :=
  [.logic .eor .x .x15 h g, .logic .and .x .x15 .x15 .x14, .logic .eor .x h g .x15]

def select : List Instr :=
  selectLimb .x4 .x9 ++ selectLimb .x5 .x10 ++ selectLimb .x6 .x11 ++ selectLimb .x7 .x12 ++
  selectLimb .x8 .x13

/-- `h` reduced fully. -/
def reduce : List Instr := normalize ++ plus5 ++ select

/-- The limbs of `h` packed into the 64-bit words `x14, x15, x16`. -/
def pack : List Instr := [
  .lsl .x .x9 .x5 26, .add .x .x14 .x4 .x9, .lsl .x .x9 .x6 52, .add .x .x14 .x14 .x9,
  .lsr .x .x15 .x6 12, .lsl .x .x9 .x7 14, .add .x .x15 .x15 .x9, .lsl .x .x9 .x8 40,
  .add .x .x15 .x15 .x9,
  .lsr .x .x16 .x8 24]

/-! ## `init(state = x0, key = x1)`

It copies the key to the state through `x2`–`x5`, and clears them before it
returns, so that it leaves no word of the key in a register: `x2` holds the
zeros of the accumulator, `x3`–`x5` are cleared at the end. -/

def init : Prog isa := .block [
  .ldr .x .x2 .x1 0, .ldr .x .x3 .x1 8, .ldr .x .x4 .x1 16, .ldr .x .x5 .x1 24,
  .str .x .x2 .x0 24, .str .x .x3 .x0 32, .str .x .x4 .x0 40, .str .x .x5 .x0 48,
  .movz .x .x2 0 0, .str .x .x2 .x0 0, .str .x .x2 .x0 8, .str .x .x2 .x0 16,
  .movz .x .x3 0 0, .movz .x .x4 0 0, .movz .x .x5 0 0]

/-! ## `blocks(state = x0, blocks = x1, n = x2)` -/

def advance : List Instr := [.addImm .x .x1 .x1 16, .subImm .x .x2 .x2 1]

def body : Prog isa := .block (absorb true ++ advance)

/-- `h` stored. -/
def storeH : List Instr := [.str .x .x14 .x0 0, .str .x .x15 .x0 8, .str .x .x16 .x0 16]

def blocks : Prog isa :=
  .seq (.block setup)
  (.seq (.ite (.zero .x .x2) (.block []) (.loop body (.nonzero .x .x2)))
    (.block (reduce ++ pack ++ storeH)))

/-! ## `update(state = x0, count = x1, data = x2, len = x3)`

With `x9` = the number of bytes in the buffer (`count mod 16`), `x2` = the
data not yet consumed and `x3` = its length: a non-empty buffer is filled
from the data (as far as it goes) and, once full, absorbed; then the whole
blocks of the data are absorbed, and the rest is copied into the buffer. -/

/-- Copies the `x10 > 0` bytes at `x1` to `[x11 + 56]` on, advancing `x1` and `x11`. -/
def copyBody : List Instr :=
  [.ldrb .x12 .x1 0, .strb .x12 .x11 56, .addImm .x .x1 .x1 1, .addImm .x .x11 .x11 1,
    .subImm .x .x10 .x10 1]

def copyIn : Prog isa := .loop (.block copyBody) (.nonzero .x .x10)

/-- The number of bytes to copy into the buffer, `n = min(16 - x9, x3)`, into
`x10` (if `x3 < 16`, `x3 < 16 - x9` is the sign of `x3 - (16 - x9)`); then
`x3 -= n`, the buffer's byte `x9` at `[x11 + 56]`, `x9 += n`, and the data into
`x1`. -/
def count : Prog isa :=
  .seq (.block [.movz .x .x10 16 0, .sub .x .x10 .x10 .x9, .lsr .x .x11 .x3 4])
  (.seq (.ite (.zero .x .x11)
      (.seq (.block [.sub .x .x12 .x3 .x10, .lsr .x .x12 .x12 63])
        (.ite (.zero .x .x12) (.block []) (.block [.addImm .x .x10 .x3 0])))
      (.block []))
    (.block [.sub .x .x3 .x3 .x10, .add .x .x11 .x0 .x9, .add .x .x9 .x9 .x10,
      .addImm .x .x1 .x2 0]))

/-! ## `finalize(state = x0, count = x1, out = x2)`

`out` is moved to `x3`, and `count mod 16`, the number of bytes in the
buffer, to `x2`. A non-empty buffer is padded in place with `0x01` and zeros
and absorbed without `pad`. Then `h` is reduced, `s` is added (as limbs, with
carries), and the low 128 bits of the sum are the tag. -/

/-- Zeros the buffer from `[x9 + 56]` on, for `x10 > 0` bytes. -/
def zeroBody : List Instr := [.strb .x11 .x9 56, .addImm .x .x9 .x9 1, .subImm .x .x10 .x10 1]

end VG.Impl.Poly1305.AArch64
