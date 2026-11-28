module

public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Impl.Bignum.Layout

/-!
# Multiword arithmetic on x86-64: the baseline

Numbers of `w` 64-bit words, little-endian, in arrays in the working space,
for a `w` known only at run time. Every loop runs over the words of an array
(its counter compared with `w`), and every address is an array's base plus
8 times a counter: only `w` and the bases may affect timing.

The working space's base is in `rdi`. Its first 256 bytes are a header of 32
words: the callee-saved registers, `w`, `-m⁻¹ mod 2⁶⁴`, the bases of the
arrays, and the functions' own values (their arguments, counters); the
arrays follow, each `w + 2` words.

* `montMul o a b`: `[o] = [a] [b] R⁻¹ mod m` for `R = 2^(64 w)`, by
  coarsely integrated operand scanning (CIOS), with the accumulator
  (`w + 2` words) in memory, then a subtraction of `m` selected by a mask.
  `o` may be `a` or `b`. The arrays are given by the header slots of their
  bases.
* `double o`: `[o] = 2 [o] mod m`.
* `loadBE`, `storeBE`: an array from and to big-endian bytes.

The registers: `rdi` the working space; `r8` the accumulator, `r9` `b`,
`r10` `m`, `r11` `a`; `r12` `w`; `r13`, `r14` counters; `r15` `-m⁻¹`;
`rcx` a word of `a` or the multiple `u` of `m`; `rbp` a carry or a borrow
mask; `rax`, `rdx`, `rsi`, `rbx` temporaries.
-/

@[expose] public section

namespace VG.Impl.Bignum.X86_64

open VG.X86_64

/-- `[rdi + 8 i]`: header slot `i`. -/
def hdr (i : Nat) : MemOp := { base := .rdi, disp := 8 * i }

/-- `[b + 8 i + d]`: word `i` of the array at `b`, `i` in a register. -/
def ix (b i : Reg) (d : Int := 0) : MemOp := { base := b, index := some i, scale := 8, disp := d }

/-- `[b]`. -/
def at0 (b : Reg) : MemOp := { base := b }

/-! ## The header -/

/-- Slots 0–5: `rbx`, `rbp`, `r12`, `r13`, `r14`, `r15` on entry. -/
def saved : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-! Slots 6 and 7 (`w`, `-m⁻¹ mod 2⁶⁴`), the arrays' bases and the
functions' own slots: `Impl/Bignum/Layout.lean`, the same on every target. -/

export VG.Impl.Bignum (sW sMinv sArr sFn hdrBytes)

/-! ## Carries kept in a register

The loops' counters clobber the flags, so a chain of `adc` or `sbb` keeps its
carry in `rbp` between iterations, as 0 or all ones: `add rbp, rbp` sets the
carry flag from it, and `sbb rbp, rbp` puts it back. -/

def cfFromRbp : Instr := .alu .add .rbp (.reg .rbp)
def cfToRbp : Instr := .alu .sbb .rbp (.reg .rbp)

/-! ## Loops over the words -/

/-- `do body; r14 += 1 while r14 ≠ r12`, starting at `r14 = start`. -/
def wordLoop (start : Nat) (body : List Instr) : Prog isa :=
  .seq (.block [.mov .r14 (.imm (BitVec.ofNat 32 start))])
    (.loop (.block (body ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) .ne)

/-- Load the bases of `o`, `a`, `b`, `m`, the accumulator and the temporary
from the header: `rbx`, `r11`, `r9`, `r10`, `r8`, `rsi`. All loads from the
header come before any store of a secret, so the bases stay public to the
taint analysis. -/
def bases (o a b mo acc tmp : Nat) : List Instr :=
  [.mov .rbx (.mem (hdr (sArr o))), .mov .r11 (.mem (hdr (sArr a))), .mov .r9 (.mem (hdr (sArr b))),
    .mov .r10 (.mem (hdr (sArr mo))), .mov .r8 (.mem (hdr (sArr acc))),
    .mov .r12 (.mem (hdr sW)), .mov .r15 (.mem (hdr sMinv)), .mov .rsi (.mem (hdr (sArr tmp)))]

def zeroAccLoop : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0)])
    (.seq (wordLoop 0 [.store (ix .r8 .r14) .rax])
      (.block [.store (ix .r8 .r12) .rax, .store (ix .r8 .r12 8) .rax]))

/-- A multiply-accumulate step at word `r14`: the low word of
`rcx · [src] + acc + rbp` stored at `acc + d` (`d` is 0 or -8), and its
high word into `rbp`. The accumulator's word is added before the carry, so
that the carry from one step to the next passes through one addition (`add`,
`adc`) rather than two. -/
def mac (src : Reg) (d : Int) : List Instr :=
  [.mov .rax (.mem (ix src .r14)), .mul .rcx, .alu .add .rax (.mem (ix .r8 .r14)), .alu .adc .rdx (.imm 0),
    .alu .add .rax (.reg .rbp), .alu .adc .rdx (.imm 0), .store (ix .r8 .r14 d) .rax,
    .mov .rbp (.reg .rdx)]

/-- Words `w` and `w + 1` of the accumulator `+= rbp`: `[r8 + 8 r12] += rbp`,
then its carry into `[r8 + 8 r12 + 8]`. -/
def rowTop : List Instr :=
  [.mov .rax (.mem (ix .r8 .r12)), .alu .add .rax (.reg .rbp), .store (ix .r8 .r12) .rax,
    .mov .rax (.mem (ix .r8 .r12 8)), .alu .adc .rax (.imm 0), .store (ix .r8 .r12 8) .rax]

/-- `acc += rcx · [r9]`, its carry word added into words `w` and `w + 1`. -/
def mulAddRow : Prog isa :=
  .seq (.block [.mov32 .rbp (.imm 0)]) (.seq (wordLoop 0 (mac .r9 0)) (.block rowTop))

/-- `u = acc₀ · (-m⁻¹) mod 2⁶⁴` into `rcx`, and the carry of `acc₀ + u m₀`
(whose low word is zero) into `rbp`. -/
def redHead : List Instr :=
  [.mov .rax (.mem (at0 .r8)), .mul .r15, .mov .rcx (.reg .rax), .mov .rax (.mem (at0 .r10)), .mul .rcx,
    .alu .add .rax (.mem (at0 .r8)), .alu .adc .rdx (.imm 0), .mov .rbp (.reg .rdx)]

/-- Words `w` and `w + 1` of the accumulator plus the carry `rbp`, stored one
word down, and word `w + 1` zeroed. -/
def redTop : List Instr :=
  [.mov .rax (.mem (ix .r8 .r12)), .alu .add .rax (.reg .rbp), .store (ix .r8 .r12 (-8)) .rax,
    .mov .rax (.mem (ix .r8 .r12 8)), .alu .adc .rax (.imm 0), .store (ix .r8 .r12) .rax,
    .mov32 .rax (.imm 0), .store (ix .r8 .r12 8) .rax]

/-- `acc := (acc + u · [r10]) / 2⁶⁴` for `u = acc₀ · (-m⁻¹) mod 2⁶⁴` (in
`rcx`), which makes the low word zero: word 0, then words 1 to `w - 1` each
stored one word down, then the top words. -/
def reduceRow : Prog isa :=
  .seq (.block redHead) (.seq (wordLoop 1 (mac .r10 (-8))) (.block redTop))

/-- One round `i = r13` of the multiplication. -/
def round : Prog isa :=
  .seq (.block [.mov .rcx (.mem (ix .r11 .r13))]) (.seq mulAddRow reduceRow)

/-- The rounds, for `r13` from 0 to `w - 1`. -/
def rounds : Prog isa :=
  .seq (.block [.mov .r13 (.imm 0)])
    (.loop (.seq round (.block [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.reg .r12)])) .ne)

/-- `[rsi] = acc - [r10]` over `w` words, then `rbp` all ones if
`acc < [r10]` (counting the top word `w` of `acc`) and 0 otherwise. -/
def subMod : Prog isa :=
  .seq (.block [.mov32 .rbp (.imm 0)])
    (.seq (wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .r8 .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
      .store (ix .rsi .r14) .rax, cfToRbp])
    (.block [.mov .rax (.mem (ix .r8 .r12)), cfFromRbp, .alu .sbb .rax (.imm 0), cfToRbp]))

/-- `[rbx] = rbp ? acc : [rsi]`, word by word. -/
def selectAcc : Prog isa :=
  wordLoop 0 [.mov .rax (.mem (ix .r8 .r14)), .mov .rdx (.mem (ix .rsi .r14)), .alu .xor .rax (.reg .rdx),
    .alu .and .rax (.reg .rbp), .alu .xor .rax (.reg .rdx), .store (ix .rbx .r14) .rax]

/-- `[o] = [a] [b] R⁻¹ mod m`, with the accumulator at array `acc` and the
temporary array `tmp`; `m` is array `mo`. -/
def montMul (mo acc tmp o a b : Nat) : Prog isa :=
  .seq (.block (bases o a b mo acc tmp)) (.seq zeroAccLoop (.seq rounds (.seq subMod selectAcc)))

/-- `[o] = 2 [o] mod m` for `[o] < m`: the double into the accumulator
(`w + 1` words), then the subtraction of `m` selected as in `montMul`. -/
def double (mo acc tmp o : Nat) : Prog isa :=
  .seq (.block [.mov .rbx (.mem (hdr (sArr o))), .mov .r10 (.mem (hdr (sArr mo))),
      .mov .r8 (.mem (hdr (sArr acc))), .mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr tmp))),
      .mov32 .rbp (.imm 0)])
    (.seq (wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .adc .rax (.reg .rax),
      .store (ix .r8 .r14) .rax, cfToRbp])
    (.seq (.block [.mov32 .rax (.imm 0), cfFromRbp, .alu .adc .rax (.imm 0), .store (ix .r8 .r12) .rax])
    (.seq subMod selectAcc)))

/-! ## Bytes and words -/

/-- `p := p - 1`, then the byte at `r14` appended to `rax` (shifted left a
byte: `rax < 2⁵⁶`), `r14` advanced, and ZF set iff `p % 8 = 0`. -/
def loadByte : List Instr :=
  [.alu .sub .rdx (.imm 1), .shift .ror .rax 56, .movzx8 .rbp (at0 .r14), .alu .add .rax (.reg .rbp),
    .alu .add .r14 (.imm 1), .mov .rbp (.reg .rdx), .alu .and .rbp (.imm 7)]

/-- `rax` stored as word `p / 8` of the array at `rbx`, and cleared. -/
def storeWord : List Instr :=
  [.mov .rbp (.reg .rdx), .shift .shr .rbp 3, .store (ix .rbx .rbp) .rax, .mov32 .rax (.imm 0)]

/-- The `k` bytes at `rsi`, most significant first, into the `w` words of
the array at `rbx` (`k` in `rcx`, `w = ⌈k / 8⌉`): byte `i` is bit position
`8 p` for `p = k - 1 - i`, accumulated in `rax` and stored as word `p / 8`
when `p % 8 = 0`. `rdx` counts `p` down from `k - 1`. -/
def loadBE : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .mov .rdx (.reg .rcx), .mov .r14 (.reg .rsi)])
    (.loop (.seq (.block loadByte) (.seq (.ite .e (.block storeWord) (.block []))
      (.block [.alu .test .rdx (.reg .rdx)]))) .ne)

/-- The low `k` bytes of the `w` words at `rbx`, each masked with `r15`,
to the `k` bytes at `rsi`, most significant first (`k` in `rcx`): for `p`
from 0 to `k - 1`, byte `k - 1 - p` is the low byte of `rax`, which is word
`p / 8` shifted right by `8 (p % 8)`. -/
def storeBE : Prog isa :=
  .seq (.block [.mov32 .rdx (.imm 0), .mov .r14 (.reg .rsi), .alu .add .r14 (.reg .rcx)])
    (.loop (.seq (.block [.mov .rbp (.reg .rdx), .alu .and .rbp (.imm 7)])
      (.seq (.ite .e (.block [.mov .rbp (.reg .rdx), .shift .shr .rbp 3,
          .mov .rax (.mem (ix .rbx .rbp)), .alu .and .rax (.reg .r15)]) (.block []))
        (.block [.alu .sub .r14 (.imm 1), .store8 (at0 .r14) .rax, .shift .shr .rax 8,
          .alu .add .rdx (.imm 1), .alu .cmp .rdx (.reg .rcx)]))) .ne)

/-- `c₁; c₂; …`. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-! ## Setting up -/

/-- The base of array `j` (in `rdx`) into its slot, and `rdx` advanced by
`rax` bytes. -/
def setBase (j : Nat) : List Instr := [.store (hdr (sArr j)) .rdx, .alu .add .rdx (.reg .rax)]

/-- The arrays' bases, `w + 2` words apart after the header, into slots
`sArr 0` to `sArr 7`; `w` in `r12`. -/
def setBases : List Instr :=
  ([.mov .rax (.reg .r12), .alu .add .rax (.imm 2), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .mov .rdx (.reg .rdi),
    .alu .add .rdx (.imm (BitVec.ofNat 32 hdrBytes))] : List Instr) ++ (List.range 8).flatMap setBase

/-- A step of Newton's iteration: `rcx := rcx (2 - rbx rcx)`. -/
def newton : List Instr :=
  [.mov .rax (.reg .rbx), .mul .rcx, .mov32 .rsi (.imm 2), .alu .sub .rsi (.reg .rax), .mov .rax (.reg .rcx),
    .mul .rsi, .mov .rcx (.reg .rax)]

/-- `-m⁻¹ mod 2⁶⁴` for the odd `m₀` in `rbx`, into `r15`: Newton's
iteration `x ↦ x (2 - m₀ x)` five times from `x = m₀`, which is right
modulo 8, then the negation. -/
def minv : List Instr :=
  ([.mov .rcx (.reg .rbx)] : List Instr) ++ newton ++ newton ++ newton ++ newton ++ newton ++
  ([.mov32 .r15 (.imm 0), .alu .sub .r15 (.reg .rcx)] : List Instr)

/-- `[o] := 0` but its word `i`, which is `rdx`. `w` in `r12`. -/
def setWord (o : Nat) (i : Reg) : Prog isa :=
  .seq (.block [.mov .r8 (.mem (hdr (sArr o)))]) (.seq zeroAccLoop (.block [.store (ix .r8 i) .rdx]))

/-- `rdx := 2^j` and `rcx := 64 - j` for the top bit `j` of the nonzero
`rax`: `rax` is halved and `rdx` doubled until `rax = 1`. -/
def topBit : Prog isa :=
  .seq (.block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 64), .alu .cmp .rax (.imm 1)])
    (.ite .e (.block [])
      (.loop (.block [.shift .shr .rax 1, .alu .add .rdx (.reg .rdx), .alu .sub .rcx (.imm 1),
        .alu .cmp .rax (.imm 1)]) .ne))

/-- `double` `rcx` times (a public count, at least 1), counted in a header
slot. -/
def doubles (mo acc tmp o slot : Nat) : Prog isa :=
  .seq (.block [.store (hdr slot) .rcx])
    (.loop (.seq (double mo acc tmp o)
      (.block [.mov .rcx (.mem (hdr slot)), .alu .sub .rcx (.imm 1), .store (hdr slot) .rcx])) .ne)

/-! ## `vg_rsa_public`

`(out, out_len, n, n_len, e, e_len, input, input_len, scratch,
scratch_len)`: the first six in `rdi`, `rsi`, `rdx`, `rcx`, `r8`, `r9`,
the others on the stack. The arrays: `m` (0), the input (1), the
accumulator (2), a temporary (3), `R² mod m` (4), the input in Montgomery
form (5), the result (6) and the number 1 (7). -/

namespace Public

/-! The arrays and the header slots of the arguments and counters
(`Impl/Bignum/Layout.lean`). -/

export VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sOut sN sK sE sElen sIn sMask sI sBit sV
  sCnt)

/-- `[o] = [a] [b] R⁻¹ mod m`. -/
def mm (o a b : Nat) : Prog isa := montMul aN aAcc aTmp o a b

/-- Save the callee-saved registers and the arguments in the header, with
the working space's base in `rdi`. -/
def entry : List Instr :=
  ([.mov .r11 (.mem { base := .rsp, disp := 24 })] : List Instr) ++
  (saved.zipIdx.map fun (r, i) => .store { base := .r11, disp := 8 * i } r) ++
  ([.store { base := .r11, disp := 8 * sOut } .rdi, .store { base := .r11, disp := 8 * sN } .rdx,
    .store { base := .r11, disp := 8 * sK } .rcx, .store { base := .r11, disp := 8 * sE } .r8,
    .store { base := .r11, disp := 8 * sElen } .r9, .mov .rax (.mem { base := .rsp, disp := 8 }),
    .store { base := .r11, disp := 8 * sIn } .rax, .mov .rdi (.reg .r11)] : List Instr)

/-- Restore the callee-saved registers. -/
def exit : List Instr := saved.zipIdx.map fun (r, i) => .mov r (.mem (hdr i))

/-- `rbp` all ones if `m` (`k` bytes at `rdx`, `k` in `rcx`) is not a valid
modulus: its first byte is zero, it is even, or it is below `2^511`, which
for `k ≥ 64` is `256 (k - 64) + m[0] < 128`. Each is a borrow of a
comparison, made a mask by `sbb`. -/
def invalid : List Instr :=
  [.movzx8 .rax (at0 .rdx), .alu .cmp .rax (.imm 1), .alu .sbb .rbp (.reg .rbp),
    .movzx8 .rax { base := .rdx, index := some .rcx, disp := -1 }, .alu .and .rax (.imm 1),
    .alu .cmp .rax (.imm 1), .alu .sbb .rsi (.reg .rsi), .alu .or .rbp (.reg .rsi),
    .mov .rsi (.reg .rcx), .alu .sub .rsi (.imm 64), .shift .ror .rsi 56,
    .movzx8 .rax (at0 .rdx), .alu .add .rsi (.reg .rax), .alu .cmp .rsi (.imm 128),
    .alu .sbb .rsi (.reg .rsi), .alu .or .rbp (.reg .rsi), .alu .test .rbp (.reg .rbp)]

/-- Zeros to the `k` bytes of `out`, and 0 returned. -/
def fail : Prog isa :=
  .seq (.block [.mov .rsi (.mem (hdr sOut)), .mov .rcx (.mem (hdr sK)), .mov32 .rax (.imm 0)])
    (.seq (.loop (.block [.store8 (at0 .rsi) .rax, .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne)
      (.block exit))

/-- The bit of `e` at the top of the byte in `sV`, into ZF. -/
def bitTest : List Instr := [.mov .rax (.mem (hdr sV)), .shift .shr .rax 7, .alu .and .rax (.imm 1)]

/-- The next bit: `sV := 2 sV`, `sBit := sBit - 1` (ZF set when 0). -/
def bitNext : List Instr :=
  [.mov .rax (.mem (hdr sV)), .alu .add .rax (.reg .rax), .store (hdr sV) .rax,
    .mov .rax (.mem (hdr sBit)), .alu .sub .rax (.imm 1), .store (hdr sBit) .rax]

/-- One bit of `e`: `Y := Y²`, then `Y := Y X` if the bit is set. -/
def expBit : Prog isa :=
  .seq (mm aY aY aY) (.seq (.block bitTest) (.seq (.ite .ne (mm aY aY aXm) (.block [])) (.block bitNext)))

/-- Byte `sI` of `e` into `sV`, and `sBit := 8`. -/
def byteHead : List Instr :=
  [.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr sI)), .movzx8 .rax { base := .rax, index := some .rcx },
    .store (hdr sV) .rax, .mov32 .rax (.imm 8), .store (hdr sBit) .rax]

/-- The next byte: `sI := sI + 1`, ZF set when it is `e_len`. -/
def byteNext : List Instr :=
  [.mov .rax (.mem (hdr sI)), .alu .add .rax (.imm 1), .store (hdr sI) .rax, .alu .cmp .rax (.mem (hdr sElen))]

/-- The exponentiation: for each byte of `e`, most significant first, and
each of its bits, most significant first: `Y := Y²`, then `Y := Y X` if the
bit is set. -/
def expLoop : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .store (hdr sI) .rax])
    (.loop (.seq (.block byteHead) (.seq (.loop expBit .ne) (.block byteNext))) .ne)

/-- The computation, once `m` is known valid. -/
def main : Prog isa := seqs [
  -- `w`, the bases, `m` and the input.
  .block (([.mov .rcx (.mem (hdr sK)), .mov .r12 (.reg .rcx), .alu .add .r12 (.imm 7),
    .shift .shr .r12 3, .store (hdr sW) .r12] : List Instr) ++ setBases ++
    ([.mov .rsi (.mem (hdr sN)), .mov .rbx (.mem (hdr (sArr aN)))] : List Instr)),
  loadBE,
  .block [.mov .rsi (.mem (hdr sIn)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))],
  loadBE,
  -- The mask of `input < m`.
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))),
    .mov .r10 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)],
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
    cfToRbp],
  -- `-m⁻¹`, and the number 1.
  .block (([.store (hdr sMask) .rbp, .mov .rbx (.mem (at0 .r10))] : List Instr) ++ minv ++
    ([.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)] : List Instr)),
  setWord aOne .rcx,
  -- `2^(b - 1)` for the bit length `b` of `m`, into the array of `R² mod m`.
  .block [.mov .rax (.mem (ix .r10 .r12 (-8)))],
  topBit,
  .block [.store (hdr sCnt) .rcx, .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 1)],
  setWord aR2 .rcx,
  -- `2^w R mod m`, then six squarings: `R² mod m`.
  .block [.mov .rcx (.mem (hdr sCnt)), .alu .add .rcx (.mem (hdr sW))],
  doubles aN aAcc aTmp aR2 sCnt,
  mm aR2 aR2 aR2, mm aR2 aR2 aR2, mm aR2 aR2 aR2, mm aR2 aR2 aR2, mm aR2 aR2 aR2, mm aR2 aR2 aR2,
  -- `Y = R mod m`, `X = input R mod m`, the exponentiation, and `Y R⁻¹`.
  mm aY aR2 aOne, mm aXm aX aR2, expLoop, mm aY aY aOne,
  -- The result, masked, and the mask's low bit returned.
  .block [.mov .rbx (.mem (hdr (sArr aY))), .mov .rsi (.mem (hdr sOut)), .mov .rcx (.mem (hdr sK)),
    .mov .r15 (.mem (hdr sMask))],
  storeBE,
  .block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)]

/-- `vg_rsa_public`. -/
def code : Prog isa :=
  .seq (.block (entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid))
    (.ite .ne fail main)

end Public

end VG.Impl.Bignum.X86_64
