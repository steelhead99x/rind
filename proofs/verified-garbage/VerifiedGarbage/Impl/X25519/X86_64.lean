module

public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Spec.X25519

/-!
# X25519: x86-64 implementation

`vg_x25519(out = rdi, scalar = rsi, point = rdx, scratch = rcx)`.

A field element is four 64-bit words `x0 + 2⁶⁴ x1 + 2¹²⁸ x2 + 2¹⁹² x3`,
any number below `2²⁵⁶`, standing for its residue modulo `p = 2²⁵⁵ - 19`;
only the result is reduced fully. Every element lives in the working space,
at a constant offset from its base, which is in `rdi` once the arguments are
read (`out` then in `rsi`):

* `[0, 48)`: the saved `rbx, rbp, r12–r15`;
* `x1, x2, z2, x3, z3` and the ladder's temporaries, 32 bytes each (`X1`, …);
* `swap` (a word, 0 or 1) and the bits of the clamped scalar `k` (`BITS`,
  byte `t` is bit `t` of `k`).

The arithmetic (registers `rax, rdx, rcx, rbp, r8–r15`), whose
multiplications (`mul`, `sqr`, and `mulSmallAdd` by `a24`) are the
`Field` `baseline`; the rest of the code takes them as a parameter
(`x25519With`), so that `vg_x25519_adx` (`X86_64/Adx.lean`) is this code with
other multiplications:

* `mul`: the 512-bit product, column by column (`r8–r15`, each product
  added to the three words of its column), with `b` in registers; then
  `lo + 38 hi` (as `2²⁵⁶ ≡ 38`), whose carry word and bit 255 are folded in
  as 19 each (`2²⁵⁵ ≡ 19`);
* `add`, `sub`: with carries (borrows), each carry folded in (subtracted) as
  38, twice; `addCmov` and `subCmov`, the ladder's, once, which is enough when an
  operand is at most `2p`, as products are;
* `sqr`: the products `a_i a_j` for `i < j` once, as columns of `mul`, then
  doubled, and the squares `a_i²` added; reduced as `mul`;
* `mulSmallAdd`: an element plus another by a one-word constant (`a24`),
  folded as for `mul`;
* `cswap`: with the mask `-swap`, as RFC 7748 §5 describes (once, after
  the ladder); `mux`: with `cmove`, choosing the point an iteration doubles;
* `freeze`: the full reduction of the result, by folding bit 255 in as 19,
  then selecting `x + 19 - 2²⁵⁵` with a mask if it is not negative.

The ladder is s2n-bignum's `curve25519_x25519`'s (`step`): RFC 7748 §5's,
but with no swap of the points in its iterations, over the bits of `k` from
254 down to 0 (the counter `rbx`, which indexes `BITS`), and the
inversion `z2^(p-2)` is by Bernstein–Yang divsteps (`invertDS`), a call of
`vg_gf25519_r64_invert` (`invertCall`).

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.X25519.X86_64

open VG.X86_64

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `[rdi + d]`: byte `d` of the working space. -/
def sc (d : Nat) : MemOp := at_ .rdi d

/-! ## The layout of the working space -/

def X1 : Nat := 64
def X2 : Nat := 96
def Z2 : Nat := 128
def X3 : Nat := 160
def Z3 : Nat := 192
def A : Nat := 224
def B : Nat := 256
def C : Nat := 288
def D : Nat := 320
def T1 : Nat := 544
def SWAP : Nat := 640
def BITS : Nat := 768

/-- The words of a product, lowest first. -/
def T : List Reg := [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- `T[i]`. -/
def t (i : Nat) : Reg := T.getD i .r8

/-! ## Field arithmetic -/

/-- `t:c = t + c + ai · src` (a multiply-accumulate step; it never
overflows). -/
def mulStep (t c ai : Reg) (src : Src) : List Instr :=
  [.mov .rax src, .mul ai, .alu .add .rax (.reg c), .alu .adc .rdx (.imm 0),
    .alu .add t (.reg .rax), .alu .adc .rdx (.imm 0), .mov c (.reg .rdx)]

/-- `r8–r11 = 0`. -/
def zero4 : List Instr := [.mov32 .r8 (.imm 0), .mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0),
  .mov32 .r11 (.imm 0)]

/-- Row `i` of a product: `t[i..i+4] += a_i · b`, `a_i` from `[rdi + a + 8i]`,
`b` from `[rdi + b]`. -/
def row (a b i : Nat) : List Instr :=
  [.mov .rcx (.mem (sc (a + 8 * i))), .mov32 .rbp (.imm 0)] ++
    ((List.range 4).flatMap fun j => mulStep (t (i + j)) .rbp .rcx (.mem (sc (b + 8 * j)))) ++
    [.mov (t (i + 4)) (.reg .rbp)]

/-- `r8–r11 += rax`, with the carry out folded in as 38 (which cannot carry
again). -/
def carry38 : List Instr :=
  [.alu .add .r8 (.reg .rax), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
    .alu .adc .r11 (.imm 0), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38),
    .alu .add .r8 (.reg .rax)]

/-- `[rdi + o] = a, b, c, d`. -/
def stores (o : Nat) (a b c d : Reg) : List Instr :=
  [.store (sc o) a, .store (sc (o + 8)) b, .store (sc (o + 16)) c, .store (sc (o + 24)) d]

/-- `[rdi + o] = r8–r11`. -/
def store4 (o : Nat) : List Instr := stores o .r8 .r9 .r10 .r11

/-- `a, b, c, d = [rdi + o]`. -/
def loads (o : Nat) (a b c d : Reg) : List Instr :=
  [.mov a (.mem (sc o)), .mov b (.mem (sc (o + 8))), .mov c (.mem (sc (o + 16))),
    .mov d (.mem (sc (o + 24)))]

/-- `xor r, r` on the low halves: `r = 0`. -/
def zero (r : Reg) : Instr := .alu32 .xor r (.reg r)

/-- `t1:t0 = [rdi + a] · b`. -/
def prod2 (t0 t1 b : Reg) (a : Nat) : List Instr :=
  [.mov .rax (.mem (sc a)), .mul b, .mov t0 (.reg .rax), .mov t1 (.reg .rdx)]

/-- `t1:t0 += [rdi + a] · b`, where the sum cannot carry out. -/
def acc2 (t0 t1 b : Reg) (a : Nat) : List Instr :=
  [.mov .rax (.mem (sc a)), .mul b, .alu .add t0 (.reg .rax), .alu .adc t1 (.reg .rdx)]

/-- `t2:t1:t0 += [rdi + a] · b`: a product added to the three words of a
column of products. -/
def acc3 (t0 t1 t2 b : Reg) (a : Nat) : List Instr :=
  acc2 t0 t1 b a ++ [.alu .adc t2 (.imm 0)]

/-- `t1:t0 += 38 h + 2⁶⁴ c` (with `rcx = 38`), for the carry `c` that the mask
`rbp` holds (`sub`, into the product's high half, which is at most 37), the
carry out of it then the mask (`sbb`). -/
def redStep (t0 t1 h : Reg) : List Instr :=
  [.mov .rax (.reg h), .mul .rcx, .alu .sub .rdx (.reg .rbp), .alu .add t0 (.reg .rax),
    .alu .adc t1 (.reg .rdx), .alu .sbb .rbp (.reg .rbp)]

/-- `r8–r11 + 2²⁵⁶ r12 = r8–r11 + 38 · r12–r15`: each `38 h_i` (`rdx:rax`)
added at its two words, with the carry out of them kept as a mask in `rbp`
for the next (`redStep`). -/
def reduceLoC : List Instr :=
  [.mov32 .rcx (.imm 38),
    .mov .rax (.reg .r12), .mul .rcx, .alu .add .r8 (.reg .rax), .alu .adc .r9 (.reg .rdx),
    .alu .sbb .rbp (.reg .rbp)] ++
    redStep .r9 .r10 .r13 ++ redStep .r10 .r11 .r14 ++
    [.mov .rax (.reg .r15), .mul .rcx, .alu .sub .rdx (.reg .rbp), .alu .add .r11 (.reg .rax),
      .alu .adc .rdx (.imm 0), .mov .r12 (.reg .rdx)]

/-- `r8–r11 + 2²⁵⁶ r12` (`r12` small) folded at bit 255: bit 255 shifted out
into CF (`shl`) and in as `q = 2 r12 + bit 255` (`adc`), `r11` shifted back
with it cleared (`shr`), and `19 q` (`imul`) added, which cannot carry out
(at most `2p`). s2n-bignum's `mul_p25519` takes `q` with `shld` and clears
the bit with `btr`, one instruction fewer, but `shld` is several µops on AMD's
cores, on the chain of every multiplication. -/
def fold19X : List Instr :=
  [.shift .shl .r11 1, .alu .adc .r12 (.reg .r12), .shift .shr .r11 1, .imul3 .rax .r12 19,
    .alu .add .r8 (.reg .rax), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
    .alu .adc .r11 (.imm 0)]

/-- `r8–r11 = r8–r11 + 38 · r12–r15`, at most `2p`. -/
def reduceC : List Instr := reduceLoC ++ fold19X

/-- `r8–r12` doubled. -/
def dbl5 : List Instr :=
  [.alu .add .r8 (.reg .r8), .alu .adc .r9 (.reg .r9), .alu .adc .r10 (.reg .r10),
    .alu .adc .r11 (.reg .r11), .alu .adc .r12 (.reg .r12)]

/-- `r8–r11 = 2 · (r8–r11 + 38 · r12–r15)`: doubled before the fold at bit 255, five
instructions rather than an addition. -/
def reduceC2 : List Instr := reduceLoC ++ dbl5 ++ fold19X

/-- A column of products: each `[rdi + a] · b` of `ps` added to `t2:t1:t0`. -/
def accCol (t0 t1 t2 : Reg) (ps : List (Reg × Nat)) : List Instr :=
  ps.flatMap fun p => acc3 t0 t1 t2 p.1 p.2

/-- `r8–r15 = [a] · [b]`: `b` in `r14, r15, rcx, rbp`, and the products
`a_i b_j` column by column (`i + j`), each added to the three words of its
column (`accCol`), the two highest in the registers of `b₀` and `b₁`, which
the columns before them used last. -/
def mulProd (a b : Nat) : List Instr :=
  loads b .r14 .r15 .rcx .rbp ++
    prod2 .r8 .r9 .r14 a ++ [zero .r10] ++ [zero .r11] ++ acc2 .r9 .r10 .r15 a ++
    accCol .r9 .r10 .r11 [(.r14, a + 8)] ++
    [zero .r12] ++ accCol .r10 .r11 .r12 [(.rcx, a), (.r15, a + 8), (.r14, a + 16)] ++
    [zero .r13] ++ accCol .r11 .r12 .r13 [(.rbp, a), (.rcx, a + 8), (.r15, a + 16), (.r14, a + 24)] ++
    [zero .r14] ++ accCol .r12 .r13 .r14 [(.rbp, a + 8), (.rcx, a + 16), (.r15, a + 24)] ++
    [zero .r15] ++ accCol .r13 .r14 .r15 [(.rbp, a + 16), (.rcx, a + 24)] ++
    acc2 .r14 .r15 .rbp (a + 24)

/-- `[o] = [a] · [b]` (`o` may be `a` or `b`). -/
def mul (o a b : Nat) : List Instr := mulProd a b ++ reduceC ++ store4 o

/-- `[o] = 2 · [a] · [b]`. -/
def mul2 (o a b : Nat) : List Instr := mulProd a b ++ reduceC2 ++ store4 o

/-- `r9–r14 = Σ a_i a_j` (`i < j`), column by column, with `a₁, a₂, a₃` in
`rcx, rbp, r15`. -/
def sqrCross (a : Nat) : List Instr :=
  [.mov .rcx (.mem (sc (a + 8))), .mov .rbp (.mem (sc (a + 16))), .mov .r15 (.mem (sc (a + 24)))] ++
    prod2 .r9 .r10 .rcx a ++ [zero .r11] ++ [zero .r12] ++ [zero .r13] ++
    acc2 .r10 .r11 .rbp a ++
    accCol .r11 .r12 .r13 [(.r15, a), (.rbp, a + 8)] ++
    [zero .r14] ++ accCol .r12 .r13 .r14 [(.r15, a + 8)] ++
    acc2 .r13 .r14 .r15 (a + 16)

/-- `r9–r15 = 2 · r9–r14`. -/
def sqrDbl : List Instr :=
  [zero .r15, .alu .add .r9 (.reg .r9), .alu .adc .r10 (.reg .r10), .alu .adc .r11 (.reg .r11),
    .alu .adc .r12 (.reg .r12), .alu .adc .r13 (.reg .r13), .alu .adc .r14 (.reg .r14),
    .alu .adc .r15 (.reg .r15)]

/-- `t1:t0 += [rdi + d]² + c`, for the carry `c` that the mask `rcx` holds, set
again by doubling the mask (`add`). -/
def diagAdd (t0 t1 : Reg) (d : Nat) : List Instr :=
  [.mov .rax (.mem (sc d)), .mul .rax, .alu .add .rcx (.reg .rcx), .alu .adc t0 (.reg .rax),
    .alu .adc t1 (.reg .rdx)]

/-- `r8–r15 = r9–r15 · 2⁶⁴ + Σ a_i² 2¹²⁸ⁱ`: the squares added two words at a
time, the carry between them kept as a mask in `rcx` (`sbb`) across the next
`mul` (`diagAdd`). -/
def sqrDiag (a : Nat) : List Instr :=
  prod2 .r8 .rbp .rax a ++
    [.mov .rax (.mem (sc (a + 8))), .mul .rax, .alu .add .r9 (.reg .rbp), .alu .adc .r10 (.reg .rax),
      .alu .adc .r11 (.reg .rdx)] ++ [.alu .sbb .rcx (.reg .rcx)] ++
    diagAdd .r12 .r13 (a + 16) ++ [.alu .sbb .rcx (.reg .rcx)] ++ diagAdd .r14 .r15 (a + 24)

/-- `r8–r15 = [a]²`. -/
def sqrProd (a : Nat) : List Instr := sqrCross a ++ sqrDbl ++ sqrDiag a

/-- `[o] = [a]²`: the products `a_i a_j` (`i < j`) into `r9–r14`
(`sqrCross`), doubled into `r9–r15`, then the squares `a_i²` added
(`sqrDiag`), and reduced as in `mul`. -/
def sqr (o a : Nat) : List Instr := sqrProd a ++ reduceC ++ store4 o

/-- `[o] = 2 · [a]²`. -/
def sqr2 (o a : Nat) : List Instr := sqrProd a ++ reduceC2 ++ store4 o

/-- `[o] = [b] + k · [a]`, for a constant `k < 2³¹`: `k · [a]` into
`r8–r12`, a word of it at a time, `[b]` added, and `r12` folded at bit 255. -/
def mulSmallAdd (o b a : Nat) (k : BitVec 32) : List Instr :=
  [.mov32 .rcx (.imm k)] ++ prod2 .r8 .r9 .rcx a ++ [zero .r10] ++ [zero .r11] ++ [zero .r12] ++
    acc2 .r9 .r10 .rcx (a + 8) ++ acc2 .r10 .r11 .rcx (a + 16) ++ acc2 .r11 .r12 .rcx (a + 24) ++
    [.alu .add .r8 (.mem (sc b)), .alu .adc .r9 (.mem (sc (b + 8))),
      .alu .adc .r10 (.mem (sc (b + 16))), .alu .adc .r11 (.mem (sc (b + 24))),
      .alu .adc .r12 (.imm 0)] ++ fold19X ++ store4 o

/-- `[o] = [a] + [b]`. -/
def add (o a b : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
    .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
    .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
    .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
    .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++ carry38 ++ store4 o

/-- `[o] = [a] + [b]`, for `[a]` and `[b]` at most `2p`: the carry out folded in
once, as 38, which cannot carry again, since the sum is at most `4p`; the
result is at most `2p`. -/
def addL (o a b : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
    .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
    .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
    .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
    .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38),
    .alu .add .r8 (.reg .rax), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
    .alu .adc .r11 (.imm 0)] ++ store4 o

/-- `[o] = [a] - [b]`, for `[a]` and `[b]` at most `2p`: a borrow out
subtracted once, as 38, which cannot borrow again, since the difference is
then `[a] - [b] + 2p ≥ 0`; the result is at most `2p`. -/
def subL (o a b : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
    .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
    .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
    .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
    .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38),
    .alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
    .alu .sbb .r11 (.imm 0)] ++ store4 o

/-- `[o] = [a] + [b]`, for `[a]` or `[b]` at most `2p`, as `addL`, but with
the carry's 38 selected by `cmov` from a constant loaded before the sum: one
instruction after the carry rather than two, on a chain the ladder waits
for. `rcx` holds the zero `cmov` selects. -/
def addCmov (o a b : Nat) : List Instr :=
  [.alu32 .xor .rcx (.reg .rcx), .mov32 .rax (.imm 38),
    .mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
    .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
    .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
    .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
    .cmov .ae .rax (.reg .rcx),
    .alu .add .r8 (.reg .rax), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
    .alu .adc .r11 (.imm 0)] ++ store4 o

/-- `[o] = [a] - [b]`, for `[b]` at most `2p`, as `subL`, with the borrow's
38 selected by `cmov` as in `addCmov`. -/
def subCmov (o a b : Nat) : List Instr :=
  [.alu32 .xor .rcx (.reg .rcx), .mov32 .rax (.imm 38),
    .mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
    .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
    .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
    .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
    .cmov .ae .rax (.reg .rcx),
    .alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
    .alu .sbb .r11 (.imm 0)] ++ store4 o

/-- `[o] = [a] - [b]`: a borrow out is `2²⁵⁶ ≡ 38` too many, subtracted
(twice at most). -/
def sub (o a b : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
    .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
    .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
    .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
    .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38),
    .alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
    .alu .sbb .r11 (.imm 0), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38),
    .alu .sub .r8 (.reg .rax)] ++ store4 o

/-- Swaps `[x]` and `[y]` if the mask `rcx` is all ones (and not if it is
zero): both into `r8–r11` and `r12–r15`, then `d = rcx ∧ (x ⊕ y)`, `x ⊕= d`,
`y ⊕= d`, word by word (with `d` in `rax`), and both stored back. -/
def cswap (x y : Nat) : List Instr :=
  loads x .r8 .r9 .r10 .r11 ++ loads y .r12 .r13 .r14 .r15 ++
  ([(Reg.r8, Reg.r12), (.r9, .r13), (.r10, .r14), (.r11, .r15)].flatMap fun (a, b) =>
    [.mov .rax (.reg a), .alu .xor .rax (.reg b), .alu .and .rax (.reg .rcx),
      .alu .xor a (.reg .rax), .alu .xor b (.reg .rax)]) ++
  store4 x ++ stores y .r12 .r13 .r14 .r15

/-- The ladder's `a24 = 121665`. -/
def a24 : BitVec 32 := 121665

/-- The field multiplications, as each implementation of X25519 does them;
the rest of the code is the same for all. Both read the working space and
write `[o]` (which may be an operand), and use only the registers `rax`,
`rcx`, `rdx`, `rbp` and `r8–r15`. -/
structure Field where
  /-- `[o] = [a] · [b]` -/
  mul : Nat → Nat → Nat → List Instr
  /-- `[o] = [a]²` -/
  sqr : Nat → Nat → List Instr
  /-- `[o] = [b] + a24 · [a]` -/
  a24add : Nat → Nat → Nat → List Instr
  /-- `[o] = 2 · [a] · [b]` (Ed25519's doublings) -/
  mul2 : Nat → Nat → Nat → List Instr
  /-- `[o] = 2 · [a]²` (Ed25519's doublings) -/
  sqr2 : Nat → Nat → List Instr
  /-- The suffix of the functions built on these multiplications (`""` for the baseline's,
  `_adx` for BMI2 and ADX's). -/
  suffix : String := ""

/-- The baseline's: `mul`, `sqr` and `mulSmallAdd`, and `mul2` and `sqr2`, which double in the
reduction. -/
def baseline : Field where
  mul := mul
  sqr := sqr
  a24add o b a := mulSmallAdd o b a a24
  mul2 := mul2
  sqr2 := sqr2

/-! ## The ladder -/

/-- `[o] = [y]` if ZF is set, else `[x]`: both into `r8–r11` and
`r12–r15`, `cmove` word by word, and stored (s2n-bignum's `mux_4`, but for
its registers); no flag changes. -/
def mux (o x y : Nat) : List Instr :=
  loads x .r8 .r9 .r10 .r11 ++ loads y .r12 .r13 .r14 .r15 ++
  [.cmov .e .r8 (.reg .r12), .cmov .e .r9 (.reg .r13), .cmov .e .r10 (.reg .r14),
    .cmov .e .r11 (.reg .r15)] ++ store4 o

/-- The bit `t = rbx - 1` of the scalar for an iteration: `k_t` from `BITS`,
compared with `swap` (ZF set if they are equal) and stored as the new `swap`. -/
def bitCmp : List Instr :=
  [.alu .sub .rbx (.imm 1), .movzx8 .rax { base := .rdi, index := some .rbx, disp := BITS },
    .alu .cmp .rax (.mem (sc SWAP)), .store (sc SWAP) .rax]

/-- One iteration of the ladder, for the bit `t = rbx - 1`, as the
iteration of s2n-bignum's `curve25519_x25519` (the order of its operations,
and of their sharing of slots): no swap of the points, which keep RFC 7748
§5's `(x_2, z_2)` and `(x_3, z_3)` in their slots, but `mux` choosing the
point to double, `(x_3, z_3)` if `swap ≠ k_t`. The sums and differences of
both points come first (`dm = x_3 - z_3` in `B`, `sn = x_2 + z_2` in `A`,
`dn = x_2 - z_2` in `z_2`'s slot, `sm = x_3 + z_3` in `z_3`'s), then
`dmsn = sn · dm` (in `C`), the bit, the differences `d` (in `D`) and sums
`s` (in `x_2`'s slot) of the doubled point, and the rest of the addition
(`dnsm = sm · dn`, then `(dmsn ± dnsm)²`) interleaved with the doubling's
(`d²`, `s²`, `p = s² - d²`, `x_2 = s² d²` and `z_2 = p (s² + a24 p)`), so
that independent multiplications are next to each other. The sums and
differences fold once (`addCmov`, `subCmov`): `z_2`, `z_3` and the other
subtrahends are products, at most `2p`. -/
def step (F : Field) : List Instr :=
  subCmov B X3 Z3 ++ addCmov A X2 Z2 ++ subCmov Z2 X2 Z2 ++ addCmov Z3 X3 Z3 ++
  F.mul C A B ++ bitCmp ++ mux D B Z2 ++ mux X2 Z3 A ++
  F.mul X3 Z3 Z2 ++ F.sqr D D ++ subCmov Z3 C X3 ++ F.sqr X2 X2 ++ addCmov X3 C X3 ++
  F.sqr Z3 Z3 ++ subCmov C X2 D ++ F.sqr X3 X3 ++ F.a24add Z2 X2 C ++
  F.mul X2 X2 D ++ F.mul Z3 Z3 X1 ++ F.mul Z2 C Z2 ++ [.alu .cmp .rbx (.imm 3)]

/-- A doubling of `(x_2, z_2)` in place: `s = x_2 + z_2`, `d = x_2 - z_2`,
`p = s² - d²`, then `x_2 = s² d²` and `z_2 = p (s² + a24 p)`. -/
def dbl (F : Field) : List Instr :=
  addCmov A X2 Z2 ++ subCmov B X2 Z2 ++ F.sqr A A ++ F.sqr B B ++ subCmov C A B ++
  F.a24add Z2 A C ++ F.mul X2 A B ++ F.mul Z2 C Z2

/-- The iterations for bits 2, 1 and 0, which clamping clears, as
s2n-bignum's: each doubles the point the swap chooses and leaves the swap
clear, so the point is chosen once (`mux`, ZF set if `swap = 0`) and doubled
three times, and `swap` is cleared, which leaves `lastSwap` nothing to swap. -/
def tail (F : Field) : List Instr :=
  [.mov .rax (.mem (sc SWAP)), .alu .cmp .rax (.imm 0)] ++ mux X2 X3 X2 ++ mux Z2 Z3 Z2 ++
    dbl F ++ dbl F ++ dbl F ++ [.mov32 .rax (.imm 0), .store (sc SWAP) .rax]

/-- The iterations for `t` from 254 down to 3, then `tail`. -/
def ladder (F : Field) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 255)]) (.seq (.loop (.block (step F)) .ne) (.block (tail F)))

/-- `[rdi + 8 rbx + BITS + j]`: bit `j` of byte `rbx` of the scalar. -/
def bitAt (j : Nat) : MemOp :=
  { base := .rdi, index := some .rbx, scale := 8, disp := ((BITS + j : Nat) : Int) }

/-- `BITS[8i + j] = bit j of scalar[i]`, for the 32 bytes `i` (the counter
`rbx`) of the scalar at `rsi`; then the clamped bits: `BITS[0..2] = 0` and
`BITS[254] = 1` (RFC 7748 §5, `decodeScalar25519`). -/
def bits : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 0)]) (.seq (.loop (.block (
    [.movzx8 .rax { base := .rsi, index := some .rbx }] ++
    ((List.range 8).flatMap fun j =>
      [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
      [.alu .and .rdx (.imm 1),
        .store8 (bitAt j) .rdx]) ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 32)])) .ne)
    (.block [.mov32 .rax (.imm 0), .store8 (sc BITS) .rax, .store8 (sc (BITS + 1)) .rax,
      .store8 (sc (BITS + 2)) .rax, .mov32 .rax (.imm 1), .store8 (sc (BITS + 254)) .rax]))

/-! ## Encoding and decoding -/

/-- `2⁶³ - 1`. -/
def low63 : BitVec 64 := 0x7fffffffffffffff

/-- The fully reduced `[a]` (`< p`) into `r8–r11`: bit 255 folded in as 19
(`x < 2²⁵⁵ + 19`), then `x + 19 - 2²⁵⁵` selected if it is not negative. -/
def freeze (a : Nat) : List Instr :=
  [.mov .r8 (.mem (sc a)), .mov .r9 (.mem (sc (a + 8))), .mov .r10 (.mem (sc (a + 16))),
    .mov .r11 (.mem (sc (a + 24))),
    .mov .rax (.reg .r11), .shift .shr .rax 63, .movImm64 .rdx low63, .alu .and .r11 (.reg .rdx),
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax), .alu .and .rcx (.imm 19),
    .alu .add .r8 (.reg .rcx), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
    .alu .adc .r11 (.imm 0),
    .mov .r12 (.reg .r8), .alu .add .r12 (.imm 19), .mov .r13 (.reg .r9), .alu .adc .r13 (.imm 0),
    .mov .r14 (.reg .r10), .alu .adc .r14 (.imm 0), .mov .r15 (.reg .r11),
    .alu .adc .r15 (.imm 0),
    .mov .rax (.reg .r15), .shift .shr .rax 63, .alu .and .r15 (.reg .rdx),
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax)] ++
  ([(Reg.r8, Reg.r12), (.r9, .r13), (.r10, .r14), (.r11, .r15)].flatMap fun (x, y) =>
    [.alu .xor y (.reg x), .alu .and y (.reg .rcx), .alu .xor x (.reg y)])

/-! ## Inversion by divsteps

`[T1] = [Z2]^(p-2)`, the inverse of `[Z2]` (zero for zero), by Bernstein–Yang
divsteps (`Proof/Divstep/`) in ten batches of 59: from `(d, f, g) = (1, p, x)`
for the fully reduced `x` and coefficients `(a, b) = (0, 1)`, a batch runs 59
divsteps on the low words of `f` and `g` (`dsteps`), giving the matrix
`(u, v, q, r)`, then `(f, g) := (u f + v g, q f + r g) / 2⁵⁹` exactly (`fRow`)
and `(a, b) := (u a + v b, q a + r b)` modulo `p` (`aRow`). Then `f = ±1` and
`± a ≡ x⁻¹ 2⁵⁹⁰`, so the result is `a` times `2⁻⁵⁹⁰` or `p - 2⁻⁵⁹⁰` by the
sign of `f`, one multiplication of `F`.

`f` and `g` are four words in two's complement, `a` and `b` four words below
`2²⁵⁶`. The working area is `[512, 768)`: `b`, `a` (the result's slot),
`f`, `g`, then `f'` (the constant at the end), `a'`, the words `d` and the
matrix, and the divsteps' low words of `f` and `g` and a temporary (`dsT`).
The count of batches is in `rbp` (times 256), and in `r14` during the
divsteps; it is public, as the branch on it is.

A batch's 59 divsteps run in packed chunks of `15, 15, 15, 14`, as the
short Weierstrass curves' (`Impl/Weierstrass/X86_64/Inv.lean`, whose code
this repeats under the names `pk…`, since that module imports this one): with
`P = [t] mod 2^15 + 2^31` and `Q = [t + 8] mod 2^15 + 2^47` (`pkSet`), the
rows `u P + v Q` and `q P + r Q` of the chunk's matrix, modulo `2^64`, in
`r8` and the `g` row's register, are updated as `(f, g)` would be, doubled
rather than halved (`pkStep`), so that step `j`'s parity is bit `j` of the
`g` row; their bits from 31 and 47 are `u` and `v` (`q` and `r`) plus
`2^14` once `2^30 + 2^45 + 2^61` is added (`pkExt`). `~d` is in `rbx`. Each
chunk's matrix updates the low words by `mul` (`pkLow`) and multiplies the
batch's so far in `r9`–`r12` (`pkComp`).

A product `m · X` of a signed word by four words is the unsigned product
`|m| · (X ^ s)` for the mask `s` of `m`'s sign: for `f` and `g`, plus
`|m|` if `m < 0` (as `-X = ~X + 1`) less `2²⁵⁶ |m|` if `X ^ s` is negative;
for `a` and `b`, less `37 |m|` if `m < 0` (as `~X = 2²⁵⁶ - 1 - X ≡ 37 - X`).
A row's two products are summed column by column (`rowP`), each word of the
sum from two `mul`s, with `|m|` and `s` of both in registers. `a'` is the
five-word sum `Q` less `37 c`, folded as `lo + 38 Q₄ - 37 c` with the carry
of that folded in as `±38`. -/

def dsB : Nat := 512
def dsA : Nat := 544
def dsF : Nat := 576
def dsG : Nat := 608
def dsNF : Nat := 640
def dsNA : Nat := 672
def dsK : Nat := 640
def dsD : Nat := 704
def dsU : Nat := 712
def dsV : Nat := 720
def dsQ : Nat := 728
def dsR : Nat := 736

/-- The divsteps' low words of `f` and `g`, and a temporary. -/
def dsT : Nat := 744

/-- Divstep `j` of a chunk: `~d` in `rbx`, the rows in `r8` and `g`, the next
`g` row into `t`. `g << (63 - j)` is `2^63` if `g` is odd and `0` if not (its
zero flag), and adding `~d` carries if `g` is odd and `d ≥ 0` (the swap):
`t` is `g`, `g + f`, or on a swap `g - f`, `f` becomes `g` on a swap and is
doubled, and `~d` becomes `~(2 - d)` on a swap and `~(d + 2)` if not. -/
def pkStep (j : Nat) (g t : Reg) : List Instr :=
  [.mov t (.reg g), .alu .add t (.reg .r8), .mov .rdx (.reg g), .alu .sub .rdx (.reg .r8),
    .mov .rcx (.imm (-2)), .alu .sub .rcx (.reg .rbx), .mov .rbp (.reg g), .shift .shl .rbp (63 - j),
    .cmov .e t (.reg g), .alu .add .rbp (.reg .rbx), .cmov .b t (.reg .rdx), .cmov .b .r8 (.reg g),
    .cmov .b .rbx (.reg .rcx), .alu .add .r8 (.reg .r8), .alu .sub .rbx (.imm 2)]

/-- The `g` row's register before step `j`: `r13` and `rax` in turn. -/
def pkReg (j : Nat) : Reg := if j % 2 = 0 then .r13 else .rax

/-- Steps `0 … n - 1`, the `g` row then moved back to `r13`. -/
def pkSteps (n : Nat) : List Instr :=
  (List.range n).flatMap (fun j => pkStep j (pkReg j) (pkReg (j + 1))) ++
    (if n % 2 = 1 then [.mov .r13 (.reg .rax)] else [])

/-- A row's start: `r = [t] mod 2^15 + c`, through `rax`. -/
def pkSetRow (r : Reg) (t : Nat) (c : BitVec 64) : List Instr :=
  [.mov r (.mem (sc t)), .alu .and r (.imm 0x7fff), .movImm64 .rax c, .alu .add r (.reg .rax)]

/-- The rows' start: `r8 = [t] mod 2^15 + 2^31`, `r13 = [t + 8] mod 2^15 + 2^47`. -/
def pkSet (t : Nat) : List Instr := pkSetRow .r8 t (2 ^ 31) ++ pkSetRow .r13 (t + 8) (2 ^ 47)

/-- What makes the rows' fields nonnegative: `2^30` below bit 31, `2^14` at bits 31 and 47. -/
def pkExtC : BitVec 64 := 2 ^ 30 + 2 ^ 45 + 2 ^ 61

/-- The matrix `u, v, q, r` into `r8`, `rcx`, `r13`, `rbp`, from the rows in `r8`, `r13`. -/
def pkExt : List Instr :=
  [.movImm64 .rcx pkExtC, .alu .add .r8 (.reg .rcx), .alu .add .r13 (.reg .rcx),
    .mov .rcx (.reg .r8), .shift .shr .rcx 47, .alu .sub .rcx (.imm 16384),
    .shift .shl .r8 17, .shift .shr .r8 48, .alu .sub .r8 (.imm 16384),
    .mov .rbp (.reg .r13), .shift .shr .rbp 47, .alu .sub .rbp (.imm 16384),
    .shift .shl .r13 17, .shift .shr .r13 48, .alu .sub .r13 (.imm 16384)]

/-- `rax = [d] r` (the low word of the product), through `rdx`. -/
def pkLdMul (d : Nat) (r : Reg) : List Instr := [.mov .rax (.mem (sc d)), .mul r]

/-- `[e] = (rax + [d]) >> n`. -/
def pkAddShr (d n e : Nat) : List Instr :=
  [.alu .add .rax (.mem (sc d)), .shift .shr .rax n] ++ [.store (sc e) .rax]

/-- `[t] = (u [t] + v [t + 8]) >> n`, `[t + 8] = (q [t] + r [t + 8]) >> n`
(modulo `2^64`), through `rax`, `rdx` and `[t + 16]`. -/
def pkLow (n t : Nat) : List Instr :=
  pkLdMul t .r8 ++ [.store (sc (t + 16)) .rax] ++ pkLdMul (t + 8) .rcx ++ pkAddShr (t + 16) n (t + 16) ++
    pkLdMul t .r13 ++ [.store (sc t) .rax] ++ pkLdMul (t + 8) .rbp ++ pkAddShr t n (t + 8) ++
    [.mov .rax (.mem (sc (t + 16))), .store (sc t) .rax]

/-- The first chunk's matrix is the batch's so far. -/
def pkFirst : List Instr :=
  [.mov .r9 (.reg .r8), .mov .r10 (.reg .rcx), .mov .r11 (.reg .r13), .mov .r12 (.reg .rbp)]

/-- A column `(x, y)` of the batch's matrix, times the chunk's: `x = u x + v y`
and `y = q x + r y`, through `rax`, `rdx` and `[t]`. -/
def pkCol (x y : Reg) (t : Nat) : List Instr :=
  [.mov .rax (.reg .r13), .mul x, .store (sc t) .rax] ++
    [.mov .rax (.reg .r8), .mul x, .mov x (.reg .rax), .mov .rax (.reg .rcx), .mul y, .alu .add x (.reg .rax),
      .mov .rax (.reg .rbp), .mul y] ++
    [.alu .add .rax (.mem (sc t)), .mov y (.reg .rax)]

/-- The batch's matrix times the chunk's. -/
def pkComp (t : Nat) : List Instr := pkCol .r9 .r11 t ++ pkCol .r10 .r12 t

/-- A chunk of `n` steps, from the low words at `[t]`, `[t + 8]`: the low
words updated unless it is the last, and the matrix the batch's if it is
the first. -/
def pkChunk (t n : Nat) (first last : Bool) : List Instr :=
  pkSet t ++ pkSteps n ++ pkExt ++ (if last then [] else pkLow n t) ++ (if first then pkFirst else pkComp (t + 16))

/-- A batch's start: the count of batches into `r14`, the low words of `f`
and `g` into `[dsT]`, `[dsT + 8]`, and `~d` into `rbx`. -/
def dstart : List Instr :=
  [.mov .r14 (.reg .rbp), .mov .rax (.mem (sc dsF)), .store (sc dsT) .rax, .mov .rax (.mem (sc dsG)),
    .store (sc (dsT + 8)) .rax, .mov .rbx (.mem (sc dsD)), .alu .xor .rbx (.imm (-1))]

/-- 59 divsteps in chunks of `15, 15, 15, 14`; then `d` and the matrix
stored, and the count of batches back in `rbp`. -/
def dsteps : Prog isa :=
  .block (dstart ++ pkChunk dsT 15 true false ++ pkChunk dsT 15 false false ++ pkChunk dsT 15 false false ++
    pkChunk dsT 14 false true ++
    [.alu .xor .rbx (.imm (-1)), .store (sc dsD) .rbx, .store (sc dsU) .r9, .store (sc dsV) .r10,
      .store (sc dsQ) .r11, .store (sc dsR) .r12, .mov .rbp (.reg .r14)])

/-- `a = |[m]|` and `k` = the mask of `[m]`'s sign, through `rax`. -/
def absMk (m : Nat) (a k : Reg) : List Instr :=
  [.mov a (.mem (sc m)), .mov k (.reg a), .shift .shr k 63, .mov32 .rax (.imm 0), .alu .sub .rax (.reg k),
    .mov k (.reg .rax), .alu .xor a (.reg k), .alu .sub a (.reg k)]

/-- `hi:lo += a · ([x] ^ k)`, through `rax` and `rdx`. -/
def term (x : Nat) (a k lo hi : Reg) : List Instr :=
  [.mov .rax (.mem (sc x)), .alu .xor .rax (.reg k), .mul a, .alu .add lo (.reg .rax), .alu .adc hi (.reg .rdx)]

/-- Column `c` of the products `|m₁| (X ^ s₁) + |m₂| (Y ^ s₂)` (`|m₁|`, `s₁`
in `rcx`, `r14`; `|m₂|`, `s₂` in `r13`, `r15`): `hi:lo` from `hi = 0`. -/
def col (X Y c : Nat) (lo hi : Reg) : List Instr :=
  .mov32 hi (.imm 0) :: (term (X + 8 * c) .rcx .r14 lo hi ++ term (Y + 8 * c) .r13 .r15 lo hi)

/-- `cd = |[m₁]| [m₁ < 0] + |[m₂]| [m₂ < 0]` (from `|m|` and `s` of both), through `rax`. -/
def cSum (cd : Reg) : List Instr :=
  [.mov cd (.reg .rcx), .alu .and cd (.reg .r14), .mov .rax (.reg .r13), .alu .and .rax (.reg .r15),
    .alu .add cd (.reg .rax)]

/-- `r8–r12 = r8 + |m₁| ([X] ^ s₁) + |m₂| ([Y] ^ s₂)`, column by column. -/
def cols (X Y : Nat) : List Instr :=
  col X Y 0 .r8 .r9 ++ col X Y 1 .r9 .r10 ++ col X Y 2 .r10 .r11 ++ col X Y 3 .r11 .r12

/-- `|m|` and `s` of `[m₁]` and `[m₂]`, and `cd` their `cSum`: `r8` for a
row of `f` and `g`, or `rbx` with `r8 = 0` for a row of `a` and `b`; then
`r8–r12 = r8 + |[m₁]| ([X] ^ s₁) + |[m₂]| ([Y] ^ s₂)`. -/
def rowP (m₁ m₂ X Y : Nat) (cd : Reg) : List Instr :=
  absMk m₁ .rcx .r14 ++ absMk m₂ .r13 .r15 ++ cSum cd ++ (if cd = .r8 then [] else [.mov32 .r8 (.imm 0)]) ++
    cols X Y

/-- `r12 -= a` if `[x + 24] ^ k` is negative. -/
def topCorr (x : Nat) (a k : Reg) : List Instr :=
  [.mov .rax (.mem (sc (x + 24))), .alu .xor .rax (.reg k), .shift .shr .rax 63, .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .alu .and .rdx (.reg a), .alu .sub .r12 (.reg .rdx)]

/-- `[dst] = ([m₁] [f] + [m₂] [g]) / 2⁵⁹`: the five words, the tops
corrected, then shifted. -/
def fRow (m₁ m₂ dst : Nat) : List Instr :=
  rowP m₁ m₂ dsF dsG .r8 ++ topCorr dsF .rcx .r14 ++ topCorr dsG .r13 .r15 ++
  ([(Reg.r8, Reg.r9, 0), (.r9, .r10, 8), (.r10, .r11, 16), (.r11, .r12, 24)].flatMap fun (lo, hi, d) =>
    [.mov .rax (.reg lo), .shift .shr .rax 59, .mov .rdx (.reg hi), .shift .shl .rdx 5,
      .alu .add .rax (.reg .rdx), .store (sc (dst + d)) .rax])

/-- `r8–r11 = r8–r12 - 37 rbx` modulo `p`, below `2²⁵⁶`: `lo + w` for
`w = 38 r12 - 37 rbx` (two words, signed), then its carry as `±38`. -/
def foldP : List Instr :=
  [.mov32 .rax (.imm 38), .mul .r12, .mov .r13 (.reg .rax), .mov .r14 (.reg .rdx),
    .mov32 .rax (.imm 37), .mul .rbx, .alu .sub .r13 (.reg .rax), .alu .sbb .r14 (.reg .rdx),
    .mov .r15 (.reg .r14), .shift .shr .r15 63, .mov32 .rax (.imm 0), .alu .sub .rax (.reg .r15),
    .alu .add .r8 (.reg .r13), .alu .adc .r9 (.reg .r14), .alu .adc .r10 (.reg .rax), .alu .adc .r11 (.reg .rax),
    .alu .sbb .rdx (.reg .rdx), .alu .and .rdx (.imm 38), .alu .and .rax (.imm 38), .alu .sub .rdx (.reg .rax),
    .mov .r15 (.reg .rdx), .shift .shr .r15 63, .mov32 .rax (.imm 0), .alu .sub .rax (.reg .r15),
    .alu .add .r8 (.reg .rdx), .alu .adc .r9 (.reg .rax), .alu .adc .r10 (.reg .rax), .alu .adc .r11 (.reg .rax)]

/-- `[dst] = [m₁] [a] + [m₂] [b]` modulo `p`, below `2²⁵⁶`. -/
def aRow (m₁ m₂ dst : Nat) : List Instr :=
  rowP m₁ m₂ dsA dsB .rbx ++ foldP ++ store4 dst

/-- `[dst] = [src]` (four words), through `r8–r11`. -/
def copy4 (dst src : Nat) : List Instr := loads src .r8 .r9 .r10 .r11 ++ store4 dst

/-- The count of batches (times 256, in `rbp`) less one, its zero flag for the loop. -/
def batchEnd : List Instr := [.alu .sub .rbp (.imm 256)]

/-- A batch. -/
def dbatch : Prog isa :=
  .seq dsteps (.block (fRow dsU dsV dsNF ++ fRow dsQ dsR dsG ++ copy4 dsF dsNF ++
    aRow dsU dsV dsNA ++ aRow dsQ dsR dsB ++ copy4 dsA dsNA ++ batchEnd))

/-- `2⁻⁵⁹⁰ mod p`. -/
def kInv : Nat := 0x276508b2417706156c6c893805ac5242a8c68f3f1d132595a0f99e2375022099

/-- `p - 2⁻⁵⁹⁰ mod p`. -/
def kInvNeg : Nat := 0x589af74dbe88f9ea939376c7fa53adbd573970c0e2ecda6a5f0661dc8afddf54

/-- `p`. -/
def pNat : Nat := 2 ^ 255 - 19

/-- The start: `g = x` fully reduced, `f = p`, `a = 0`, `b = 1`, `d = 1`, and
ten batches. -/
def dinit : List Instr :=
  freeze Z2 ++ store4 dsG ++
  ((List.range 4).flatMap fun i =>
    [.movImm64 .rax (BitVec.ofNat 64 (pNat >>> (64 * i))), .store (sc (dsF + 8 * i)) .rax]) ++
  [.mov32 .rax (.imm 0)] ++ stores dsA .rax .rax .rax .rax ++ stores dsB .rax .rax .rax .rax ++
  [.mov32 .rax (.imm 1), .store (sc dsB) .rax, .store (sc dsD) .rax, .mov32 .rbp (.imm 2560)]

/-- `[dsK] = 2⁻⁵⁹⁰` if `f ≥ 0`, else `p - 2⁻⁵⁹⁰`. -/
def dsel : List Instr :=
  [.mov .rdx (.mem (sc (dsF + 24))), .shift .shr .rdx 63, .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)] ++
  ((List.range 4).flatMap fun i =>
    [.movImm64 .rax (BitVec.ofNat 64 (kInv >>> (64 * i))), .movImm64 .rdx (BitVec.ofNat 64 (kInvNeg >>> (64 * i))),
      .alu .xor .rdx (.reg .rax), .alu .and .rdx (.reg .rcx), .alu .xor .rax (.reg .rdx),
      .store (sc (dsK + 8 * i)) .rax])

/-- `[T1] = [Z2]^(p-2)`, by divsteps. -/
def invertDS (F : Field) : Prog isa :=
  .seq (.block dinit) (.seq (.loop dbatch .ne) (.block (dsel ++ F.mul T1 T1 dsK)))

/-- The callee-saved registers the inversion writes, into `xmm0`–`xmm5`. -/
def invSaves : List Instr :=
  [.xop (.movq .xmm0 .rbx), .xop (.movq .xmm1 .rbp), .xop (.movq .xmm2 .r12),
    .xop (.movq .xmm3 .r13), .xop (.movq .xmm4 .r14), .xop (.movq .xmm5 .r15)]

/-- The callee-saved registers back from `xmm0`–`xmm5`. -/
def invRestores : List Instr :=
  [.movqR .rbx .xmm0, .movqR .rbp .xmm1, .movqR .r12 .xmm2, .movqR .r13 .xmm3, .movqR .r14 .xmm4,
    .movqR .r15 .xmm5]

/-- `vg_gf25519_r64_invert(ws = rdi)`: `[T1] = [Z2]^(p-2)` by divsteps, with the
baseline multiplication, the callee-saved registers kept in `xmm0`–`xmm5`. -/
def invertFn : Prog isa := .seq (.block invSaves) (.seq (invertDS baseline) (.block invRestores))

/-- A call of `vg_gf25519_r64_invert`, which every inversion of the x86-64 code
is (`ws` in `rdi`). -/
def invertCall : Prog isa := .call "vg_gf25519_r64_invert" invertFn

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 0), (.rbp, 8), (.r12, 16), (.r13, 24), (.r14, 32), (.r15, 40)]

/-- Saves them (with the working space in `rcx`). -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .rcx d) r

def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (sc d))

/-- The u-coordinate at `rdx`, its top bit masked, into `r8–r11`. -/
def loadU : List Instr :=
  [.mov .r8 (.mem (at_ .rdx 0)), .mov .r9 (.mem (at_ .rdx 8)), .mov .r10 (.mem (at_ .rdx 16)),
    .mov .r11 (.mem (at_ .rdx 24)), .movImm64 .rax low63, .alu .and .r11 (.reg .rax)]

/-- Reads the arguments (with the working space in `rcx`): `u` with its top
bit masked into `X1` and `X3`; then `out` into `r12`, the working space into
`rdi`, and `x2 = 1`, `z2 = 0`, `z3 = 1`, `swap = 0`. The scalar stays at
`rsi` for `bits`. -/
def setup : List Instr :=
  loadU ++ save ++ [.mov .r12 (.reg .rdi), .mov .rdi (.reg .rcx)] ++ store4 X1 ++ store4 X3 ++
    [.mov32 .rax (.imm 0), .mov32 .rdx (.imm 1)] ++ stores X2 .rdx .rax .rax .rax ++
    stores Z2 .rax .rax .rax .rax ++ stores Z3 .rdx .rax .rax .rax ++ [.store (sc SWAP) .rax]

/-- `x2 · z2^(p-2)`, reduced fully, to `out`, and the saved registers
restored (before the stores, which do not touch the working space). -/
def finish (F : Field) : List Instr :=
  F.mul X2 X2 T1 ++ freeze X2 ++ restore ++
  [.store (at_ .rsi 0) .r8, .store (at_ .rsi 8) .r9, .store (at_ .rsi 16) .r10,
    .store (at_ .rsi 24) .r11]

/-- The swap after the loop. -/
def lastSwap : List Instr :=
  [.mov .rdx (.mem (sc SWAP)), .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)] ++
  cswap X2 X3 ++ cswap Z2 Z3

/-- X25519 with the ladder `lad` (which leaves the ladder's final state in the
working space as `ladder` does) and the field multiplications `F` for the
inversion. -/
def x25519Of (F : Field) (lad : Prog isa) : Prog isa :=
  .seq (.block setup) <| .seq bits <| .seq (.block [.mov .rsi (.reg .r12)]) <| .seq lad <|
    .seq (.block lastSwap) <| .seq invertCall (.block (finish F))

/-- X25519 with the field multiplications `F`. -/
def x25519With (F : Field) : Prog isa := x25519Of F (ladder F)

def x25519 : Prog isa := x25519With baseline

end VG.Impl.X25519.X86_64
