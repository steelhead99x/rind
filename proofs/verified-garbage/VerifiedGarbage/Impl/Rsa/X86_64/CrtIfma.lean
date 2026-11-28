module

public import VerifiedGarbage.Impl.Rsa.X86_64.Crt

/-!
# RSA with the CRT private key on x86-64, with AVX512_IFMA, for any size

`vg_rsa_private_crt_ifma` and `vg_rsa_private_crt_ifma512`:
`vg_rsa_private_crt_adx`'s code, but for a
modulus of `2 W` words and primes of `W` words each, whose two
exponentiations (modulo `p` and modulo `q`) run at once, in radix `2⁵²`,
with AVX512_IFMA's `vpmadd52luq` and `vpmadd52huq`, with numbers of `4 R`
limbs in `R` rows of four (`Lay`): `R = 5`, `W = 16` for 2048-bit keys,
`R = 8`, `W = 24` for 3072-bit keys, `R = 10`, `W = 32` for 4096-bit keys.
Each prime's rows are 256-bit registers: the
two accumulators take `2 R` registers, with the two broadcast limbs, the
two `u`, a zero and a temporary: `2 R + 6` of the thirty-two, named through
`VReg` and the `EVEX.256` instructions of `TCB/X86_64/Evex.lean`, which
reach `ymm16`–`ymm31`.

The two functions differ for 2048-bit keys alone, where
`vg_rsa_private_crt_ifma512` has `R = 6` (`lay2048z`): the two primes' rows
are the halves of 512-bit registers, and the exponentiations multiply
modulo a multiple of each prime that is `-1` modulo `2¹⁰⁴` (`ammCoreZ`, and
`zPre` and `zPost` around the exponentiations), which takes about 1.3 times
the multiplications of 52-bit limbs and no multiplication for a quotient
digit. It is the faster where two 512-bit multipliers run them (Intel's
Xeons from Sapphire Rapids on), and the slower where a 512-bit
multiplication is two of 256 bits (AMD's Zen 4), so the functions that
call it are chosen only with AVX512_FP16 (`CrtImpl.extra`), which the first
have and the second do not.

* A number below `2^(208 R)` is `4 R` limbs below `2⁵²`, limb `j` in
  quadword `j / R` of the 32-byte vector `j % R` (`32 R` bytes): the stride
  layout.
* `amm`: two almost-Montgomery multiplications at once, `a b 2^(-52 S)`
  modulo `p` and modulo `q`, in `S ≤ 4 R` steps (30 of the 32 limbs for
  3072-bit keys, whose primes need no more): for each limb `b_i`
  of the second operand, the low halves of `a b_i` into the accumulator and
  the high halves of those that stay in their lane, `u = acc₀ k₀ mod 2⁵²`,
  the low halves of `u m`, the carry of limb 0 into limb 1 (`vpsrlq` and
  `vmovq`, which keeps the low quadword), the accumulator shifted down a
  limb (a change of the registers' roles and `valignq` of the register of
  limb 0 with the zero register, which moves its lanes down one and the
  zero in), and the high halves of `u m` and of the rest of `a b_i`.
* The bases and 1 in Montgomery form (`R_I = 2^(52 S)`) from those of
  `vg_rsa_private_crt` (`R_X = 2^(64 W)`) by a multiplication by
  `2^(104 S - 64 W) mod X` (`R_X` doubled `104 S - 128 W` times); a table
  of the `2^w` powers; `w` squares and a multiplication by the masked
  selection of an entry per window of `w` bits (4 for 2048-bit keys, 5
  otherwise), the exponents padded with zero bytes at the top to whole
  groups of `w` bytes and recoded into digits of `w` bits, a byte each,
  from the first digit with a bit of the exponent; then a multiplication
  by 1, which leaves the result out of Montgomery form, reduced in 64-bit
  words.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.CrtIfma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
  VG.Impl.Rsa.X86_64.Crt

/-- The offset of the modulus in a prime's region. -/
def oM : Nat := 0

/-- The sizes: `R` registers per number, primes of `W` words, `S` steps
of a multiplication (`S ≤ 4 R`): the Montgomery radix is `2^(52 S)`;
windows of `w` bits; and `nl` lanes, numbers multiplied side by side, each
in its own region `D` bytes after the previous one (the two primes). -/
structure Lay where
  R : Nat
  W : Nat
  S : Nat
  w : Nat
  nl : Nat
  /-- Whether the multiplications of the exponentiation are modulo a
  multiple of the prime that is `-1` modulo `2¹⁰⁴` (`ammCoreZ`). -/
  z : Bool
  deriving DecidableEq, Repr

namespace Lay

variable (l : Lay)

/-- The limbs of a number. -/
def L : Nat := 4 * l.R
/-- The bytes of a number. -/
def NB : Nat := 32 * l.R
/-- The bytes of the exponent, a prime's. -/
def E : Nat := 8 * l.W
/-- The entries of the table. -/
def T : Nat := 2 ^ l.w
/-- The bytes of the padded exponent: `E` and the fewest zero bytes before
it that make it a whole number of groups of `w` bytes. -/
def P : Nat := l.E + (l.w - l.E % l.w) % l.w
/-- The digits of `w` bits of the padded exponent, 8 per group. -/
def ND : Nat := 8 * (l.P / l.w)
/-- The first digit with a bit of the exponent (those before are zero). -/
def k0 : Nat := 8 * (l.P - l.E) / l.w
/-- The bytes of the padded exponent and of its digits (none with windows of
4 bits, whose digits are the exponent's nibbles), each a whole number of 32
bytes. -/
def XE : Nat := (l.P + 31) / 32 * 32 + (if l.w = 4 then 0 else (l.ND + 31) / 32 * 32)

/-- The bytes of the two numbers only `ammCoreZ`'s layouts have. -/
def zx : Nat := if l.z then 2 * l.NB else 0

/-! In a prime's region: the modulus, `k₀` in each quadword, `Y`, the base
`X`, the selected entry, the table, the padded exponent, its digits (a byte
each), `2^(104 S - 64 W) mod X`, the digit being read, the last multiplier;
and with `ammCoreZ` the multiple of the prime plus one and the last
multiplier's copy. -/
def oK0 : Nat := l.NB
def oY : Nat := l.NB + 32
def oX : Nat := l.oY + l.NB
def oS : Nat := l.oX + l.NB
def oTab : Nat := l.oS + l.NB
def oE : Nat := l.oTab + l.T * l.NB
def oD : Nat := l.oE + (l.P + 31) / 32 * 32
def oK1 : Nat := l.oE + l.XE
def oV : Nat := l.oK1 + l.NB
/-- The last multiplier: 1 for `q`, `R mod p` for `p`. -/
def oFin : Nat := l.oV + 32
def oMs : Nat := l.oFin + l.NB
def oF2 : Nat := l.oFin + 2 * l.NB
/-- `q`'s region from `p`'s. -/
def D : Nat := l.oFin + l.NB + l.zx
/-- The 8 bytes after the regions, which once held the caller's MXCSR and
`0x1FBF` (the code no longer loads MXCSR: `withVzu`), and which the
layouts built on this one keep. -/
def oMx : Nat := l.nl * l.D
/-- The doublings of `R_X mod X` that make `2^(104 S - 64 W) mod X`; with
`ammCoreZ`, those after which a multiplication by `2^(52 L - 1)` leaves
`2^(104 S - cv)`. -/
def dbls : Nat := if l.z then 208 * l.S + 2 - 104 * l.L - 128 * l.W else 104 * l.S - 128 * l.W
/-- The base and 1 come to the exponentiation times `2^cv`: `R_X`, and with
`ammCoreZ` a multiplication by `2^(52 L - 1)` more. -/
def cv : Nat := if l.z then 52 * l.L - 1 + 64 * l.W - 52 * l.S else 64 * l.W
/-- With `ammCoreZ`: the limb of `2^(52 zE)`, whose square over `2^(52 S)`
is `2^(-104)`. -/
def zE : Nat := (l.S - 2) / 2

/-- The quadword of limb `j` in the stride layout. -/
def off (j : Nat) : Nat := 32 * (j % l.R) + 8 * (j / l.R)

end Lay

/-- 2048-bit keys: primes of 16 words, numbers of 20 limbs, windows of 4
bits. -/
def lay2048 : Lay := ⟨5, 16, 20, 4, 2, false⟩
/-- 2048-bit keys with `ammCoreZ`: primes of 16 words, numbers of 24 limbs,
of which 22 hold the multiple of the prime and a multiplication's 22 steps,
windows of 4 bits. -/
def lay2048z : Lay := ⟨6, 16, 22, 4, 2, true⟩
/-- 3072-bit keys: primes of 24 words, numbers of 32 limbs, of which 30
hold the primes' 1536 bits and a multiplication's 30 steps, windows of 5
bits. -/
def lay3072 : Lay := ⟨8, 24, 30, 5, 2, false⟩
/-- 4096-bit keys: primes of 32 words, numbers of 40 limbs, windows of 5
bits. -/
def lay4096 : Lay := ⟨10, 32, 40, 5, 2, false⟩

/-- In the prime workspaces: the base of the IFMA area, and a counter. -/
def sIfma : Nat := sFn 13
def sCtr : Nat := sFn 14

def at_ (r : Reg) (d : Nat) : MemOp := { base := r, disp := d }

def mask52 : BitVec 64 := BitVec.ofNat 64 (2 ^ 52 - 1)

/-! ## Registers -/

/-- Vector register `n` (of 32). -/
def vreg (n : Nat) : VReg :=
  match n with
  | 0 => .lo .xmm0 | 1 => .lo .xmm1 | 2 => .lo .xmm2 | 3 => .lo .xmm3
  | 4 => .lo .xmm4 | 5 => .lo .xmm5 | 6 => .lo .xmm6 | 7 => .lo .xmm7
  | 8 => .lo .xmm8 | 9 => .lo .xmm9 | 10 => .lo .xmm10 | 11 => .lo .xmm11
  | 12 => .lo .xmm12 | 13 => .lo .xmm13 | 14 => .lo .xmm14 | 15 => .lo .xmm15
  | 16 => .hi .xmm16 | 17 => .hi .xmm17 | 18 => .hi .xmm18 | 19 => .hi .xmm19
  | 20 => .hi .xmm20 | 21 => .hi .xmm21 | 22 => .hi .xmm22 | 23 => .hi .xmm23
  | 24 => .hi .xmm24 | 25 => .hi .xmm25 | 26 => .hi .xmm26 | 27 => .hi .xmm27
  | 28 => .hi .xmm28 | 29 => .hi .xmm29 | 30 => .hi .xmm30 | _ => .hi .xmm31

variable (l : Lay)

/-- The register of limb role `k` of lane `p` at step `i` of a block; then
each lane's `b` and `u`, the zero register and a temporary. -/
def acc (p k i : Nat) : VReg := vreg (l.R * p + (k + i) % l.R)
def bReg (p : Nat) : VReg := vreg (l.nl * l.R + p)
def uReg (p : Nat) : VReg := vreg (l.nl * l.R + l.nl + p)
def zReg : VReg := vreg (l.nl * l.R + 2 * l.nl)
def tReg : VReg := vreg (l.nl * l.R + 2 * l.nl + 1)

/-! ## The multiplication -/

/-- Step `i` of a block, for each lane (`p` then `q`) in turn at each stage:
`r8` the first operand, `r9` the second plus 8 per block, `r10` the region
(the modulus and `k₀`). Ordered so that the chain through `u` and the
shift starts first: the low halves into roles 0 and 1, `u`, what role 1
needs before the shift, the shift, then the rest limb by limb. -/
def ammStep (i : Nat) : List Instr :=
  let ps := List.range l.nl
  let D := l.D
  let loA (p k : Nat) : Instr := .evMadd52Load false (acc l p k i) (bReg l p) (at_ .r8 (D * p + 32 * k))
  let hiA (p k : Nat) : Instr := .evMadd52Load true (acc l p (k + 1) i) (bReg l p) (at_ .r8 (D * p + 32 * k))
  let loM (p k : Nat) : Instr := .evMadd52Load false (acc l p k i) (uReg l p) (at_ .r10 (D * p + oM + 32 * k))
  let hiM (p k : Nat) : Instr := .evMadd52Load true (acc l p k (i + 1)) (uReg l p) (at_ .r10 (D * p + oM + 32 * k))
  ps.flatMap (fun p => [.mov .rax (.mem (at_ .r9 (D * p + 32 * i))), .eop (.vmovq (bReg l p) .rax),
    .eop (.vpbroadcastq (bReg l p) (bReg l p))]) ++
  ps.flatMap (fun p => [loA p 0, loA p 1]) ++
  ps.flatMap (fun p => [.eop (.bin .vpxorq (tReg l) (tReg l) (tReg l)),
    .evMadd52Load false (tReg l) (acc l p 0 i) (at_ .r10 (D * p + l.oK0)),
    .eop (.vpbroadcastq (uReg l p) (tReg l))]) ++
  ps.flatMap (fun p => [hiA p 0, loM p 0, loM p 1]) ++
  ps.flatMap (fun p => [.eop (.shift .vpsrlq (tReg l) (acc l p 0 i) 52), .eop (.vmovqx (tReg l) (tReg l)),
    .eop (.bin .vpaddq (acc l p 1 i) (acc l p 1 i) (tReg l)),
    .eop (.valignq (acc l p 0 i) (zReg l) (acc l p 0 i) 1)]) ++
  ps.flatMap (fun p => [hiM p 0]) ++
  ps.flatMap (fun p => (List.range (l.R - 2)).flatMap fun j =>
    [loA p (j + 2), hiA p (j + 1), loM p (j + 2), hiM p (j + 1)]) ++
  ps.flatMap (fun p => [hiA p (l.R - 1), hiM p (l.R - 1)])

/-- A block: `R` steps, then the next block's limbs of the second operand
and the count of blocks. -/
def ammBlock : List Instr :=
  (List.range l.R).flatMap (ammStep l) ++ ([.alu .add .r9 (.imm 8), .alu .sub .rcx (.imm 1)] : List Instr)

/-- Lane `p`'s carry (`rdx`, then `rsi`) and its temporary (`rax`, then `rcx`). -/
def cReg (p : Nat) : Reg := if p = 0 then .rdx else .rsi
def cTmp (p : Nat) : Reg := if p = 0 then .rax else .rcx

/-- Limb `j` of lane `p`'s carry chain. -/
def carryStep (j p : Nat) : List Instr :=
  [.alu .add (cReg p) (.mem (at_ .r11 (l.D * p + l.off j))), .mov (cTmp p) (.reg (cReg p)),
    .alu .and (cTmp p) (.reg .r12), .store (at_ .r11 (l.D * p + l.off j)) (cTmp p), .shift .shr (cReg p) 52]

/-- The accumulators' limbs, carried in order into limbs below `2⁵²`, at
`r11` (and `r11 + D`), the lanes' chains interleaved (carries in `rdx` and
`rsi`); `r12` holds `2⁵² - 1`. -/
def carryOut : List Instr :=
  (List.range l.nl).map (fun p => .mov32 (cReg p) (.imm 0)) ++
    (List.range l.L).flatMap fun j => (List.range l.nl).flatMap (carryStep l j)

/-! ### The multiplication with a look-ahead of `u`

`ammCoreU`: `ammCore` with its `S` steps unrolled and the next step's `u`
computed from limb 1 of the accumulator alone, before the rest of the row,
so that the chain from one `u` to the next is a multiplication, the carry,
the additions into limb 1, the multiplication by `k₀` and the broadcast,
and the row's other products run beside it. The limbs of the second
operand and the `u`s alternate between two registers of each lane (`par`,
the step's parity), so no step copies one. -/

/-- Lane `p`'s registers after the roles: the limb of the second operand and
`u` of a step of parity `par`, a temporary, the two products of `u` for limb
1, and the next `lo(a₀ b)`; then the zero register. -/
def ubReg (p par : Nat) : VReg := vreg (l.nl * l.R + 8 * p + par)
def uuReg (p par : Nat) : VReg := vreg (l.nl * l.R + 8 * p + 2 + par)
def utReg (p : Nat) : VReg := vreg (l.nl * l.R + 8 * p + 4)
def um1Reg (p : Nat) : VReg := vreg (l.nl * l.R + 8 * p + 5)
def um2Reg (p : Nat) : VReg := vreg (l.nl * l.R + 8 * p + 6)
def upnReg (p : Nat) : VReg := vreg (l.nl * l.R + 8 * p + 7)
def uzReg : VReg := vreg (l.nl * l.R + 8 * l.nl)

/-- Step `i` of lane `p`: `b_i` in `ubReg p (i % 2)`, `u_i` in
`uuReg p (i % 2)`, and role 0 already holding `lo(a₀ b_i)`; it leaves
`b_(i+1)`, `u_(i+1)` and role 0's `lo(a₀ b_(i+1))` for the next, unless `i`
is the last step. -/
def ammStepU (p i : Nat) : List Instr :=
  let D := l.D
  let par := i % 2
  let nxt := (i + 1) % 2
  let B := ubReg l p par
  let U := uuReg l p par
  let z (r : VReg) : Instr := .eop (.bin .vpxorq r r r)
  let loA (k : Nat) : Instr := .evMadd52Load false (acc l p k i) B (at_ .r8 (D * p + 32 * k))
  let hiA (k : Nat) : Instr := .evMadd52Load true (acc l p (k + 1) i) B (at_ .r8 (D * p + 32 * k))
  let loM (k : Nat) : Instr := .evMadd52Load false (acc l p k i) U (at_ .r10 (D * p + oM + 32 * k))
  let hiM (k : Nat) : Instr := .evMadd52Load true (acc l p k (i + 1)) U (at_ .r10 (D * p + oM + 32 * k))
  let last := l.S ≤ i + 1
  [loM 0, z (um1Reg l p), .evMadd52Load false (um1Reg l p) U (at_ .r10 (D * p + oM + 32)),
    z (um2Reg l p), .evMadd52Load true (um2Reg l p) U (at_ .r10 (D * p + oM)),
    loA 1, hiA 0] ++
  (if last then [] else
    [.mov .rax (.mem (at_ .r9 (D * p + l.off (i + 1)))), .eop (.vmovq (ubReg l p nxt) .rax),
      .eop (.vpbroadcastq (ubReg l p nxt) (ubReg l p nxt)), z (upnReg l p),
      .evMadd52Load false (upnReg l p) (ubReg l p nxt) (at_ .r8 (D * p)),
      .eop (.bin .vpaddq (acc l p 1 i) (acc l p 1 i) (upnReg l p))]) ++
  [.eop (.bin .vpaddq (acc l p 1 i) (acc l p 1 i) (um1Reg l p)),
    .eop (.bin .vpaddq (acc l p 1 i) (acc l p 1 i) (um2Reg l p)),
    .eop (.shift .vpsrlq (utReg l p) (acc l p 0 i) 52), .eop (.vmovqx (utReg l p) (utReg l p)),
    .eop (.bin .vpaddq (acc l p 1 i) (acc l p 1 i) (utReg l p))] ++
  (if last then [] else
    [z (utReg l p), .evMadd52Load false (utReg l p) (acc l p 1 i) (at_ .r10 (D * p + l.oK0)),
      .eop (.vpbroadcastq (uuReg l p nxt) (utReg l p))]) ++
  [.eop (.valignq (acc l p 0 i) (uzReg l) (acc l p 0 i) 1)] ++
  (List.range (l.R - 2)).flatMap (fun j => [loA (j + 2), hiA (j + 1), loM (j + 2), hiM (j + 1)]) ++
  [hiA (l.R - 1), hiM (l.R - 1)]

/-- The start: `b₀`, role 0's `lo(a₀ b₀)` and `u₀` from it. -/
def ammStartU (p : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .r9 (l.D * p))), .eop (.vmovq (ubReg l p 0) .rax),
    .eop (.vpbroadcastq (ubReg l p 0) (ubReg l p 0)),
    .evMadd52Load false (acc l p 0 0) (ubReg l p 0) (at_ .r8 (l.D * p)),
    .eop (.bin .vpxorq (utReg l p) (utReg l p) (utReg l p)),
    .evMadd52Load false (utReg l p) (acc l p 0 0) (at_ .r10 (l.D * p + l.oK0)),
    .eop (.vpbroadcastq (uuReg l p 0) (utReg l p))]

/-- `ammCore` with the look-ahead, its `S` steps unrolled. -/
def ammCoreU : Prog isa :=
  .block (([.mov .r10 (.reg .rbx)] : List Instr) ++
    (List.range (l.nl * l.R)).map (fun r => .eop (.bin .vpxorq (vreg r) (vreg r) (vreg r))) ++
    [.eop (.bin .vpxorq (uzReg l) (uzReg l) (uzReg l))] ++
    (List.range l.nl).flatMap (ammStartU l) ++
    (List.range l.S).flatMap (fun i => (List.range l.nl).flatMap fun p => ammStepU l p i) ++
    ((List.range l.nl).flatMap fun p => (List.range l.R).map fun k =>
      .evStore (at_ .r11 (l.D * p + 32 * k)) (acc l p k (l.S % l.R))) ++
    ([.movImm64 .r12 mask52] : List Instr) ++ carryOut l)

/-- `[r11] := [r8] [r9] 2^(-52 S)` modulo each prime, almost (`rbx` the
area): `S / R` blocks, then the first `S % R` steps of another, which leave
role `k` in the register of `k + S % R`. -/
def ammCore : Prog isa :=
  .seq (.block (([.mov .r10 (.reg .rbx), .mov32 .rcx (.imm (BitVec.ofNat 32 (l.S / l.R)))] : List Instr) ++
      (List.range (l.nl * l.R + 2 * l.nl + 1)).map fun r => .eop (.bin .vpxorq (vreg r) (vreg r) (vreg r))))
    (.seq (.loop (.block (ammBlock l)) .ne)
      (.block ((List.range (l.S % l.R)).flatMap (ammStep l) ++ ((List.range l.nl).flatMap fun p => (List.range l.R).map fun k =>
          .evStore (at_ .r11 (l.D * p + 32 * k)) (acc l p k (l.S % l.R))) ++
        ([.movImm64 .r12 mask52] : List Instr) ++ carryOut l)))

/-! ### The multiplication modulo a number that is `-1` modulo `2¹⁰⁴`

`ammCoreZ`: both lanes at once, lane `p` in quadwords `4 p` to `4 p + 3`
of 512-bit registers (`TCB/X86_64/Evex.lean`'s `E5Op`), modulo the number
`X = 2¹⁰⁴ m - 1` for the `m` at `oMs`, of at most `4 R - 2` limbs: `X + 1`
is `m` two limbs up, with limbs 0 and 1 zero. So the digit `u` of a step is
limb 0 of the accumulator, with no multiplication by `k₀`, and none of
`u`'s products reaches limbs 0 and 1: the chain from one `u` to the next is
the addition of the two halves of limb 0 (`zU 0` and `zB 0`), and the
step's products run beside it.

The accumulator is two sets of `R` registers, the products of the second
operand's limbs with the first operand (`zB`) and those of the `u`s with
`X + 1` (`zU`), which change roles as `ammCore`'s do; the operands' rows
stay in registers (`zA`, `zM`). A step adds the two registers of role 0,
takes `u` from the sum's quadword 0 of each lane, carries each of its
quadwords into role 1 (`zC`), and moves its other three quadwords down one
(`vpermq`, their low 52 bits kept by `zK`) into the `zU` register that
becomes the top role, with the products of `u` and of the step before's
`u` that belong there: those of limbs `R c` and `R c + 1` of `X + 1`, from
`zM R` and `zM (R + 1)`, rows 0 and 1 moved down a quadword, which are
`m`'s last two rows (and rows 0 and 1 are those moved up a quadword, their
last quadword, zero, first). After the last step, the last `u`'s products
of rows 0 and 1 are still to add (`zFin`). The first product of the next limb of the second operand goes
into role 1 a step early, as `ammCoreU`'s. -/

/-- The registers: role `k` of the two sets at step `i`, the limb of the
second operand and `u` of a step of parity `par`, the carries, the first
operand's row `k`, row `k` of `X + 1` (`1 ≤ k < R`; `R` and `R + 1` are
rows 0 and 1 moved down a quadword), the mask of the three low quadwords'
52 bits, and a temporary. -/
def zB (k i : Nat) : VReg := vreg ((k + i) % l.R)
def zU (k i : Nat) : VReg := vreg (l.R + (k + i) % l.R)
def zBq (par : Nat) : VReg := vreg (2 * l.R + par)
def zUq (par : Nat) : VReg := vreg (2 * l.R + 2 + par)
def zC : VReg := vreg (2 * l.R + 4)
def zA (k : Nat) : VReg := vreg (2 * l.R + 5 + k)
def zM (k : Nat) : VReg := vreg (3 * l.R + 4 + k)
def zK : VReg := vreg (4 * l.R + 6)
def zT : VReg := vreg (4 * l.R + 7)

/-- `r := ` the rows at `[b + d]` and `[b + D + d]`, a lane each. -/
def zLoad (r : VReg) (b : Reg) (d : Nat) : List Instr :=
  [.evLoad r (at_ b d), .e5InsertLoad r r (at_ b (l.D + d)) 1]

/-- `zBq par := ` the limbs at `[r9 + d]` and `[r9 + D + d]`, in every
quadword of their lanes. -/
def zBLoad (par d : Nat) : List Instr :=
  [.evBroadcastLoad (zBq l par) (at_ .r9 d), .evBroadcastLoad (zT l) (at_ .r9 (l.D + d)),
    .e5op (.vinserti64x4 (zBq l par) (zBq l par) (zT l) 1)]

/-- Step `i` of a block (`last`: no limb of the second operand follows). -/
def zStep (i : Nat) (last : Bool) : List Instr :=
  let par := i % 2
  let nxt := (i + 1) % 2
  let B := zBq l par
  let U := zUq l par
  let Up := zUq l nxt
  let B0 := zB l 0 i
  let B1 := zB l 1 i
  let U0 := zU l 0 i
  let lo (d x y : VReg) : Instr := .e5op (.vpmadd52 false d x y)
  let hi (d x y : VReg) : Instr := .e5op (.vpmadd52 true d x y)
  ([.e5op (.bin .vpaddq U0 U0 B0), .e5op (.vpermq U U0 0), .e5op (.shift .vpsrlq (zC l) U0 52)] : List Instr) ++
  (if last then [] else zBLoad l nxt (l.off (i + 1)) ++ [lo B1 (zBq l nxt) (zA l 0)]) ++
  [lo B1 B (zA l 1), hi B1 B (zA l 0), .e5op (.bin .vpaddq B1 B1 (zC l)),
    .e5op (.vpermq U0 U0 0xF9), .e5op (.bin .vpandq U0 U0 (zK l)), .e5op (.bin .vpxorq B0 B0 B0),
    hi U0 Up (zM l l.R), lo U0 Up (zM l (l.R + 1)), lo U0 U (zM l l.R)] ++
  (List.range (l.R - 2)).flatMap (fun j =>
    [lo (zB l (j + 2) i) B (zA l (j + 2)), hi (zB l (j + 2) i) B (zA l (j + 1)),
      lo (zU l (j + 2) i) U (zM l (j + 2)), hi (zU l (j + 2) i) U (zM l (j + 1))]) ++
  [hi B0 B (zA l (l.R - 1)), hi U0 U (zM l (l.R - 1))]

/-- The start: the mask, the operands' rows, the accumulators and the `u`
before the first zeroed, the second operand's first limb and its first
product. -/
def zStart : List Instr :=
  ([.mov .r10 (.reg .rbx), .mov32 .rcx (.imm (BitVec.ofNat 32 (l.S / l.R))), .movImm64 .rax mask52,
    .eop (.vmovq (zK l) .rax), .e5op (.vpermq (zK l) (zK l) 0x40),
    .e5op (.vinserti64x4 (zK l) (zK l) (zK l) 1)] : List Instr) ++
  (List.range l.R).flatMap (fun k => zLoad l (zA l k) .r8 (32 * k)) ++
  (List.range l.R).flatMap (fun k => zLoad l (zM l (k + 2)) .r10 (l.oMs + 32 * k)) ++
  [.e5op (.vpermq (zM l 1) (zM l (l.R + 1)) 0x93)] ++
  (List.range (2 * l.R)).map (fun r => .e5op (.bin .vpxorq (vreg r) (vreg r) (vreg r))) ++
  [.e5op (.bin .vpxorq (zUq l 1) (zUq l 1) (zUq l 1))] ++
  zBLoad l 0 0 ++ [.e5op (.vpmadd52 false (zB l 0 0) (zBq l 0) (zA l 0))]

/-- A block: `R` steps, then the next block's limbs of the second operand
and the count of blocks. -/
def zBlock : List Instr :=
  (List.range l.R).flatMap (fun i => zStep l i false) ++
    ([.alu .add .r9 (.imm 8), .alu .sub .rcx (.imm 1)] : List Instr)

/-- The end: the last `u`'s products of rows 0 and 1 of `X + 1`, and the
two sets added. -/
def zFin : List Instr :=
  let i := l.S % l.R
  let U := zUq l ((l.S - 1) % 2)
  [.e5op (.vpermq (zT l) (zM l l.R) 0x93),
    .e5op (.vpmadd52 true (zU l 0 i) U (zT l)), .e5op (.vpmadd52 false (zU l 0 i) U (zM l 1))] ++
  (List.range l.R).map fun k => .e5op (.bin .vpaddq (zB l k i) (zB l k i) (zU l k i))

/-- The sums stored, a lane at `r11` and the other at `r11 + D`. -/
def zStores : List Instr :=
  (List.range l.R).flatMap fun k =>
    [.evStore (at_ .r11 (32 * k)) (zB l k (l.S % l.R)),
      .e5ExtractStore (at_ .r11 (l.D + 32 * k)) (zB l k (l.S % l.R)) 1]

/-- `[r11] := [r8] [r9] 2^(-52 S)` modulo `2¹⁰⁴ m - 1` for the `m` at `oMs`
(`rbx` the area), for both lanes: `S / R` blocks, then the `S % R` steps
left (at least one, the last). -/
def ammCoreZ : Prog isa :=
  .seq (.block (zStart l))
    (.seq (.loop (.block (zBlock l)) .ne)
      (.block ((List.range (l.S % l.R)).flatMap (fun i => zStep l i (i + 1 = l.S % l.R)) ++ zFin l ++
        zStores l ++ ([.movImm64 .r12 mask52] : List Instr) ++ carryOut l)))

/-- The multiplication of a layout: `ammCoreZ` where the layout says so;
else with the look-ahead where the lanes' roles take at most 10 registers
(2048 bits, the public operation's), whose multiplications the chain of
`u`s bounds. -/
def ammMul : Prog isa :=
  if l.z then ammCoreZ l else if l.nl * l.R ≤ 10 then ammCoreU l else ammCore l

/-- A multiplication's operands: `r8`, `r9` and `r11` at offsets `a`, `b`
and `o` of the area. -/
def ammOps (o a b : Nat) : List Instr :=
  [.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 a)), .mov .r9 (.reg .rbx),
    .alu .add .r9 (.imm (BitVec.ofNat 32 b)), .mov .r11 (.reg .rbx), .alu .add .r11 (.imm (BitVec.ofNat 32 o))]

/-- `[o] := [a] [b] 2^(-52 S)`, the offsets in `p`'s region. -/
def amm (o a b : Nat) : Prog isa := .seq (.block (ammOps o a b)) (ammMul l)

/-- `amm` modulo the prime at `oM`, by `ammCore`. -/
def ammP (o a b : Nat) : Prog isa := .seq (.block (ammOps o a b)) (ammCore l)

/-! ## Moving numbers between the layouts -/

/-- `r` shifted left by `t` (`0 < t < 64`), through `rbp`: rotated, its low
`t` bits cleared. -/
def shl (r : Reg) (t : Nat) : List Instr :=
  [.shift .ror r (64 - t), .movImm64 .rbp (BitVec.ofNat 64 (2 ^ 64 - 2 ^ t)), .alu .and r (.reg .rbp)]

/-- The `W` words at `rsi` into the limbs at `r11` (`r12` holds `2⁵² - 1`). -/
def to52 : List Instr :=
  (List.range l.L).flatMap fun j =>
    let b := 52 * j
    let w := b / 64
    let s := b % 64
    if l.W ≤ w then [.mov32 .rax (.imm 0), .store (at_ .r11 (l.off j)) .rax] else
    ([.mov .rax (.mem (at_ .rsi (8 * w)))] : List Instr) ++
    (if s = 0 then [] else [.shift .shr .rax s]) ++
    (if 12 < s ∧ w + 1 < l.W then
      ([.mov .rcx (.mem (at_ .rsi (8 * (w + 1))))] : List Instr) ++ shl .rcx (64 - s) ++
        ([.alu .or .rax (.reg .rcx)] : List Instr)
    else []) ++
    ([.alu .and .rax (.reg .r12), .store (at_ .r11 (l.off j)) .rax] : List Instr)

/-- The limbs below `2⁵²` at `r11` into `W + 1` words at `r8`. -/
def to64 : List Instr :=
  (List.range (l.W + 1)).flatMap fun w =>
    let lo := 64 * w
    let js := (List.range l.L).filter fun j => 52 * j < lo + 64 ∧ lo < 52 * j + 52
    (.mov32 .rax (.imm 0) :: js.flatMap fun j =>
      ([.mov .rcx (.mem (at_ .r11 (l.off j)))] : List Instr) ++
      (if lo ≤ 52 * j then (if 52 * j = lo then [] else shl .rcx (52 * j - lo))
        else [.shift .shr .rcx (lo - 52 * j)]) ++
      ([.alu .or .rax (.reg .rcx)] : List Instr)) ++
    ([.store (at_ .r8 (8 * w)) .rax] : List Instr)

/-! ## Before the vector code, in a prime's workspace (`rdi`) -/

/-- `aT := 2^dbls [aY] mod X` (`[aY] = R_X mod X`, so `aT = 2^(104 S - 64 W) mod X`). -/
def k1 : List (Prog isa) :=
  copyArr aT aY ++ [.block [.mov32 .rcx (.imm (BitVec.ofNat 32 l.dbls))], doubles aN aAcc aTmp aT sCtr]

/-- `to52`'s arguments for array `j` and the limbs at offset `o` of region
`p`: the array, the limbs, and `2⁵² - 1`. -/
def arrPtrs (p j o : Nat) : List Instr :=
  [.mov .rsi (.mem (hdr (sArr j))), .mov .r11 (.mem (hdr sIfma)),
    .alu .add .r11 (.imm (BitVec.ofNat 32 (l.D * p + o))), .movImm64 .r12 mask52]

/-- Array `j` into the limbs at offset `o` of the region at `r11`'s base
`rbx + p D`. -/
def arr52 (p j o : Nat) : List Instr := arrPtrs l p j o ++ to52 l

/-- The arrays every region takes, with their offsets: the modulus,
`2^dbls R_X mod X`, `x R_X`, `R_X`, and `R_X` again as the last multiplier
(`q`'s then 1, `finOne`). -/
def arrs : List (Nat × Nat) := [(aN, oM), (aT, l.oK1), (aXc, l.oX), (aY, l.oY), (aY, l.oFin)]

/-- `to52`'s arguments for the entry of `ps` that `r8` counts down to
(`ps.length` for the first). -/
def arrSel (p : Nat) : List (Nat × Nat) → Prog isa
  | [] => .block []
  | [(j, o)] => .block (arrPtrs l p j o)
  | (j, o) :: ps => .seq (.block [.alu .cmp .r8 (.imm (BitVec.ofNat 32 (ps.length + 1)))])
      (.ite .e (.block (arrPtrs l p j o)) (arrSel p ps))

/-- `arrs` into region `p`, by one `to52` in a loop. -/
def arrLoop (p : Nat) : Prog isa :=
  .seq (.block [.mov32 .r8 (.imm 5)])
    (.loop (.seq (arrSel l p (arrs l)) (.block (to52 l ++ ([.alu .sub .r8 (.imm 1)] : List Instr)))) .ne)

/-- `k₀` (the low 52 bits of the inverse) in each quadword of `oK0`, `r11`
the region (`r12` holds `2⁵² - 1`). -/
def k0St (p : Nat) : List Instr :=
  ([.mov .r11 (.mem (hdr sIfma)), .alu .add .r11 (.imm (BitVec.ofNat 32 (l.D * p))),
    .mov .rax (.mem (hdr sMinv)), .alu .and .rax (.reg .r12)] : List Instr) ++
  (List.range 4).map (fun i => .store (at_ .r11 (l.oK0 + 8 * i)) .rax)

/-- Zeros where the padded exponent goes. -/
def eZero : List Instr :=
  .mov32 .rax (.imm 0) :: (List.range ((l.P + 7) / 8)).map (fun i => .store (at_ .r11 (l.oE + 8 * i)) .rax)

/-- `q`'s last multiplier, 1 (`rax` is 0). -/
def finOne : List Instr :=
  (List.range l.L).map (fun j => .store (at_ .r11 (l.oFin + l.off j)) .rax) ++
    ([.mov32 .rax (.imm 1), .store (at_ .r11 l.oFin) .rax] : List Instr)

/-- The exponent's bytes (pointer and length in `n`'s slots `slotPtr`,
`slotLen`) at the end of the `P` at `oE`. -/
def eCopy (slotPtr slotLen : Nat) : List (Prog isa) :=
  [.block [.mov .rax (.mem (hdr sLink)), .mov .rsi (.mem (ws .rax slotPtr)), .mov .rcx (.mem (ws .rax slotLen)),
      .alu .add .r11 (.imm (BitVec.ofNat 32 (l.oE + l.P))), .alu .sub .r11 (.reg .rcx)],
    .loop (.block [.movzx8 .rax (at0 .rsi), .store8 (at0 .r11) .rax, .alu .add .rsi (.imm 1),
      .alu .add .r11 (.imm 1), .alu .sub .rcx (.imm 1)]) .ne]

/-- A group of `w` bytes of the padded exponent at `r8` (most significant
first) into its 8 digits of `w` bits at `r9`, a byte each; then the next
group. -/
def recodeBody : List Instr :=
  ([.mov32 .rax (.imm 0)] : List Instr) ++
  (List.range l.w).flatMap (fun j => [.shift .shl .rax 8, .movzx8 .rdx (at_ .r8 j), .alu .or .rax (.reg .rdx)]) ++
  (List.range 8).flatMap (fun t => [.mov .rdx (.reg .rax)] ++
    (if t = 7 then [] else [.shift .shr .rdx (l.w * (7 - t))]) ++
    [.alu .and .rdx (.imm (BitVec.ofNat 32 (l.T - 1))), .store8 (at_ .r9 t) .rdx]) ++
  ([.alu .add .r8 (.imm (BitVec.ofNat 32 l.w)), .alu .add .r9 (.imm 8), .alu .sub .rcx (.imm 1)] : List Instr)

/-- The padded exponent of region `p` into its `ND` digits at `oD`. -/
def recode (p : Nat) : List (Prog isa) :=
  [.block [.mov .r8 (.mem (hdr sIfma)), .alu .add .r8 (.imm (BitVec.ofNat 32 (l.D * p + l.oE))),
      .mov .r9 (.mem (hdr sIfma)), .alu .add .r9 (.imm (BitVec.ofNat 32 (l.D * p + l.oD))),
      .mov32 .rcx (.imm (BitVec.ofNat 32 (l.P / l.w)))],
    .loop (.block (recodeBody l)) .ne]

/-- A prime's region (`p` 0 or 1): the modulus, `2^(104 S - 64 W) mod X`,
`x R_X` as `X`, `R_X` as `Y`, the last multiplier, `k₀`, the padded
exponent and, with windows of more than 4 bits, its digits. -/
def region (p slotPtr slotLen : Nat) : List (Prog isa) :=
  k1 l ++ [arrLoop l p] ++
    [.block (k0St l p), .block (eZero l)] ++
    (if p = 0 then [] else [.block (finOne l)]) ++ eCopy l slotPtr slotLen ++ (if l.w = 4 then [] else recode l p)

/-! ## The vector code (`rbx` the area) -/

/-- `[S] := T_v` for each prime, `v` the digit at `oV`:
for each entry `j`, OR'ed in under the mask of `j = v` (one `vpternlogq`
per register), in registers `0`–`R - 1`, with the mask in `R` and a
temporary in `R + 1`. -/
def select (p : Nat) : List (Prog isa) :=
  [.block (([.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 (l.D * p + l.oTab))),
      .mov .rdx (.mem (at_ .rbx (l.D * p + l.oV))), .mov32 .rcx (.imm 0)] : List Instr) ++ (List.range l.R).map fun k => .eop (.bin .vpxorq (vreg k) (vreg k) (vreg k))),
    .loop (.block (([.mov .rax (.reg .rcx), .alu .xor .rax (.reg .rdx), .alu .cmp .rax (.imm 1),
        .alu .sbb .rax (.reg .rax), .eop (.vmovq (vreg l.R) .rax), .eop (.vpbroadcastq (vreg l.R) (vreg l.R))] : List Instr) ++
      ((List.range l.R).flatMap fun k => [.evLoad (vreg (l.R + 1)) (at_ .r8 (32 * k)),
        .eop (.vpternlogq (vreg k) (vreg (l.R + 1)) (vreg l.R) 0xF8)]) ++
      ([.alu .add .r8 (.imm (BitVec.ofNat 32 l.NB)), .alu .add .rcx (.imm 1),
        .alu .cmp .rcx (.imm (BitVec.ofNat 32 l.T))] : List Instr))) .ne,
    .block ((List.range l.R).map fun k => .evStore (at_ .rbx (l.D * p + l.oS + 32 * k)) (vreg k))]

/-- `[o] := [a]` (a number) in every region. -/
def copyN (o a : Nat) : List Instr :=
  (List.range l.nl).flatMap fun p => (List.range l.R).flatMap fun k =>
    [.evLoad (vreg 0) (at_ .rbx (l.D * p + a + 32 * k)), .evStore (at_ .rbx (l.D * p + o + 32 * k)) (vreg 0)]

/-- The operands of entry `i < 2` (`r13 = oTab + NB i`) of `convTab`: `Y`
or `X` (`oY + NB i`), in place, times `[oK1]`. -/
def convSetup : List Instr :=
  [.mov .r8 (.reg .rbx), .alu .add .r8 (.reg .r13), .alu .sub .r8 (.imm (BitVec.ofNat 32 (l.oTab - l.oY))),
   .mov .r9 (.reg .rbx), .alu .add .r9 (.imm (BitVec.ofNat 32 l.oK1)), .mov .r11 (.reg .r8)]

/-- The operands of entry `i ≥ 2` (`r13 = oTab + NB i`): `T_(i-1)`, `X`, `T_i`. -/
def tabSetup : List Instr :=
  [.mov .r8 (.reg .rbx), .alu .add .r8 (.reg .r13), .alu .sub .r8 (.imm (BitVec.ofNat 32 l.NB)),
   .mov .r9 (.reg .rbx), .alu .add .r9 (.imm (BitVec.ofNat 32 l.oX)), .mov .r11 (.reg .rbx),
   .alu .add .r11 (.reg .r13)]

/-- Entry `i` of `convTab` (`r13 = oTab + NB i`), one multiplication: below
2, `Y` or `X` into Montgomery form; after `X`, the table's first entries
`T_0 = Y` and `T_1 = X`; from 2, `T_i = T_(i-1) X 2^(-52 S)`. Then `r13`
to the next entry, `ZF` after the last. -/
def convTabBody : Prog isa :=
  .seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + 2 * l.NB)))])
    (.seq (.ite .b (.block (convSetup l)) (.block (tabSetup l)))
      (.seq (ammMul l)
        (.seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + l.NB)))])
          (.seq (.ite .e (.block (copyN l l.oTab l.oY ++ copyN l (l.oTab + l.NB) l.oX)) (.block []))
            (.block [.alu .add .r13 (.imm (BitVec.ofNat 32 l.NB)),
              .alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.oTab + l.T * l.NB)))])))))

/-- `Y` and `X` into Montgomery form (times `[oK1] 2^(-52 S)`), and the
table `T_0 = Y`, `T_1 = X`, `T_i = T_(i-1) X 2^(-52 S)`, in one loop. -/
def convTab : List (Prog isa) :=
  [.block [.mov32 .r13 (.imm (BitVec.ofNat 32 l.oTab))], .loop (convTabBody l) .ne]

/-- The operands of a window's multiplication: `[oY] := [oY] [b]`. -/
def winSetup (b : Nat) : List Instr :=
  [.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 l.oY)), .mov .r9 (.reg .rbx),
   .alu .add .r9 (.imm (BitVec.ofNat 32 b)), .mov .r11 (.reg .rbx),
   .alu .add .r11 (.imm (BitVec.ofNat 32 l.oY))]

/-- A nibble of `r` by the mask in `rdx` (all ones for the high nibble,
zero for the low), through `rcx`: `lo ^ ((hi ^ lo) & mask)`. -/
def nibSel (r : Reg) : List Instr :=
  [.mov .rcx (.reg r), .shift .shr .rcx 4, .alu .and r (.imm 15), .alu .xor .rcx (.reg r),
    .alu .and .rcx (.reg .rdx), .alu .xor r (.reg .rcx)]

/-- The register of lane `p`'s digit: `rax`, then `rsi`. -/
def dReg (p : Nat) : Reg := if p = 0 then .rax else .rsi

/-- Digit `r13` of each prime into its `V`: with windows of 4 bits, a nibble
of byte `r13 / 2` of the padded exponent (the high one for an even digit);
otherwise the digit's byte at `oD`. -/
def digLoad : List Instr :=
  if l.w = 4 then
    ([.mov .r8 (.reg .r13), .shift .shr .r8 1, .mov .rdx (.reg .r13), .alu .and .rdx (.imm 1),
      .alu .sub .rdx (.imm 1)] : List Instr) ++
    (List.range l.nl).map (fun p =>
      .movzx8 (dReg p) { base := .rbx, index := some .r8, disp := ((l.D * p + l.oE : Nat) : Int) }) ++
    (List.range l.nl).flatMap fun p => nibSel (dReg p) ++ [.store (at_ .rbx (l.D * p + l.oV)) (dReg p)]
  else
    (List.range l.nl).flatMap fun p =>
      [.movzx8 .rax { base := .rbx, index := some .r13, disp := ((l.D * p + l.oD : Nat) : Int) },
        .store (at_ .rbx (l.D * p + l.oV)) .rax]

/-- A window: `Y := Y^(2^w) T_v 2^(-52 S)` for each prime, `v` its digit
`r13` (`digLoad`, into `oV`). `S := T_v` first, then one loop of `w + 1`
multiplications (`r15` counting them down): `w` squarings of `Y`, then
`Y S`. After the last digit (`r13 = ND`), instead `S := Fin` and the one
multiplication `Y S`. -/
def window : List (Prog isa) :=
  [.seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 l.ND))])
      (.ite .e (.block (copyN l l.oS l.oFin ++ [.mov32 .r15 (.imm 1)]))
        (seqs ([.block (digLoad l)] ++ (List.range l.nl).flatMap (select l) ++
          [.block [.mov32 .r15 (.imm (BitVec.ofNat 32 (l.w + 1)))]]))),
    .loop (.seq (.block [.alu .cmp .r15 (.imm 1)])
      (.seq (.ite .e (.block (winSetup l l.oS)) (.block (winSetup l l.oY)))
        (.seq (ammMul l) (.block [.alu .sub .r15 (.imm 1)])))) .ne]

/-- The exponentiations, a digit of each exponent (`r13`, from the first
that holds a bit of it, `k0`) at a time, and after the last,
`Y := Y Fin 2^(-52 S)` (`window`). -/
def expLoop (start : List Instr := [.mov32 .r13 (.imm (BitVec.ofNat 32 l.k0))]) : List (Prog isa) :=
  convTab l ++ [.block start,
    .loop (seqs (window l ++ [.block [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.ND + 1)))]])) .ne]

/-- `c`, then `vzeroupper`. The vector code sets no MXCSR of its own: the
dispatcher of every function that runs it runs `vg_mcdt_enter` first, which
leaves MXCSR `0x1FBF` for the whole call, as MCDT asks of its multiplies
(see "MCDT" in `TCB/X86_64/Isa.lean`). -/
def withVzu (c : Prog isa) : Prog isa := .seq c (.block [.vop .vzeroupper])

/-! ### Around the exponentiations with `ammCoreZ`

The exponentiations run modulo `X = 2¹⁰⁴ m - 1` for `m = 2^(-104)` modulo
the prime, a multiple of the prime: `zPre` makes `m`, as
`2^(52 zE) 2^(52 zE) 2^(-52 S)` by `ammCore` (`ammP`), at `oMs`. Its
results are below `2 X`, not `2 p`, so the multiplication by
the last multiplier is `ammCore`'s, after the exponentiations (`zPost`),
which multiply by 1 in Montgomery form in its place.

A multiplication modulo `X` leaves a number of the size of `X` or of its
operands' product over `2^(52 S)`, whichever is larger, so it only moves
the region's numbers, which are below the prime, to the radix `2^(52 S)`
when they are multiplied by a number above it: by `2^(52 L - 1)`, which
leaves them times `2^cv`, and `2^dbls R_X` then becomes `2^(104 S - cv)`,
which `convTab` multiplies them by. -/

/-- The number whose limb `j` is `v` and the others zero, at offset `o` of
every region (through `rax`). -/
def litN (o j : Nat) (v : BitVec 64) : List Instr :=
  (List.range l.nl).flatMap fun p =>
    ([.mov32 .rax (.imm 0)] : List Instr) ++
    (List.range l.L).map (fun q => .store (at_ .rbx (l.D * p + o + l.off q)) .rax) ++
    [.movImm64 .rax v, .store (at_ .rbx (l.D * p + o + l.off j)) .rax]

/-- Before the exponentiations: `m` at `oMs`; `[oK1]`, `Y` and the
base times `2^(52 L - 1) 2^(-52 S)`; the last multiplier at `oF2`, and
`Y [oK1] 2^(-52 S)`, 1 in Montgomery form, in its place. -/
def zPre : List (Prog isa) :=
  [.block (litN l l.oS l.zE 1), ammP l l.oMs l.oS l.oS,
    .block (litN l l.oS (l.L - 1) (BitVec.ofNat 64 (2 ^ 51))),
    amm l l.oK1 l.oS l.oK1, amm l l.oY l.oS l.oY, amm l l.oX l.oS l.oX,
    .block (copyN l l.oF2 l.oFin), amm l l.oFin l.oY l.oK1]

/-- After the exponentiations: `Y` times the last multiplier, modulo the
prime. -/
def zPost : Prog isa := ammP l l.oY l.oY l.oF2

/-- The vector code: the exponentiations (`Y` and `X` into Montgomery form
with the table), the results multiplied by `oFin`. -/
def vec : Prog isa :=
  if l.z then withVzu (.seq (seqs (zPre l)) (.seq (seqs (expLoop l)) (zPost l)))
  else withVzu (seqs (expLoop l))

/-- In a prime's workspace: the result into `aY`, reduced below `X`. -/
def result (p : Nat) : List (Prog isa) :=
  [.block (([.mov .r11 (.mem (hdr sIfma)), .alu .add .r11 (.imm (BitVec.ofNat 32 (l.D * p + l.oY))),
      .mov .r8 (.mem (hdr (sArr aAcc)))] : List Instr) ++ to64 l ++
      ([.mov .rbx (.mem (hdr (sArr aY))), .mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)),
        .mov .rsi (.mem (hdr (sArr aTmp)))] : List Instr)),
    subMod, selectAcc]

/-! ## The phases -/

/-- The IFMA area after `q`'s workspace, its base into both prime
workspaces; the regions; the vector code; the results. -/
def ifma : List (Prog isa) :=
  [.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++ ([.mov .rdx (.mem (hdr sWsP)), .store (ws .rdx sIfma) .rax,
      .mov .rdx (.mem (hdr sWsQ)), .store (ws .rdx sIfma) .rax, enterP] : List Instr))] ++
  region l 0 sDp sPlen ++ [.block [leave, enterQ]] ++ region l 1 sDq sQlen ++
  [.block [.mov .rbx (.mem (hdr sIfma))], vec l] ++
  result l 1 ++ [.block [leave, enterP]] ++ result l 0 ++ [.block [leave]]

/-! ## With the key's precomputed values

`vg_rsa_private_crt_ifma_precomputed` (`mainP`) copies each prime's `R_X²
mod X` from the key's precomputed values `pre` (the CRT's stack argument 12)
rather than reducing `n`'s `R_n² mod n` (`r2X`): `R_p² mod p` is at word
`2 w_n = 4 w_X` of `pre`, and `R_q² mod q` at `5 w_X`, as `n` has `2 w_X`
words. It is masked by `n`'s mask, as `p` and `q` are: where the mask is
clear the prime is 3, and `R_X² mod 3 = 1`. -/

/-- In a prime's workspace: `rsi := pre + 8 (4 w_X)` (`+ 8 w_X` for `q`),
`r12 := w_X` and `rbx := [j]`. -/
def r2XBlk (q : Bool) (j : Nat) : List Instr :=
  [.mov .rsi (.mem Crt.preArg), .mov .rax (.mem (hdr sW)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax)] ++ (if q then [.alu .add .rsi (.reg .rax)] else []) ++
  [.alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rsi (.reg .rax), .mov .r12 (.mem (hdr sW)),
    .mov .rbx (.mem (hdr (sArr j)))]

/-- The low word of `[rbx]`, masked by `r15`, with 1 where the mask is
clear. -/
def orOne : List Instr :=
  [.mov .rax (.reg .r15), .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .alu .and .rax (.imm 1),
    .alu .or .rax (.mem (at0 .rbx)), .store (at0 .rbx) .rax]

/-- `[j]` masked by `n`'s mask, which it leaves in `r15`. -/
def maskN (j : Nat) : List (Prog isa) := [
  .block [.mov .rax (.mem (hdr sLink)), .mov .r15 (.mem (ws .rax sMask)), .mov .r12 (.mem (hdr sW)),
    .mov .rbx (.mem (hdr (sArr j)))],
  wordLoop 0 [.mov .rax (.mem (ix .rbx .r14)), .alu .and .rax (.reg .r15), .store (ix .rbx .r14) .rax]]

/-- In a prime's workspace, `[j] := mask ? R_X² mod X : 1` from `pre`
(`q` for `q`'s), with `n`'s mask. -/
def r2X (q : Bool) (j : Nat) : List (Prog isa) :=
  [.block (r2XBlk q j), copyWords] ++ maskN j ++ [.block orOne]

/-- `prep`, with `R_X² mod X` from `pre`. -/
def prepP (mul : Nat → Nat → Nat → Prog isa) (sl : Nat) (q : Bool) : List (Prog isa) :=
  [.block [.mov .rdi (.mem (hdr sl))]] ++ r2X q aY ++ redc mul aXm ++ [mul aT aY aXc] ++
    copyArr aXc aT ++ [mul aY aY aOne, .block [leave]]

/-- `pre`, with `R_X² mod X` from `pre`. -/
def preP (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  prepP mul sWsQ true ++ prepP mul sWsP false

/-- `post`, with `R_p² mod p` from `pre`. -/
def postP (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [.block [enterP]] ++ r2X false aXc ++
  [.block [.mov .rax (.mem (hdr sLink)), .mov .rax (.mem (ws .rax sWsQ)), .mov .rsi (.mem (ws .rax (sArr aY))),
      .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aChunk)))],
    copyWords, mul aChunk aChunk aXc] ++ copyArr aXc aChunk ++
  subModArr aT aY aXc ++ loadArr aChunk sQinv sPlen ++ maskArr aChunk ++ [mul aY aT aChunk, .block [leave]]

/-- Whether `n` has `2 W` words and `p` and `q` `W` (`(len + 7) / 8` of
their lengths in bytes): ZF. -/
def sizes : List Instr :=
  [.mov .rax (.mem (hdr sW)), .alu .xor .rax (.imm (BitVec.ofNat 32 (2 * l.W))), .mov .rdx (.mem (hdr sPlen)),
    .alu .add .rdx (.imm 7), .shift .shr .rdx 3, .alu .xor .rdx (.imm (BitVec.ofNat 32 l.W)),
    .alu .or .rax (.reg .rdx), .mov .rdx (.mem (hdr sQlen)),
    .alu .add .rdx (.imm 7), .shift .shr .rdx 3, .alu .xor .rdx (.imm (BitVec.ofNat 32 l.W)),
    .alu .or .rax (.reg .rdx)]

end VG.Impl.Rsa.X86_64.CrtIfma

namespace VG.Impl.Rsa.X86_64.CrtIfma
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
  VG.Impl.Rsa.X86_64.Crt

/-- ZF: whether the key has the sizes of one of the layouts. -/
def anySizes : Prog isa :=
  .seq (.block (sizes lay2048)) (.ite .e (.block [])
    (.seq (.block (sizes lay3072)) (.ite .e (.block []) (.block (sizes lay4096)))))

/-- The vector code of the layout whose sizes the key has (one of them, by
`anySizes`), with the layout `l2` for 2048-bit keys (`lay2048` or
`lay2048z`, which have the same sizes). -/
def ifmaAny (l2 : Lay) : Prog isa :=
  .seq (.block (sizes lay2048)) (.ite .e (seqs (ifma l2))
    (.seq (.block (sizes lay3072)) (.ite .e (seqs (ifma lay3072)) (seqs (ifma lay4096)))))

/-- `main` with `R² mod n` from the key's precomputed values (`nSetupP`). -/
def mainP (l2 : Lay) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs (nSetupP mul ++ primesSetup ++ checksP ++
    [.seq anySizes (.ite .e (seqs (preP mul ++ [ifmaAny l2] ++ postP mul))
      (seqs (qPhase mul (Crt.expLoop mul tabSelect) ++ pPhase mul (Crt.expLoop mul tabSelect))))] ++
    finish)

/-- `vg_rsa_private_crt_ifma_precomputed` and
`vg_rsa_private_crt_ifma512_precomputed`: `code` with `mainP`. -/
def codeP (l2 : Lay) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block (Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid))
    (.ite .ne fail (mainP l2 mul))

end VG.Impl.Rsa.X86_64.CrtIfma
