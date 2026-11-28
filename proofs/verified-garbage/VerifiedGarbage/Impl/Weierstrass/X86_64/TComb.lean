module

public import VerifiedGarbage.Impl.Weierstrass.X86_64
public import VerifiedGarbage.Impl.Weierstrass.TCombWords

/-!
# Short Weierstrass curves on x86-64: a fixed-base comb from tables in memory

`[k]G` for the fixed point `G` and a scalar `k < 2^(w J)` whose bits are a
table of bytes (byte `t` is bit `t`, as `bits` writes it), from `J` tables of
constants in memory (the `static` `tsym`, `Artifact.consts`, whose address
the code forms with `leaSym`): table `j` holds `[m 2^(wj)]G` for
`m = 1 … H` (`H = 2^(w-1)`), affine and in Montgomery form, entry `m` at
`16 n (m - 1)` bytes into the table (`x` then `y`, `n` words each), the
tables `16 n H` bytes apart (`tcombWords`). With the windows `k_j` of `w`
bits of `k` and the digits `d_j = k_j - H ∈ [-H, H)`,
`k = c + Σ d_j 2^(wj)` for `c = H Σ_{j<J} 2^(wj)`: the accumulator `A`
starts at `[c]G` (a constant), and iteration `j` adds the entry of table `j`
for `|d_j|` (or the point at infinity for `d_j = 0`), negated if `d_j < 0`,
for `j = J - 1` down to `0`: `J` additions, and no doublings. This is the comb
of `Impl/Weierstrass/AArch64/TComb.lean`, with the same tables. An entry's `Z`
is 1, so the addition is the mixed one for `a = -3` (`rcb3m`, with `b` in
`S.b3`), into `D`; it is wrong for the point at infinity, so `A` takes `D`
under the mask of a nonzero digit (`eqMask 0`, from the digit computed
again).

For secret scalars, entries are selected in constant time: every
entry of the table is loaded, 16 bytes at a time, at an address that depends
only on `j` (public), into `xmm14`, and kept (`pand`, `por`) under a mask in
both quadwords of `xmm15` that is all ones exactly when its index is the
magnitude (`selEntryAt`); the entry accumulates in `xmm0`, `xmm1`, …, and is
stored to `E`'s `x` and `y`, which are adjacent. The entry's `Z` is `1`
(Montgomery's, `R mod p`) unless the magnitude is zero, when the entry is
`(0 : 1 : 0)`. The negation computes `0 - y` and selects it by the mask of the
digit's sign.

Public verification scalars may instead use `selectPublic`: it directly
loads the selected entry, with a safe first-entry address for a zero digit.
The default `comb` and `step` keep the full scan for secret scalars.

The counter is `rbx`, and products of it with constants are by `mul`.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

/-- What the comb needs: the field, the complete addition's slots, the
accumulator `A`, the selected entry `E` (`E.y = E.x + 8 n`), the sum `D`, a
slot for `-y` and one holding zero, the table of the scalar's bits, the
digits' width `w` and number `J`, the name of the static holding the tables,
the start `[c]G` and `R mod p`, both in Montgomery form. -/
structure TCombCfg where
  M : Mod
  S : RcbSlots
  A : Pt
  E : Pt
  D : Pt
  neg : Nat
  zero : Nat
  bits : Nat
  /-- The bytes of the table of bits the scalar's bits fill; the code clears
  those up to `w J`. -/
  kbytes : Nat
  tsym : String
  w : Nat
  J : Nat
  start : Nat × Nat
  one : Nat
  /-- Whether the selection loads 32 bytes at a time, with AVX2 (`selPassV`). -/
  avx2 : Bool := false
  /-- Whether the comb with Booth's digits selects window `j + 1`'s entry
  during window `j`'s addition (`TCombCfg.combJP`), where that code is
  eligible (`TCombCfg.pipeOk`). -/
  pipe : Bool := false

/-- The accumulators of the selection: `xmm0`, `xmm1`, …, sixteen bytes of the
entry each. -/
def selAcc (c : Nat) : XReg :=
  [XReg.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11,
    .xmm12, .xmm13].getD c .xmm0

/-- `rcx = w (rbx)`, through `rax` and `rdx`. -/
def winIndex (w : Nat) : List Instr :=
  [.mov .rax (.reg .rbx), .mov32 .rcx (.imm (BitVec.ofNat 32 w)), .mul .rcx, .mov .rcx (.reg .rax)]

/-- `[rdi + rcx + d]`: byte `d` of the window at `rcx`. -/
def winByte (d : Nat) : MemOp := { base := .rdi, index := some .rcx, disp := d }

/-- `rax = Σ_{i<k} b_i 2^i` for the bytes `b_i` at `rdi + rcx + d + i`, by
Horner's rule from the top, through `rdx`. -/
def hornerBits : Nat → Nat → List Instr
  | _, 0 => [.mov32 .rax (.imm 0)]
  | d, k + 1 => hornerBits (d + 1) k ++ [.alu .add .rax (.reg .rax), .movzx8 .rdx (winByte d),
      .alu .add .rax (.reg .rdx)]

/-- From the window `v` in `rax`: `|v - H|` into `rax` and `r8`, through `rdx`. -/
def magnitudeH (H : Nat) : List Instr :=
  [.alu .sub .rax (.imm (BitVec.ofNat 32 H)), .mov .rdx (.reg .rax), .shift .shr .rdx 63,
    .mov32 .r8 (.imm 0), .alu .sub .r8 (.reg .rdx), .alu .xor .rax (.reg .r8), .alu .sub .rax (.reg .r8),
    .mov .r8 (.reg .rax)]

/-- `rcx` all ones if `r8 = v`, else zero (`v < 2^31`). -/
def eqMask (v : Nat) : List Instr :=
  [.mov32 .rcx (.imm (BitVec.ofNat 32 v)), .alu .xor .rcx (.reg .r8), .alu .cmp .rcx (.imm 1),
    .alu .sbb .rcx (.reg .rcx)]

/-- `[o] = [a]` for a point. -/
def copyPt (n : Nat) (o a : Pt) : List Instr := copy n o.x a.x ++ copy n o.y a.y ++ copy n o.z a.z

/-- `[rdx + d]`: byte `d` of the table at `rdx`. -/
def tblAt (d : Nat) : MemOp := { base := .rdx, disp := d }

/-- Entry `m` (from 1) of a table at `rdx` whose entries are `st` bytes
apart: its `np` 16-byte pieces, piece `c` at `po c` bytes into the entry,
kept in the accumulators under the mask of `r8 = m`. -/
def selEntryAt (st np : Nat) (po : Nat → Nat) (m : Nat) : List Instr :=
  eqMask m ++ ([.xop (.movq .xmm15 .rcx), .xop (.bin .punpcklqdq .xmm15 .xmm15)] : List Instr) ++
  ((List.range np).flatMap fun c =>
    [.movdquLoad .xmm14 (tblAt (st * (m - 1) + po c)), .xop (.bin .pand .xmm14 .xmm15),
      .xop (.bin .por (selAcc c) .xmm14)] : List Instr)

/-- The entry for the magnitude in `r8` of the `H` entries of the table at
`rdx` (`selEntryAt st np po`) to `o`, piece `c` at `o + po c`: the
accumulators cleared, every entry kept under its mask, and stored. -/
def selPassAt (o H st np : Nat) (po : Nat → Nat) : List Instr :=
  (List.range np).map (fun c => .xop (.bin .pxor (selAcc c) (selAcc c))) ++
  (List.range H).flatMap (fun m => selEntryAt st np po (m + 1)) ++
  (List.range np).map fun c => .movdquStore (sc (o + po c)) (selAcc c)

/-- The 16-byte piece where 32-byte piece `c` of an entry of `n` 16-byte
pieces starts: `2 c`, and for the last of the `(n + 1) / 2`, `n - 2`, so
that for an odd `n` it overlaps the one before rather than reading past the
entry. -/
def qY (n c : Nat) : Nat := if c + 1 < (n + 1) / 2 then 2 * c else n - 2

/-- Entry `m` (from 1) of a table at `rdx` whose entries are `st` bytes
apart, with AVX2: the mask of `ymm14 = ymm13` (both broadcasts of a
doubleword: `m` and the magnitude) in `ymm15`, `ymm14` incremented by
`ymm12` (one in every doubleword), and the entry's `np` 32-byte pieces,
piece `c` at `16 q c` bytes into the entry, kept in the 256-bit
accumulators under the mask, through `ymm11`. -/
def selEntryY (st np : Nat) (q : Nat → Nat) (m : Nat) : List Instr :=
  [.vop (.vbin .vpcmpeqd .l256 .xmm15 .xmm14 .xmm13), .vop (.vbin .vpaddd .l256 .xmm14 .xmm14 .xmm12)] ++
  (List.range np).flatMap fun c =>
    [.vbinLoad .vpand .l256 .xmm11 .xmm15 (tblAt (st * (m - 1) + 16 * q c)),
      .vop (.vbin .vpor .l256 (selAcc c) (selAcc c) .xmm11)]

/-- `selPassAt` with AVX2, for entries of `np` 32-byte pieces, piece `c` at
`16 q c` bytes into the entry: the magnitude in `r8` and the counter (from
1) broadcast, the 256-bit accumulators cleared, every entry kept under its
mask (`selEntryY`), the accumulators stored to `o + 16 q c`, and the upper
halves of the `ymm` registers cleared (`vzeroupper`), through `rcx`. -/
def selPassY (o H st np : Nat) (q : Nat → Nat) : List Instr :=
  ([.vop (.vmovq .xmm13 .r8), .vop (.vpbroadcastd .l256 .xmm13 .xmm13), .mov32 .rcx (.imm 1),
    .vop (.vmovq .xmm12 .rcx), .vop (.vpbroadcastd .l256 .xmm12 .xmm12), .vop (.vmovdqa .l256 .xmm14 .xmm12)] : List Instr) ++
  ((List.range np).map (fun c => .vop (.vbin .vpxor .l256 (selAcc c) (selAcc c) (selAcc c))) : List Instr) ++
  ((List.range H).flatMap (fun m => selEntryY st np q (m + 1)) : List Instr) ++
  ((List.range np).map (fun c => .vmovdquStore .l256 (sc (o + 16 * q c)) (selAcc c)) : List Instr) ++ ([.vop .vzeroupper] : List Instr)

namespace TCombCfg

variable (K : TCombCfg)

/-- `H = 2^(w-1)`, the entries of a table. -/
def H : Nat := 2 ^ (K.w - 1)

/-- The bytes of a table. -/
def tblBytes : Nat := 16 * K.M.n * K.H

/-- `rdx` = table `rbx`'s address, from the static `tsym`'s, through `rax` and
`rcx`. -/
def selSetup : List Instr :=
  [.mov .rax (.reg .rbx), .mov32 .rcx (.imm (BitVec.ofNat 32 K.tblBytes)), .mul .rcx,
    .leaSym .rdx K.tsym, .alu .add .rdx (.reg .rax)]

/-- The entry of table `rbx` for the magnitude in `r8` into `E`'s `x` and
`y`: the accumulators cleared, every entry kept under its mask, and stored. -/
def selPass : List Instr := selPassAt K.E.x K.H (16 * K.M.n) K.M.n (16 * ·)

/-- `selPass`, with AVX2 (`selPassY`, 32 bytes at a time) if the comb uses
it: for an odd number of words, the last two 32-byte pieces of an entry
overlap (`qY`). -/
def selPassV : List Instr :=
  if K.avx2 && 2 ≤ K.M.n then selPassY K.E.x K.H (16 * K.M.n) ((K.M.n + 1) / 2) (qY K.M.n) else K.selPass

/-- `y = R` if the magnitude in `r8` is zero (when the selected `y` is zero),
and `Z = R` unless it is, through `rax`, `rcx` and `rdx`. -/
def selOne : List Instr :=
  [.mov .rcx (.reg .r8), .alu .cmp .rcx (.imm 1), .alu .sbb .rcx (.reg .rcx)] ++
  (List.range K.M.n).flatMap (fun i =>
    [.movImm64 .rax (wordOf K.one i), .alu .and .rax (.reg .rcx), .alu .or .rax (.mem (sc (K.E.y + 8 * i))),
      .store (sc (K.E.y + 8 * i)) .rax]) ++
  .alu .xor .rcx (.imm (-1)) :: (List.range K.M.n).flatMap fun i =>
    [.movImm64 .rax (wordOf K.one i), .alu .and .rax (.reg .rcx), .store (sc (K.E.z + 8 * i)) .rax]

/-- The entry of table `rbx` for the magnitude in `r8` into `E`. -/
def select : List Instr := K.selSetup ++ K.selPassV ++ K.selOne

/-- Address of the public digit's entry. A zero magnitude safely reads the
first entry, which the mask subsequently clears. -/
def publicAddress : List Instr :=
  [.mov .rax (.reg .rbx), .mov32 .rcx (.imm (BitVec.ofNat 32 K.H)), .mul .rcx,
    .mov .rcx (.reg .r8), .alu .sub .rcx (.imm 1), .alu .adc .rcx (.imm 0),
    .alu .add .rax (.reg .rcx), .mov32 .rcx (.imm (BitVec.ofNat 32 (16 * K.M.n))), .mul .rcx,
    .leaSym .rdx K.tsym, .alu .add .rdx (.reg .rax)]

/-- All ones in both halves of `xmm15` unless the public magnitude is zero. -/
def publicMask : List Instr :=
  eqMask 0 ++ [.alu .xor .rcx (.imm (-1)),
    .xop (.movq .xmm15 .rcx), .xop (.bin .punpcklqdq .xmm15 .xmm15)]

/-- Read only the selected public entry, then store its masked coordinates.
All loads precede the stores. -/
def publicLoad : List Instr :=
  (List.range K.M.n).flatMap (fun i =>
    [.movdquLoad (selAcc i) (tblAt (16 * i)), .xop (.bin .pand (selAcc i) .xmm15)]) ++
  (List.range K.M.n).map (fun i => .movdquStore (sc (K.E.x + 16 * i)) (selAcc i))

/-- Direct lookup for public scalars only. Secret scalars use `select`. -/
def selectPublic : List Instr := K.publicAddress ++ publicMask ++ K.publicLoad ++ K.selOne

/-- The digit's magnitude into `rax` and `r8`: its window and `|k - H|`. -/
def digit : List Instr := winIndex K.w ++ hornerBits K.bits K.w ++ magnitudeH K.H

/-- `rcx` all ones if digit `rbx` is negative, that is if the top bit of its
window is clear: `rcx = b_{w-1} - 1`, through `rax` and `rdx`. -/
def signMask : List Instr :=
  winIndex K.w ++ [.movzx8 .rax (winByte (K.bits + K.w - 1)), .alu .sub .rax (.imm 1),
    .mov .rcx (.reg .rax)]

/-- `[y] = -[y]` (through `[neg]`, with zero at `zero`) if digit `rbx` is
negative. -/
def negY : List Instr := Mont.X86_64.sub K.M K.neg K.zero K.E.y ++ K.signMask ++ sel K.M.n K.E.y K.E.y K.neg

/-- Iteration `j = rbx - 1` (with `rbx` counting down from `J`): the entry,
negated for a negative digit, added to `A`. -/
def step (publicLookup : Bool := false) : Prog isa :=
  .seq (.block ([.alu .sub .rbx (.imm 1)] ++ K.digit ++ (if publicLookup then K.selectPublic else K.select))) <|
  .seq (.block K.negY) <|
  .seq (fprogB K.M (rcb3m K.S K.A K.E K.D)) <|
  .block (K.digit ++ eqMask 0 ++ selPt K.M.n K.A K.D K.A ++ [.alu .test .rbx (.reg .rbx)])

/-- The words of the table of bits the comb clears, past the scalar's
`kbytes`, up to `w J`. -/
def zw : Nat := (K.w * K.J - K.kbytes + 7) / 8

/-- `A = [c]G`, the bytes of the table of bits past the scalar's cleared (to
`w J`, in words), and the counter. -/
def init : List Instr :=
  setConst K.M.n K.A.x K.start.1 ++ setConst K.M.n K.A.y K.start.2 ++ setConst K.M.n K.A.z K.one ++
    .mov32 .rax (.imm 0) :: (List.range K.zw).map (fun i => .store (sc (K.bits + K.kbytes + 8 * i)) .rax) ++
    [.mov32 .rbx (.imm (BitVec.ofNat 32 K.J))]

/-- `[k]G` into `A`. -/
def comb (publicLookup : Bool := false) : Prog isa := .seq (.block K.init) (.loop (K.step publicLookup) .ne)

end TCombCfg

end VG.Impl.Weierstrass.X86_64
