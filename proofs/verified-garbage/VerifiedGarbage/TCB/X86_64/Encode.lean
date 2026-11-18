module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Machine code of the x86-64 model's instructions

**Trusted.** The bytes of each straight-line instruction of the model
(`Instr`), and of the return: what the printer (`Print.lean`) emits, as
`.byte <bytes>`, in place of the instruction's text, so that what runs is
these bytes, not the assembler's reading of a mnemonic. The branches (`jcc`,
`jmp`), the call and the address of a static (`leaSym`), whose bytes depend
on where their target is, are still printed as text for the assembler and
linker to lay out.

The encodings are those of the Intel 64 and IA-32 Architectures Software
Developer's Manual, Volume 2, chapter 2: the instruction format (legacy
prefixes, REX, opcode, ModR/M, SIB, displacement, immediate; §2.1, §2.2.1,
Tables 2-2 and 2-3 for the ModR/M and SIB forms, Table 2-4 for REX), the
VEX prefix (§2.3.5, Figure 2-9: `C5` with `R̄ vvvv̄ L pp`, or `C4` with
`R̄ X̄ B̄ m-mmmm` and `W vvvv̄ L pp`) and the EVEX prefix (§2.7.1, Table
2-36: `62` with `R̄ X̄ B̄ R̄' 0 mmm`, `W vvvv̄ 1 pp` and `z L'L b V̄' aaa`; for
a register `r/m`, `X̄` holds bit 4 of its number, §2.7.2), with each
instruction's opcode, `pp` (none, `66`, `F3`, `F2`), opcode map (`0F`,
`0F38`, `0F3A`) and `W` from its page in chapters 3 to 6, which each
definition names. `WIG` is encoded `W = 0`.

Where an instruction has more than one encoding, the one here is LLVM's
assembler's for the printed text, so that the bytes are those it produced:
* between two general-purpose registers, the form whose ModR/M `r/m` field
  is the destination (`89 /r` for `mov`; `01 /r`, `29 /r`, … for the ALU
  instructions; `85 /r` for `test`);
* an immediate that fits a sign-extended byte, the `83 /digit ib` form
  (`6B /r ib` for `imul`); a wider one, `RAX`'s one-byte-shorter form
  (`05 id`, …, `A9 id`) for `RAX`, else `81 /digit id` (`F7 /0 id` for
  `test`, which has no `ib` form; `69 /r id` for `imul`); `mov r64, imm32`
  is `REX.W C7 /0 id` (sign-extended), `mov r32, imm32` is `B8+rd id`;
* a shift by 1, `D1 /digit`, else `C1 /digit ib`;
* a memory operand, the shortest ModR/M and SIB: no displacement for 0
  (but with `RBP` or `R13` as base, whose `mod = 00` encoding means no
  base or RIP, which take a zero byte), a byte for a displacement in
  `-128 … 127`, else 4 bytes; a SIB byte when there is an index, or the
  base is `RSP` or `R12` (`24`: no index); with EVEX, the byte is the
  displacement divided by the operand's size `N` (disp8*N, §2.7.5) when it
  divides it, else 4 bytes;
* REX only when one of its bits is set, or to name `SPL`, `BPL`, `SIL` or
  `DIL` (§2.2.1.2); the two-byte VEX prefix when `X`, `B` and `W` are 0
  and the map is `0F`;
* for a commutative VEX instruction of map `0F` and `W = 0` between three
  registers (`vpaddd`, `vpaddq`, `vpaddw`, `vpxor`, `vpor`, `vpand`,
  `vpmuludq`, `vpmullw`, `vpmulhw`, `vpmaddwd`, `vpcmpeqd`), whose second
  source is one of registers 8–15 and first source is not, the sources
  swapped, which computes the same and fits the two-byte prefix; likewise
  `vmovdqa` and `vmovq` between registers of which only the source is one of
  8–15 take their store forms (`66 0F 7F /r`, `66 0F D6 /r`), with the
  source in ModR/M's `reg` field;
* the mnemonics of `Evex.lean` with every operand in `xmm0`–`xmm15`
  (`.lo`) that have a VEX form (`vpaddq`, `vpsubq`, the logical shifts,
  `vpermq`, `vpbroadcastq`, `vmovq`) are encoded with VEX, as `Print.lean`'s
  docs of `EOp.asm` say.

`encode` is `none` for an instruction whose operand does not fit its field
(a displacement outside `-2³¹ … 2³¹ - 1`, an immediate count of 256 or
more, a scale other than 1, 2, 4 or 8, `RSP` as an index, an immediate
where only a register or memory can be), which the printer reports as
unencodable (`Printer.unencodable`) and the emitter refuses
(`Rust.checkEncodable`), rather than truncating it; and for `leaSym`, which
is text.
-/

@[expose] public section

namespace VG.X86_64

namespace Enc

/-- The number of a register in ModR/M, SIB, VEX and EVEX fields (SDM Vol.
2, Table 3-1, and §2.2.1.2, REX's extension of each field to 4 bits):
`RAX` 0 to `R15` 15, `Reg`'s order. -/
def reg (r : Reg) : Nat := r.ctorIdx

/-- `xmm0` 0 to `xmm15` 15. -/
def xreg (r : XReg) : Nat := r.ctorIdx

/-- `xmm16` 16 to `xmm31` 31. -/
def hreg (r : HReg) : Nat := r.ctorIdx + 16

def vreg : VReg → Nat
  | .lo r => xreg r
  | .hi r => hreg r

/-- The little-endian bytes of the `n`-byte value `v`. -/
def le (n v : Nat) : List Nat := (List.range n).map fun i => (v >>> (8 * i)) % 256

/-- The byte of a signed 8-bit value. -/
def i8 (v : Int) : Nat := (v % 256).toNat

def fitsI8 (v : Int) : Bool := -128 ≤ v && v < 128

def fitsI32 (v : Int) : Bool := -2 ^ 31 ≤ v && v < 2 ^ 31

/-- An immediate byte: `none` for a value of 256 or more. -/
def ib (n : Nat) : Option (List Nat) := if n < 256 then some [n] else none

/-- The `r/m` operand of an instruction: a register, by number, or memory. -/
inductive RM
  | reg (n : Nat)
  | mem (m : MemOp)

/-- The ModR/M, SIB and displacement bytes of an `r/m` operand, and its
extension bits: `x`, REX/VEX/EVEX's `X` (bit 3 of the index; for a register
in EVEX, bit 4 of its number), and `b`, their `B` (bit 3 of the base or the
register). -/
structure ModRM where
  x : Nat
  b : Nat
  bytes : List Nat

/-- SIB's `ss` of a scale. -/
def ss : Nat → Option Nat
  | 1 => some 0 | 2 => some 1 | 4 => some 2 | 8 => some 3 | _ => none

/-- The ModR/M, SIB and displacement of `rm` with the `reg` field `r` (its
low 3 bits), in the shortest form (see the module docs), an 8-bit
displacement scaled by `n` (EVEX's disp8*N; 1 otherwise). -/
def modrm (r : Nat) (rm : RM) (n : Nat := 1) : Option ModRM :=
  match rm with
  | .reg k => some { x := k / 16 % 2, b := k / 8 % 2, bytes := [0xC0 ||| (r % 8) <<< 3 ||| k % 8] }
  | .mem m => do
    let b := reg m.base
    let (x, sib) ← match m.index with
      | none => some (0, if b % 8 == 4 then [0x24] else [])
      | some i =>
        if i == .rsp then none
        else (ss m.scale).map fun s => (reg i / 8, [s <<< 6 ||| (reg i % 8) <<< 3 ||| b % 8])
    let rmBits := if sib.isEmpty then b % 8 else 4
    let (md, disp) ←
      if m.disp == 0 && b % 8 != 5 then some (0, [])
      else if m.disp % n == 0 && fitsI8 (m.disp / n) then some (1, [i8 (m.disp / n)])
      else if fitsI32 m.disp then some (2, le 4 (m.disp % 2 ^ 32).toNat)
      else none
    return { x, b := b / 8, bytes := [md <<< 6 ||| (r % 8) <<< 3 ||| rmBits] ++ sib ++ disp }

/-- A legacy-encoded instruction (§2.1, §2.2.1): the prefixes `pfx`, REX
(`0100WRXB`) if any of its bits is set or `rex` (to name `SPL`, `BPL`, `SIL`
or `DIL`), the opcode `op`, the ModR/M of `r` and `rm`, and `imm`. -/
def legacy (pfx : List Nat) (w : Bool) (op : List Nat) (r : Nat) (rm : RM) (imm : List Nat := [])
    (rex : Bool := false) : Option (List Nat) := do
  let e ← modrm r rm
  let bits := (if w then 8 else 0) ||| (r / 8 % 2) <<< 2 ||| e.x <<< 1 ||| e.b
  return pfx ++ (if bits != 0 || rex then [0x40 ||| bits] else []) ++ op ++ e.bytes ++ imm

/-- An instruction whose opcode's last byte holds the register `k`'s low 3
bits (`B8+rd`, `50+rd`, `0F C8+rd`): REX if `W` or `B` is set, `pre`, then
`op + (k mod 8)`, then `imm`. -/
def plusReg (w : Bool) (pre : List Nat) (op k : Nat) (imm : List Nat := []) : List Nat :=
  let bits := (if w then 8 else 0) ||| k / 8 % 2
  (if bits != 0 then [0x40 ||| bits] else []) ++ pre ++ [op + k % 8] ++ imm

/-- The legacy prefix of `pp`: none, `66`, `F3`, `F2`. -/
def ppBytes : Nat → List Nat
  | 1 => [0x66] | 2 => [0xF3] | 3 => [0xF2] | _ => []

/-- The escape bytes of an opcode map: `0F`, `0F 38`, `0F 3A`. -/
def mapBytes : Nat → List Nat
  | 2 => [0x0F, 0x38] | 3 => [0x0F, 0x3A] | _ => [0x0F]

/-- A legacy SSE instruction of prefix `pp`, map `map` and opcode `op`. -/
def sse (pp map op r : Nat) (rm : RM) (imm : List Nat := []) (w : Bool := false) :
    Option (List Nat) :=
  legacy (ppBytes pp) w (mapBytes map ++ [op]) r rm imm

/-- A VEX-encoded instruction (§2.3.5): `pp` (0 none, 1 `66`, 2 `F3`, 3
`F2`), `map` (1 `0F`, 2 `0F38`, 3 `0F3A`), `W`, `L`, the register `v` of
`vvvv` (0, encoded `1111`, if it has none), the opcode, the ModR/M of `r` and
`rm`, and `imm`. The two-byte prefix `C5` when `X`, `B` and `W` are 0 and
the map is `0F`, else `C4`. -/
def vex (pp map : Nat) (w : Bool) (l v op r : Nat) (rm : RM) (imm : List Nat := []) :
    Option (List Nat) := do
  let e ← modrm r rm
  let rb := 1 - r / 8 % 2
  let vv := 15 - v % 16
  let tail := [op] ++ e.bytes ++ imm
  if e.x == 0 && e.b == 0 && !w && map == 1 then
    return [0xC5, rb <<< 7 ||| vv <<< 3 ||| l <<< 2 ||| pp] ++ tail
  else
    return [0xC4, rb <<< 7 ||| (1 - e.x) <<< 6 ||| (1 - e.b) <<< 5 ||| map,
      (if w then 0x80 else 0) ||| vv <<< 3 ||| l <<< 2 ||| pp] ++ tail

/-- An EVEX-encoded instruction (§2.7.1): as `vex`, with `ll` the vector
length (`L'L`: 0 128, 1 256, 2 512 bits), registers 0–31, `n` the size of
the memory operand that scales an 8-bit displacement (§2.7.5), `b` the
broadcast bit, `aaa` the opmask register and `z` zeroing-masking. -/
def evex (pp map : Nat) (w : Bool) (ll v op r : Nat) (rm : RM) (n : Nat := 1)
    (imm : List Nat := []) (b : Bool := false) (aaa : Nat := 0) (z : Bool := false) :
    Option (List Nat) := do
  let e ← modrm r rm n
  let p0 := (1 - r / 8 % 2) <<< 7 ||| (1 - e.x) <<< 6 ||| (1 - e.b) <<< 5 |||
    (1 - r / 16 % 2) <<< 4 ||| map
  let p1 := (if w then 0x80 else 0) ||| (15 - v % 16) <<< 3 ||| 4 ||| pp
  let p2 := (if z then 0x80 else 0) ||| ll <<< 5 ||| (if b then 0x10 else 0) |||
    (1 - v / 16 % 2) <<< 3 ||| aaa
  return [0x62, p0, p1, p2, op] ++ e.bytes ++ imm

/-- `L` of a VEX vector length. -/
def len : VLen → Nat
  | .l128 => 0
  | .l256 => 1

/-- The `r/m` operand of a general-purpose source: `none` for an
immediate. -/
def src : Src → Option RM
  | .reg r => some (.reg (reg r))
  | .mem m => some (.mem m)
  | .imm _ => none

/-- The `/digit` of an ALU instruction's `81`/`83` forms, the opcode of its
`r/m, r` form (whose `r, r/m` form is 2 more) and of `RAX`'s `imm32` form;
`test`'s are `F7 /0`, `85` (both ways) and `A9`. -/
def aluDigit : AluOp → Nat
  | .add => 0 | .or => 1 | .adc => 2 | .sbb => 3 | .and => 4 | .sub => 5 | .xor => 6 | .cmp => 7
  | .test => 0

def aluRm : AluOp → Nat
  | .add => 0x01 | .or => 0x09 | .adc => 0x11 | .sbb => 0x19 | .and => 0x21 | .sub => 0x29
  | .xor => 0x31 | .cmp => 0x39 | .test => 0x85

def aluRax : AluOp → Nat
  | .add => 0x05 | .or => 0x0D | .adc => 0x15 | .sbb => 0x1D | .and => 0x25 | .sub => 0x2D
  | .xor => 0x35 | .cmp => 0x3D | .test => 0xA9

/-- `op dst, src` of an ALU instruction, 64-bit (`W`) or 32-bit. -/
def alu (w : Bool) (op : AluOp) (d : Reg) : Src → Option (List Nat)
  | .reg s => legacy [] w [aluRm op] (reg s) (.reg (reg d))
  | .mem m => legacy [] w [if op == .test then 0x85 else aluRm op + 2] (reg d) (.mem m)
  | .imm v =>
    if op != .test && fitsI8 v.toInt then
      legacy [] w [0x83] (aluDigit op) (.reg (reg d)) [i8 v.toInt]
    else if d == .rax then
      some ((if w then [0x48] else []) ++ [aluRax op] ++ le 4 v.toNat)
    else legacy [] w [if op == .test then 0xF7 else 0x81] (aluDigit op) (.reg (reg d)) (le 4 v.toNat)

/-- "ROR" (`/1`), "SHL" (`/4`), "SHR" (`/5`) by an immediate: `D1 /digit` by
1, else `C1 /digit ib`. -/
def shift (w : Bool) (op : ShiftOp) (d : Reg) (n : Nat) : Option (List Nat) := do
  let digit := match op with | .ror => 1 | .shl => 4 | .shr => 5
  if n == 1 then legacy [] w [0xD1] digit (.reg (reg d))
  else legacy [] w [0xC1] digit (.reg (reg d)) (← ib n)

end Enc

open Enc

/-- `pp`, map and opcode of each two-operand SSE instruction (SDM Vol. 2,
by mnemonic: `66 0F 6F` MOVDQA, `66 0F FE` PADDD, …, `66 0F 38 00` PSHUFB,
`NP 0F 38 CC` SHA256MSG1, …). -/
def XBinOp.opc : XBinOp → Nat × Nat × Nat
  | .movdqa => (1, 1, 0x6F) | .paddd => (1, 1, 0xFE) | .pxor => (1, 1, 0xEF)
  | .por => (1, 1, 0xEB) | .punpckldq => (1, 1, 0x62) | .punpckhdq => (1, 1, 0x6A)
  | .punpcklqdq => (1, 1, 0x6C) | .punpckhqdq => (1, 1, 0x6D) | .pshufb => (1, 2, 0x00)
  | .sha256msg1 => (0, 2, 0xCC) | .sha256msg2 => (0, 2, 0xCD) | .sha1msg1 => (0, 2, 0xC9)
  | .sha1msg2 => (0, 2, 0xCA) | .sha1nexte => (0, 2, 0xC8) | .pand => (1, 1, 0xDB)
  | .pandn => (1, 1, 0xDF) | .paddq => (1, 1, 0xD4) | .psubq => (1, 1, 0xFB)
  | .pmuludq => (1, 1, 0xF4) | .paddw => (1, 1, 0xFD) | .psubw => (1, 1, 0xF9)
  | .psubd => (1, 1, 0xFA) | .pmullw => (1, 1, 0xD5) | .pmulhw => (1, 1, 0xE5)
  | .packssdw => (1, 1, 0x6B) | .punpcklwd => (1, 1, 0x61) | .punpckhwd => (1, 1, 0x69)
  | .pmaddwd => (1, 1, 0xF5) | .pmulhrsw => (1, 2, 0x0B) | .pcmpgtw => (1, 1, 0x65)
  | .packsswb => (1, 1, 0x63) | .aesenc => (1, 2, 0xDC) | .aesenclast => (1, 2, 0xDD)
  | .aesdec => (1, 2, 0xDE) | .aesdeclast => (1, 2, 0xDF) | .aesimc => (1, 2, 0xDB)
  | .pcmpeqd => (1, 1, 0x76)

/-- The opcode and `/digit` of each shift by an immediate (`66 0F 71`, `72`,
`73`): "PSLLW/PSLLD/PSLLQ" (`/6`), "PSRLW/PSRLD/PSRLQ" (`/2`),
"PSRAW/PSRAD" (`/4`), "PSLLDQ" (`73 /7`), "PSRLDQ" (`73 /3`). -/
def XShiftOp.opc : XShiftOp → Nat × Nat
  | .psllw => (0x71, 6) | .psrlw => (0x71, 2) | .psraw => (0x71, 4)
  | .pslld => (0x72, 6) | .psrld => (0x72, 2) | .psrad => (0x72, 4)
  | .psllq => (0x73, 6) | .psrlq => (0x73, 2) | .pslldq => (0x73, 7) | .psrldq => (0x73, 3)

/-- The bytes of a legacy SSE instruction. -/
def XOp.encode : XOp → Option (List Nat)
  | .bin op d s => let (pp, map, o) := op.opc; sse pp map o (xreg d) (.reg (xreg s))
  | .shift op d n => let (o, digit) := op.opc; sse 1 1 o digit (.reg (xreg d)) [n.toNat]
  -- "PSHUFD" (`66 0F 70 /r ib`), "PALIGNR" (`66 0F 3A 0F /r ib`), "PBLENDW"
  -- (`66 0F 3A 0E /r ib`), "SHA256RNDS2" (`NP 0F 38 CB /r`), "SHA1RNDS4"
  -- (`NP 0F 3A CC /r ib`), "MOVQ" (`66 REX.W 0F 6E /r`), "AESKEYGENASSIST"
  -- (`66 0F 3A DF /r ib`), "PCLMULQDQ" (`66 0F 3A 44 /r ib`).
  | .pshufd d s o => sse 1 1 0x70 (xreg d) (.reg (xreg s)) [o.toNat]
  | .palignr d s n => sse 1 3 0x0F (xreg d) (.reg (xreg s)) [n.toNat]
  | .pblendw d s n => sse 1 3 0x0E (xreg d) (.reg (xreg s)) [n.toNat]
  | .sha256rnds2 d s => sse 0 2 0xCB (xreg d) (.reg (xreg s))
  | .sha1rnds4 d s n => sse 0 3 0xCC (xreg d) (.reg (xreg s)) [n.toNat]
  | .movq d r => sse 1 1 0x6E (xreg d) (.reg (reg r)) (w := true)
  | .aeskeygenassist d s n => sse 1 3 0xDF (xreg d) (.reg (xreg s)) [n.toNat]
  | .pclmulqdq d s n => sse 1 3 0x44 (xreg d) (.reg (xreg s)) [n.toNat]

/-- `pp`, map and opcode of each three-operand AVX instruction (the VEX
forms of `XBinOp.opc`'s: SDM Vol. 2, `VEX.128/256.66.0F.WIG FE /r` VPADDD,
…), and whether it is commutative (see the module docs). -/
def VBinOp.opc : VBinOp → Nat × Nat × Nat × Bool
  | .vpaddd => (1, 1, 0xFE, true) | .vpaddq => (1, 1, 0xD4, true) | .vpxor => (1, 1, 0xEF, true)
  | .vpor => (1, 1, 0xEB, true) | .vpand => (1, 1, 0xDB, true) | .vpandn => (1, 1, 0xDF, false)
  | .vpshufb => (1, 2, 0x00, false) | .vpmuludq => (1, 1, 0xF4, true)
  | .vpunpckldq => (1, 1, 0x62, false) | .vpunpckhdq => (1, 1, 0x6A, false)
  | .vpunpcklqdq => (1, 1, 0x6C, false) | .vpunpckhqdq => (1, 1, 0x6D, false)
  | .vpaddw => (1, 1, 0xFD, true) | .vpsubw => (1, 1, 0xF9, false)
  | .vpsubd => (1, 1, 0xFA, false) | .vpmullw => (1, 1, 0xD5, true)
  | .vpmulhw => (1, 1, 0xE5, true) | .vpackssdw => (1, 1, 0x6B, false)
  | .vpunpcklwd => (1, 1, 0x61, false) | .vpunpckhwd => (1, 1, 0x69, false)
  | .vpmaddwd => (1, 1, 0xF5, true) | .vpmulhrsw => (1, 2, 0x0B, false)
  | .vpcmpgtw => (1, 1, 0x65, false) | .vpacksswb => (1, 1, 0x63, false)
  | .vpsubq => (1, 1, 0xFB, false) | .vaesenc => (1, 2, 0xDC, false)
  | .vaesenclast => (1, 2, 0xDD, false) | .vaesdec => (1, 2, 0xDE, false)
  | .vaesdeclast => (1, 2, 0xDF, false) | .vpcmpeqd => (1, 1, 0x76, true)

/-- `op dst, src1, src2` of a VEX instruction of `pp`, `map` and opcode `o`
between registers 0–15, its sources swapped when it is commutative and that
fits the two-byte prefix (see the module docs). -/
def vexBin (pp map o : Nat) (comm : Bool) (l d a b : Nat) : Option (List Nat) :=
  if comm && map == 1 && a < 8 && 8 ≤ b then vex pp map false l b o d (.reg a)
  else vex pp map false l a o d (.reg b)

/-- `vmovq xmm1, xmm2` (`VEX.128.F3.0F.WIG 7E /r`, or its store form
`VEX.128.66.0F.WIG D6 /r` when only `xmm2` is one of 8–15, see the module
docs). -/
def vexMovq (d s : Nat) : Option (List Nat) :=
  if d < 8 && 8 ≤ s then vex 1 1 false 0 0 0xD6 s (.reg d) else vex 2 1 false 0 0 0x7E d (.reg s)

/-- The bytes of an AVX instruction: VEX, but `vpmadd52luq`, `vpmadd52huq`,
`vprold`, `vpternlogd` and `vprorq`, which have only EVEX forms in the
model (`Avx.lean`). -/
def VOp.encode : VOp → Option (List Nat)
  | .vbin op l d a b =>
    let (pp, map, o, comm) := op.opc; vexBin pp map o comm (len l) (xreg d) (xreg a) (xreg b)
  -- "PCLMULQDQ" (`VEX.66.0F3A.WIG 44 /r ib`).
  | .vpclmulqdq l d a b n => vex 1 3 false (len l) (xreg a) 0x44 (xreg d) (.reg (xreg b)) [n.toNat]
  -- "MOVDQA" (`VEX.66.0F.WIG 6F /r`, its store form `7F /r`).
  | .vmovdqa l d s =>
    if xreg d < 8 && 8 ≤ xreg s then vex 1 1 false (len l) 0 0x7F (xreg s) (.reg (xreg d))
    else vex 1 1 false (len l) 0 0x6F (xreg d) (.reg (xreg s))
  -- The shifts by an immediate (`VEX.66.0F.WIG 71`/`72`/`73 /digit ib`,
  -- `vvvv` the destination).
  | .vshift op l d s n =>
    let (o, digit) := op.opc; vex 1 1 false (len l) (xreg d) o digit (.reg (xreg s)) [n.toNat]
  -- "PSHUFD" (`VEX.66.0F.WIG 70 /r ib`), "PALIGNR" (`VEX.66.0F3A.WIG 0F /r
  -- ib`), "VPBLENDD" (`VEX.66.0F3A.W0 02 /r ib`), "PBLENDW" (`VEX.66.0F3A.WIG
  -- 0E /r ib`).
  | .vpshufd l d s o => vex 1 1 false (len l) 0 0x70 (xreg d) (.reg (xreg s)) [o.toNat]
  | .vpalignr l d a b n => vex 1 3 false (len l) (xreg a) 0x0F (xreg d) (.reg (xreg b)) [n.toNat]
  | .vpblendd l d a b n => vex 1 3 false (len l) (xreg a) 0x02 (xreg d) (.reg (xreg b)) [n.toNat]
  | .vpblendw l d a b n => vex 1 3 false (len l) (xreg a) 0x0E (xreg d) (.reg (xreg b)) [n.toNat]
  -- "VPSLLVD/VPSLLVQ" (`VEX.66.0F38.W0`/`W1 47 /r`), "VPSRLVD/VPSRLVQ"
  -- (`VEX.66.0F38.W0`/`W1 45 /r`).
  | .vvar op l d a b =>
    let (o, w) := match op with
      | .vpsllvd => (0x47, false) | .vpsllvq => (0x47, true)
      | .vpsrlvd => (0x45, false) | .vpsrlvq => (0x45, true)
    vex 1 2 w (len l) (xreg a) o (xreg d) (.reg (xreg b))
  -- "VPBROADCAST" (`VEX.66.0F38.W0 58 /r`, `59 /r`).
  | .vpbroadcastd l d s => vex 1 2 false (len l) 0 0x58 (xreg d) (.reg (xreg s))
  | .vpbroadcastq l d s => vex 1 2 false (len l) 0 0x59 (xreg d) (.reg (xreg s))
  -- "VPERMQ" (`VEX.256.66.0F3A.W1 00 /r ib`), "VPERMD" (`VEX.256.66.0F38.W0
  -- 36 /r`), "VPERM2I128" (`VEX.256.66.0F3A.W0 46 /r ib`), "VINSERTI128"
  -- (`VEX.256.66.0F3A.W0 38 /r ib`), "VEXTRACTI128" (`VEX.256.66.0F3A.W0 39
  -- /r ib`, the destination in `r/m`), "MOVQ" (`VEX.128.66.0F.W1 6E /r`),
  -- "VZEROUPPER" (`VEX.128.0F.WIG 77`).
  | .vpermq d s o => vex 1 3 true 1 0 0x00 (xreg d) (.reg (xreg s)) [o.toNat]
  | .vpermd d i s => vex 1 2 false 1 (xreg i) 0x36 (xreg d) (.reg (xreg s))
  | .vperm2i128 d a b n => vex 1 3 false 1 (xreg a) 0x46 (xreg d) (.reg (xreg b)) [n.toNat]
  | .vinserti128 d a b n => vex 1 3 false 1 (xreg a) 0x38 (xreg d) (.reg (xreg b)) [n.toNat]
  | .vextracti128 d s n => vex 1 3 false 1 0 0x39 (xreg s) (.reg (xreg d)) [n.toNat]
  | .vmovq d r => vex 1 1 true 0 0 0x6E (xreg d) (.reg (reg r))
  | .vzeroupper => some [0xC5, 0xF8, 0x77]
  -- "VSHA512RNDS2" (`VEX.256.F2.0F38.W0 CB /r`), "VSHA512MSG1" (`CC /r`),
  -- "VSHA512MSG2" (`CD /r`).
  | .vsha512rnds2 d a b => vex 3 2 false 1 (xreg a) 0xCB (xreg d) (.reg (xreg b))
  | .vsha512msg1 d s => vex 3 2 false 1 0 0xCC (xreg d) (.reg (xreg s))
  | .vsha512msg2 d s => vex 3 2 false 1 0 0xCD (xreg d) (.reg (xreg s))
  -- "VPMADD52LUQ" (`EVEX.66.0F38.W1 B4 /r`), "VPMADD52HUQ" (`B5 /r`),
  -- "VPROLD" (`EVEX.66.0F.W0 72 /1 ib`, `vvvv` the destination),
  -- "VPTERNLOGD" (`EVEX.66.0F3A.W0 25 /r ib`), "VPRORQ" (`EVEX.66.0F.W1 72
  -- /0 ib`).
  | .vpmadd52luq l d a b => evex 1 2 true (len l) (xreg a) 0xB4 (xreg d) (.reg (xreg b))
  | .vpmadd52huq l d a b => evex 1 2 true (len l) (xreg a) 0xB5 (xreg d) (.reg (xreg b))
  | .vprold l d s n => evex 1 1 false (len l) (xreg d) 0x72 1 (.reg (xreg s)) (imm := [n.toNat])
  | .vpternlogd l d a b n =>
    evex 1 3 false (len l) (xreg a) 0x25 (xreg d) (.reg (xreg b)) (imm := [n.toNat])
  | .vprorq l d s n => evex 1 1 true (len l) (xreg d) 0x72 0 (.reg (xreg s)) (imm := [n.toNat])

/-- Map, opcode and `W` of each `EVEX.512.66` instruction of `ZBinOp`
(SDM Vol. 2: `0F.W0 FE` VPADDD, `0F.W0 EF` VPXORD, `0F.W0 62`/`6A`
VPUNPCKLDQ/VPUNPCKHDQ, `0F.W1 6C`/`6D` VPUNPCKLQDQ/VPUNPCKHQDQ, `0F.W1 D4`
VPADDQ, `0F.W1 F4` VPMULUDQ, `0F.W1 DB` VPANDQ, `0F.W1 EB` VPORQ, `0F.W1
DF` VPANDNQ, `0F38.WIG DC`–`DF` VAESENC, VAESENCLAST, VAESDEC,
VAESDECLAST, `0F38.WIG 00` VPSHUFB, `0F.W1 FB` VPSUBQ). -/
def ZBinOp.opc : ZBinOp → Nat × Nat × Bool
  | .vpaddd => (1, 0xFE, false) | .vpxord => (1, 0xEF, false)
  | .vpunpckldq => (1, 0x62, false) | .vpunpckhdq => (1, 0x6A, false)
  | .vpunpcklqdq => (1, 0x6C, true) | .vpunpckhqdq => (1, 0x6D, true)
  | .vpaddq => (1, 0xD4, true) | .vpmuludq => (1, 0xF4, true) | .vpandq => (1, 0xDB, true)
  | .vporq => (1, 0xEB, true) | .vpandnq => (1, 0xDF, true)
  | .vaesenc => (2, 0xDC, false) | .vaesenclast => (2, 0xDD, false)
  | .vaesdec => (2, 0xDE, false) | .vaesdeclast => (2, 0xDF, false)
  | .vpshufb => (2, 0x00, false) | .vpsubq => (1, 0xFB, true)

/-- The bytes of an `EVEX.512` instruction between registers. -/
def ZOp.encode : ZOp → Option (List Nat)
  | .zbin op d a b => let (map, o, w) := op.opc; evex 1 map w 2 (xreg a) o (xreg d) (.reg (xreg b))
  -- `ZKeyOp`: `0F.W0 EF` VPXORD, `0F38.WIG DC`/`DD` VAESENC/VAESENCLAST,
  -- `0F.W0 FE` VPADDD.
  | .zbinH op d a b =>
    let (map, o) := match op with
      | .vpxord => (1, 0xEF) | .vaesenc => (2, 0xDC) | .vaesenclast => (2, 0xDD)
      | .vpaddd => (1, 0xFE)
    evex 1 map false 2 (xreg a) o (xreg d) (.reg (hreg b))
  -- "PCLMULQDQ" (`EVEX.512.66.0F3A.WIG 44 /r ib`), "VPROLD" (`0F.W0 72 /1
  -- ib`), "PSHUFD" (`0F.W0 70 /r ib`), "VSHUFI32X4" (`0F3A.W0 43 /r ib`),
  -- "PSLLQ"/"PSRLQ" (`0F.W1 73 /6`, `/2 ib`), "PSLLDQ"/"PSRLDQ" (`0F.WIG 73
  -- /7`, `/3 ib`), "VPBROADCASTQ" (`0F38.W1 59 /r`), "VMOVDQA64" (`0F.W1 6F
  -- /r`), "VPTERNLOGD" (`0F3A.W0 25 /r ib`), "VPRORQ" (`0F.W1 72 /0 ib`),
  -- "VPERMQ" (`0F3A.W1 00 /r ib`), "VPMADD52LUQ"/"VPMADD52HUQ" (`0F38.W1
  -- B4`/`B5 /r`).
  | .vpclmulqdq d a b n => evex 1 3 false 2 (xreg a) 0x44 (xreg d) (.reg (xreg b)) (imm := [n.toNat])
  | .vprold d s n => evex 1 1 false 2 (xreg d) 0x72 1 (.reg (xreg s)) (imm := [n.toNat])
  | .vpshufd d s o => evex 1 1 false 2 0 0x70 (xreg d) (.reg (xreg s)) (imm := [o.toNat])
  | .vshufi32x4 d a b n => evex 1 3 false 2 (xreg a) 0x43 (xreg d) (.reg (xreg b)) (imm := [n.toNat])
  | .vshift op d s n =>
    let digit := match op with | .vpsllq => 6 | .vpsrlq => 2
    evex 1 1 true 2 (xreg d) 0x73 digit (.reg (xreg s)) (imm := [n.toNat])
  | .vpslldq d s n => evex 1 1 false 2 (xreg d) 0x73 7 (.reg (xreg s)) (imm := [n.toNat])
  | .vpsrldq d s n => evex 1 1 false 2 (xreg d) 0x73 3 (.reg (xreg s)) (imm := [n.toNat])
  | .vpbroadcastq d s => evex 1 2 true 2 0 0x59 (xreg d) (.reg (xreg s))
  | .vmovdqa64 d s => evex 1 1 true 2 0 0x6F (xreg d) (.reg (xreg s))
  | .vpternlogd d a b n => evex 1 3 false 2 (xreg a) 0x25 (xreg d) (.reg (xreg b)) (imm := [n.toNat])
  | .vprorq d s n => evex 1 1 true 2 (xreg d) 0x72 0 (.reg (xreg s)) (imm := [n.toNat])
  | .vpermq d s o => evex 1 3 true 2 0 0x00 (xreg d) (.reg (xreg s)) (imm := [o.toNat])
  | .vpmadd52 hi d a b => evex 1 2 true 2 (xreg a) (if hi then 0xB5 else 0xB4) (xreg d) (.reg (xreg b))
  -- "VPERMB/VPERMW/VPERMD/VPERMQ" (`EVEX.512.66.0F38.W1 8D /r`: `zmm1` in
  -- `reg`, the indices `zmm2` in `vvvv`, `zmm3` in `r/m`), "VPSRLVW"
  -- (`EVEX.512.66.0F38.W1 10 /r`), and "VEXTRACTI32x4"
  -- (`EVEX.512.66.0F3A.W0 39 /r ib`: the source `zmm2` in `reg`, the
  -- destination `xmm1` in `r/m`).
  | .vpermw d a b => evex 1 2 true 2 (xreg a) 0x8D (xreg d) (.reg (xreg b))
  | .vpsrlvw d a b => evex 1 2 true 2 (xreg a) 0x10 (xreg d) (.reg (xreg b))
  | .vextracti32x4 d s n => evex 1 3 false 2 0 0x39 (xreg s) (.reg (xreg d)) (imm := [n.toNat])

/-- Whether a register of `Evex.lean` is one of `xmm0`–`xmm15`. -/
def VReg.isLo : VReg → Bool
  | .lo _ => true
  | .hi _ => false

/-- The bytes of an instruction of `Evex.lean`: with VEX if all its
registers are in `xmm0`–`xmm15` and it has a VEX form (see the module
docs), else with EVEX (`EVEX.256`, `EVEX.128` for `vmovq`). -/
def EOp.encode : EOp → Option (List Nat)
  -- "PADDQ" (`VEX.256.66.0F.WIG D4 /r`, `EVEX.256.66.0F.W1 D4 /r`), "PSUBQ"
  -- (`VEX.256.66.0F.WIG FB /r`, `EVEX.256.66.0F.W1 FB /r`), "PXOR"
  -- (`EVEX.256.66.0F.W1 EF /r`, VPXORQ), "PAND" (`DB`, VPANDQ), "POR" (`EB`,
  -- VPORQ).
  | .bin op d a b =>
    match op with
    | .vpaddq =>
      if d.isLo && a.isLo && b.isLo then vexBin 1 1 0xD4 true 1 (vreg d) (vreg a) (vreg b)
      else evex 1 1 true 1 (vreg a) 0xD4 (vreg d) (.reg (vreg b))
    | .vpsubq =>
      if d.isLo && a.isLo && b.isLo then vexBin 1 1 0xFB false 1 (vreg d) (vreg a) (vreg b)
      else evex 1 1 true 1 (vreg a) 0xFB (vreg d) (.reg (vreg b))
    | .vpxorq => evex 1 1 true 1 (vreg a) 0xEF (vreg d) (.reg (vreg b))
    | .vpandq => evex 1 1 true 1 (vreg a) 0xDB (vreg d) (.reg (vreg b))
    | .vporq => evex 1 1 true 1 (vreg a) 0xEB (vreg d) (.reg (vreg b))
  -- "PSLLQ"/"PSRLQ" (`VEX.256.66.0F.WIG 73 /6`, `/2 ib`; `EVEX.256.66.0F.W1`).
  | .shift op d s n =>
    let digit := match op with | .vpsllq => 6 | .vpsrlq => 2
    if d.isLo && s.isLo then vex 1 1 false 1 (vreg d) 0x73 digit (.reg (vreg s)) [n.toNat]
    else evex 1 1 true 1 (vreg d) 0x73 digit (.reg (vreg s)) (imm := [n.toNat])
  -- "VPERMQ" (`VEX.256.66.0F3A.W1 00 /r ib`, `EVEX.256.66.0F3A.W1`).
  | .vpermq d s o =>
    if d.isLo && s.isLo then vex 1 3 true 1 0 0x00 (vreg d) (.reg (vreg s)) [o.toNat]
    else evex 1 3 true 1 0 0x00 (vreg d) (.reg (vreg s)) (imm := [o.toNat])
  -- "VALIGNQ" (`EVEX.256.66.0F3A.W1 03 /r ib`).
  | .valignq d a b n => evex 1 3 true 1 (vreg a) 0x03 (vreg d) (.reg (vreg b)) (imm := [n.toNat])
  -- "VPBROADCASTQ" (`VEX.256.66.0F38.W0 59 /r`, `EVEX.256.66.0F38.W1`).
  | .vpbroadcastq d s =>
    if d.isLo && s.isLo then vex 1 2 false 1 0 0x59 (vreg d) (.reg (vreg s))
    else evex 1 2 true 1 0 0x59 (vreg d) (.reg (vreg s))
  -- "MOVQ" (`VEX.128.66.0F.W1 6E /r`, `EVEX.128.66.0F.W1 6E /r`; between
  -- registers `VEX.128.F3.0F.WIG 7E /r`, `EVEX.128.F3.0F.W1 7E /r`).
  | .vmovq d r =>
    if d.isLo then vex 1 1 true 0 0 0x6E (vreg d) (.reg (reg r))
    else evex 1 1 true 0 0 0x6E (vreg d) (.reg (reg r))
  | .vmovqx d s =>
    if d.isLo && s.isLo then vexMovq (vreg d) (vreg s)
    else evex 2 1 true 0 0 0x7E (vreg d) (.reg (vreg s))
  -- "VPMADD52LUQ"/"VPMADD52HUQ" (`EVEX.256.66.0F38.W1 B4`/`B5 /r`),
  -- "VPTERNLOGQ" (`EVEX.256.66.0F3A.W1 25 /r ib`), "VPRORQ"
  -- (`EVEX.256.66.0F.W1 72 /0 ib`).
  | .vpmadd52 hi d a b => evex 1 2 true 1 (vreg a) (if hi then 0xB5 else 0xB4) (vreg d) (.reg (vreg b))
  | .vpternlogq d a b n => evex 1 3 true 1 (vreg a) 0x25 (vreg d) (.reg (vreg b)) (imm := [n.toNat])
  | .vprorq d s n => evex 1 1 true 1 (vreg d) 0x72 0 (.reg (vreg s)) (imm := [n.toNat])
  -- "VPSRAQ" (`EVEX.256.66.0F.W1 72 /4 ib`), "VMOVDQA64"
  -- (`EVEX.256.66.0F.W1 6F /r`).
  | .vpsraq d s n => evex 1 1 true 1 (vreg d) 0x72 4 (.reg (vreg s)) (imm := [n.toNat])
  | .vmovdqa64 d s => evex 1 1 true 1 0 0x6F (vreg d) (.reg (vreg s))

/-- The bytes of an `EVEX.512` instruction (`EVEX.L'L = 10`). -/
def E5Op.encode : E5Op → Option (List Nat)
  -- "PADDQ" (`EVEX.512.66.0F.W1 D4 /r`), "PSUBQ" (`EVEX.512.66.0F.W1 FB
  -- /r`), "PXOR" (`EVEX.512.66.0F.W1 EF /r`,
  -- VPXORQ), "PAND" (`DB`, VPANDQ), "POR" (`EB`, VPORQ).
  | .bin op d a b =>
    let o := match op with | .vpaddq => 0xD4 | .vpsubq => 0xFB | .vpxorq => 0xEF | .vpandq => 0xDB | .vporq => 0xEB
    evex 1 1 true 2 (vreg a) o (vreg d) (.reg (vreg b))
  -- "PSLLQ"/"PSRLQ" (`EVEX.512.66.0F.W1 73 /6`, `/2 ib`).
  | .shift op d s n =>
    let digit := match op with | .vpsllq => 6 | .vpsrlq => 2
    evex 1 1 true 2 (vreg d) 0x73 digit (.reg (vreg s)) (imm := [n.toNat])
  -- "VPERMQ" (`EVEX.512.66.0F3A.W1 00 /r ib`).
  | .vpermq d s o => evex 1 3 true 2 0 0x00 (vreg d) (.reg (vreg s)) (imm := [o.toNat])
  -- "VPMADD52LUQ"/"VPMADD52HUQ" (`EVEX.512.66.0F38.W1 B4`/`B5 /r`).
  | .vpmadd52 hi d a b => evex 1 2 true 2 (vreg a) (if hi then 0xB5 else 0xB4) (vreg d) (.reg (vreg b))
  -- "VINSERTI64X4" (`EVEX.512.66.0F3A.W1 3A /r ib`).
  | .vinserti64x4 d a b n => evex 1 3 true 2 (vreg a) 0x3A (vreg d) (.reg (vreg b)) (imm := [n.toNat])

/-- The bytes of each instruction `Instr.asm` (`Print.lean`) names, in
order; `none` if an operand does not fit its field (see the module docs),
or for `leaSym`, which is text. -/
def Instr.encode : Instr → Option (List (List Nat))
  -- "MOV": `REX.W 89 /r` between registers, `REX.W C7 /0 id`, `REX.W 8B /r`
  -- (a load), `REX.W 89 /r` (a store); without `REX.W` 32-bit, and
  -- `B8+rd id`.
  | .mov d (.reg s) => (legacy [] true [0x89] (reg s) (.reg (reg d))).map ([·])
  | .mov d (.imm v) => (legacy [] true [0xC7] 0 (.reg (reg d)) (le 4 v.toNat)).map ([·])
  | .mov d (.mem m) => (legacy [] true [0x8B] (reg d) (.mem m)).map ([·])
  | .store m r => (legacy [] true [0x89] (reg r) (.mem m)).map ([·])
  | .mov32 d (.reg s) => (legacy [] false [0x89] (reg s) (.reg (reg d))).map ([·])
  | .mov32 d (.imm v) => some [plusReg false [] 0xB8 (reg d) (le 4 v.toNat)]
  | .mov32 d (.mem m) => (legacy [] false [0x8B] (reg d) (.mem m)).map ([·])
  | .store32 m r => (legacy [] false [0x89] (reg r) (.mem m)).map ([·])
  -- The ALU instructions (`Enc.alu`).
  | .alu op d s => (Enc.alu true op d s).map ([·])
  | .aluTbl op d m .. => (Enc.alu true op d (.mem m)).map ([·])
  | .alu32 op d s => (Enc.alu false op d s).map ([·])
  | .shift32 op d n => (Enc.shift false op d n).map ([·])
  | .shift op d n => (Enc.shift true op d n).map ([·])
  -- "BSWAP" (`0F C8+rd`, `REX.W 0F C8+rd`).
  | .bswap32 d => some [plusReg false [0x0F] 0xC8 (reg d)]
  | .bswap d => some [plusReg true [0x0F] 0xC8 (reg d)]
  -- "RORX" (`VEX.LZ.F2.0F3A.W0`/`W1 F0 /r ib`), "ANDN" (`VEX.LZ.0F38.W0`/`W1
  -- F2 /r`).
  | .rorx32 d s n => do return [← vex 3 3 false 0 0 0xF0 (reg d) (.reg (reg s)) (← ib n)]
  | .rorx d s n => do return [← vex 3 3 true 0 0 0xF0 (reg d) (.reg (reg s)) (← ib n)]
  | .andn32 d a b => (vex 0 2 false 0 (reg a) 0xF2 (reg d) (.reg (reg b))).map ([·])
  | .andn d a b => (vex 0 2 true 0 (reg a) 0xF2 (reg d) (.reg (reg b))).map ([·])
  -- "MOVZX" (`0F B6 /r`, `0F B7 /r`), "MOV" (`88 /r`, a byte store, with REX
  -- to name `SPL`–`DIL`; `66 89 /r`, a word store).
  | .movzx8 d m => (legacy [] false [0x0F, 0xB6] (reg d) (.mem m)).map ([·])
  | .movzx16 d m => (legacy [] false [0x0F, 0xB7] (reg d) (.mem m)).map ([·])
  | .store8 m r =>
    (legacy [] false [0x88] (reg r) (.mem m) (rex := 4 ≤ reg r && reg r < 8)).map ([·])
  | .store16 m r => (legacy [0x66] false [0x89] (reg r) (.mem m)).map ([·])
  -- "SAL/SAR/SHL/SHR" by `CL` (`REX.W D3 /4`, `/7`, `/5`).
  | .shiftCl op d =>
    let digit := match op with | .shl => 4 | .shr => 5 | .sar => 7
    (legacy [] true [0xD3] digit (.reg (reg d))).map ([·])
  -- "SHLX/SHRX" (`VEX.LZ.66.0F38.W1 F7 /r`, `VEX.LZ.F2.0F38.W1 F7 /r`, `vvvv`
  -- the count).
  | .shiftx op d s c =>
    let pp := match op with | .shlx => 1 | .shrx => 3
    (vex pp 2 true 0 (reg c) 0xF7 (reg d) (.reg (reg s))).map ([·])
  -- "MOV" (`REX.W B8+rd io`).
  | .movImm64 d v => some [plusReg true [] 0xB8 (reg d) (le 8 v.toNat)]
  | .leaSym .. => none
  -- "MOVDQU" (`F3 0F 6F /r`, `F3 0F 7F /r`), "MOVQ" (`66 REX.W 0F 7E /r`, the
  -- general-purpose register in `r/m`).
  | .movdquLoad d m => (sse 2 1 0x6F (xreg d) (.mem m)).map ([·])
  | .movdquStore m r => (sse 2 1 0x7F (xreg r) (.mem m)).map ([·])
  | .movdquTbl d m .. => (sse 2 1 0x6F (xreg d) (.mem m)).map ([·])
  | .movqR d r => (sse 1 1 0x7E (xreg r) (.reg (reg d)) (w := true)).map ([·])
  | .xop op => op.encode.map ([·])
  | .vop op => op.encode.map ([·])
  -- "MOVDQU" (`VEX.F3.0F.WIG 6F /r`, `7F /r`), "VBROADCASTI128"
  -- (`VEX.256.66.0F38.W0 5A /r`), the memory forms of `VBinOp.opc`'s, "PMOVMSKB"
  -- (`VEX.66.0F.WIG D7 /r`).
  | .vmovdquLoad l d m => (vex 2 1 false (len l) 0 0x6F (xreg d) (.mem m)).map ([·])
  | .vmovdquStore l m r => (vex 2 1 false (len l) 0 0x7F (xreg r) (.mem m)).map ([·])
  | .vmovdquTbl d m .. => (vex 2 1 false 1 0 0x6F (xreg d) (.mem m)).map ([·])
  | .vbroadcasti128 d m => (vex 1 2 false 1 0 0x5A (xreg d) (.mem m)).map ([·])
  | .vbinLoad op l d a m =>
    let (pp, map, o, _) := op.opc; (vex pp map false (len l) (xreg a) o (xreg d) (.mem m)).map ([·])
  | .vpmovmskb l d r => (vex 1 1 false (len l) 0 0xD7 (reg d) (.reg (xreg r))).map ([·])
  | .zop op => op.encode.map ([·])
  -- "MOVDQU32" (`EVEX.512.F3.0F.W0 6F /r`, `7F /r`), "VBROADCASTI32X4"
  -- (`EVEX.512.66.0F38.W0 5A /r`, Tuple4: `N = 16`), the broadcast forms of
  -- VPMULUDQ, VPANDQ, VPORQ (`EVEX.512.66.0F.W1 F4`, `DB`, `EB /r`, `b = 1`,
  -- `N = 8`), "VPBROADCASTD" (`EVEX.512.66.0F38.W0 58 /r`, Tuple1 Scalar:
  -- `N = 4`), the broadcast form of VPADDD (`EVEX.512.66.0F.W0 FE /r`, `b =
  -- 1`, `N = 4`), the memory forms of VPMADD52LUQ/VPMADD52HUQ
  -- (`EVEX.256.66.0F38.W1 B4`/`B5 /r`, Full: `N = 32`).
  | .vmovdqu32Load d m => (evex 2 1 false 2 0 0x6F (xreg d) (.mem m) 64).map ([·])
  | .vmovdqu32Store m r => (evex 2 1 false 2 0 0x7F (xreg r) (.mem m) 64).map ([·])
  | .vbroadcasti32x4 d m => (evex 1 2 false 2 0 0x5A (xreg d) (.mem m) 16).map ([·])
  | .vbroadcasti32x4H d m => (evex 1 2 false 2 0 0x5A (hreg d) (.mem m) 16).map ([·])
  | .zbcst op d a m =>
    let o := match op with | .vpmuludq => 0xF4 | .vpandq => 0xDB | .vporq => 0xEB
    (evex 1 1 true 2 (xreg a) o (xreg d) (.mem m) 8 (b := true)).map ([·])
  | .vpbroadcastdZ d m => (evex 1 2 false 2 0 0x58 (xreg d) (.mem m) 4).map ([·])
  | .zbcstd .vpaddd d a m => (evex 1 1 false 2 (xreg a) 0xFE (xreg d) (.mem m) 4 (b := true)).map ([·])
  | .vpmadd52Load hi d a m =>
    (evex 1 2 true 1 (xreg a) (if hi then 0xB5 else 0xB4) (xreg d) (.mem m) 32).map ([·])
  | .eop op => op.encode.map ([·])
  -- "MOVDQU64" (`EVEX.256.F3.0F.W1 6F /r`, `7F /r`, Full Mem: `N = 32`).
  | .evLoad d m => (evex 2 1 true 1 0 0x6F (vreg d) (.mem m) 32).map ([·])
  | .evStore m r => (evex 2 1 true 1 0 0x7F (vreg r) (.mem m) 32).map ([·])
  | .evMadd52Load hi d a m =>
    (evex 1 2 true 1 (vreg a) (if hi then 0xB5 else 0xB4) (vreg d) (.mem m) 32).map ([·])
  | .e5op op => op.encode.map ([·])
  -- "VPBROADCASTQ" (`EVEX.256.66.0F38.W1 59 /r`, Tuple1 Scalar: `N = 8`).
  | .evBroadcastLoad d m => (evex 1 2 true 1 0 0x59 (vreg d) (.mem m) 8).map ([·])
  -- "VINSERTI64X4" (`EVEX.512.66.0F3A.W1 3A /r ib`) and "VEXTRACTI64X4"
  -- (`EVEX.512.66.0F3A.W1 3B /r ib`, the register in `ModRM.reg`), Tuple4:
  -- `N = 32`.
  | .e5InsertLoad d a m n =>
    (evex 1 3 true 2 (vreg a) 0x3A (vreg d) (.mem m) 32 (imm := [n.toNat])).map ([·])
  | .e5ExtractStore m r n =>
    (evex 1 3 true 2 0 0x3B (vreg r) (.mem m) 32 (imm := [n.toNat])).map ([·])
  -- "KMOVW" (`VEX.L0.0F.W0 92 /r`), "KMOVQ" (`VEX.L0.F2.0F.W1 92 /r`), into
  -- `k1`; then "MOVDQU64" (`EVEX.512.F3.0F.W1 6F`/`7F /r`) or "MOVDQU8"
  -- (`EVEX.512.F2.0F.W0 6F`/`7F /r`), masked by `k1` (`aaa = 001`), zeroing
  -- (`z = 1`) for the loads, `N = 64`.
  | .kLoad k d m => do
    return [← vex 0 1 false 0 0 0x92 1 (.reg (reg k)),
      ← evex 2 1 true 2 0 0x6F (xreg d) (.mem m) 64 (aaa := 1) (z := true)]
  | .kStore m k r => do
    return [← vex 0 1 false 0 0 0x92 1 (.reg (reg k)),
      ← evex 2 1 true 2 0 0x7F (xreg r) (.mem m) 64 (aaa := 1)]
  | .kLoad8 k d m => do
    return [← vex 3 1 true 0 0 0x92 1 (.reg (reg k)),
      ← evex 3 1 false 2 0 0x6F (xreg d) (.mem m) 64 (aaa := 1) (z := true)]
  | .kStore8 m k r => do
    return [← vex 3 1 true 0 0 0x92 1 (.reg (reg k)),
      ← evex 3 1 false 2 0 0x7F (xreg r) (.mem m) 64 (aaa := 1)]
  -- "VPCMPW/VPCMPUW" (`EVEX.512.66.0F3A.W1 3E /r ib`: `k1` in `reg`, `zmm2`
  -- in `vvvv`, `zmm3` in `r/m`), with the predicate `1`; then "KMOVD"
  -- (`VEX.L0.F2.0F.W0 93 /r`: the general-purpose register in `reg`, `k1`
  -- in `r/m`).
  | .vpcmpltuw d a b => do
    return [← evex 1 3 true 2 (xreg a) 0x3E 1 (.reg (xreg b)) (imm := [1]),
      ← vex 3 1 false 0 0 0x93 (reg d) (.reg 1)]
  -- "STMXCSR" (`NP 0F AE /3`), "LDMXCSR" (`NP 0F AE /2`), "LFENCE" (`NP 0F AE
  -- E8`).
  | .stmxcsr m => (legacy [] false [0x0F, 0xAE] 3 (.mem m)).map ([·])
  | .ldmxcsr m => (legacy [] false [0x0F, 0xAE] 2 (.mem m)).map ([·])
  | .lfence => some [[0x0F, 0xAE, 0xE8]]
  -- "MUL" (`REX.W F7 /4`), "IMUL" (`REX.W 0F AF /r`; `REX.W 6B /r ib`, `REX.W
  -- 69 /r id`), "SHLD" (`REX.W 0F A4 /r ib`, the destination in `r/m`),
  -- "BTR" (`REX.W 0F BA /6 ib`).
  | .mul r => (legacy [] true [0xF7] 4 (.reg (reg r))).map ([·])
  -- "CALL—Call Procedure": `FF /2`, "CALL r/m64", whose operand size is 64
  -- bits in 64-bit mode without `REX.W`.
  | .callr r => (legacy [] false [0xFF] 2 (.reg (reg r))).map ([·])
  | .imul d r => (legacy [] true [0x0F, 0xAF] (reg d) (.reg (reg r))).map ([·])
  | .imul3 d r v =>
    if fitsI8 v.toInt then (legacy [] true [0x6B] (reg d) (.reg (reg r)) [i8 v.toInt]).map ([·])
    else (legacy [] true [0x69] (reg d) (.reg (reg r)) (le 4 v.toNat)).map ([·])
  | .shld d r n => do return [← legacy [] true [0x0F, 0xA4] (reg r) (.reg (reg d)) (← ib n)]
  | .btr d n => do return [← legacy [] true [0x0F, 0xBA] 6 (.reg (reg d)) (← ib n)]
  -- "MULX" (`VEX.LZ.F2.0F38.W1 F6 /r`, `vvvv` the low half), "ADCX" (`66
  -- REX.W 0F 38 F6 /r`), "ADOX" (`F3 REX.W 0F 38 F6 /r`), "CMOVcc" (`REX.W 0F
  -- 42`, `43`, `44`, `45 /r`).
  | .mulx hi lo s => do return [← vex 3 2 true 0 (reg lo) 0xF6 (reg hi) (← src s)]
  | .adcx d s => do return [← legacy [0x66] true [0x0F, 0x38, 0xF6] (reg d) (← src s)]
  | .adox d s => do return [← legacy [0xF3] true [0x0F, 0x38, 0xF6] (reg d) (← src s)]
  | .cmov c d s => do
    let cc := match c with | .b => 2 | .ae => 3 | .e => 4 | .ne => 5
    return [← legacy [] true [0x0F, 0x40 + cc] (reg d) (← src s)]
  -- "PUSH" (`50+rd`), "POP" (`58+rd`), "LEA" (`REX.W 8D /r`) of `[rsp -
  -- bytes]`, `[rsp + bytes]`.
  | .push rs => some (rs.map fun r => plusReg false [] 0x50 (reg r))
  | .pop r k => some (List.replicate k (plusReg false [] 0x58 (reg r)))
  | .alloc bytes =>
    (legacy [] true [0x8D] (reg .rsp) (.mem { base := .rsp, disp := -(bytes : Int) })).map ([·])
  | .free bytes => (legacy [] true [0x8D] (reg .rsp) (.mem { base := .rsp, disp := bytes })).map ([·])

/-- `ret` ("RET", `C3`). -/
def retBytes : List Nat := [0xC3]

/-- `b` as two hexadecimal digits, after `0x`. -/
def hex8 (b : Nat) : String :=
  ("0x".push (Nat.digitChar (b % 256 / 16))).push (Nat.digitChar (b % 16))

/-- The assembler directive emitting the bytes `bs`: `.byte` of each, as
two hexadecimal digits, separated by commas alone (the form the emitter
joins and packs, `Rust.pushLine`). -/
def byteLine (bs : List Nat) : String := ".byte " ++ ",".intercalate (bs.map hex8)

end VG.X86_64
