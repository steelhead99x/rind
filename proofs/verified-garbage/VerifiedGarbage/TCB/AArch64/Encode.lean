module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Machine code of the AArch64 model's instructions

**Trusted.** The 32-bit encoding of each straight-line instruction of the
model (`Instr`), and of the return: what the printer (`Print.lean`) emits,
as `.inst <word>`, in place of the instruction's text, so that what runs is
these words, not the assembler's reading of a mnemonic. Branches (`cbz`,
`cbnz`, `b`), calls (`bl`), the address of a static (`adrp` and `add` of its
page offset, whose bytes the linker writes) and alignment (`.p2align`) are
still printed as text for the assembler and linker to lay out.

Each encoding is the one the Arm Architecture Reference Manual for A-profile
(DDI 0487) gives for the instruction the model's semantics describes, in
section C6.2 ("Alphabetical list of A64 base instructions") for the general
purpose ones and C7.2 ("Alphabetical list of A64 Advanced SIMD and
floating-point instructions") for the vector ones, by the name in each
definition's docs, with the SVE2 `XAR` of the SVE chapter (C8.2). Where an
alias is printed (`mov`, `tst`, `ror`, `lsl`, `lsr`, `mul`, `umull`, `not`)
the encoding is the instruction it stands for, as its section says ("This
instruction is an alias of …"). Every encoding is the one the assembler
gives the printed text: `ldr`, `str`, `ldrb`, `strb` with an offset are the
unsigned-offset forms (`LDR (immediate)`, … "Unsigned offset"), which the
model's semantics require, never `LDUR`; an `add`/`sub` immediate below
4096 is unshifted.

`encode` is `none` for an instruction whose operand does not fit its field,
which the printer reports as unencodable (`Printer.unencodable`) and the
emitter refuses (`Rust.checkEncodable`), rather than truncating it; and for
the instructions printed as text (`adrSym`, `align`).
-/

@[expose] public section

namespace VG.AArch64

/-- The number `n` of `x<n>`/`w<n>`. -/
def Reg.index : Reg → Nat
  | .x0 => 0 | .x1 => 1 | .x2 => 2 | .x3 => 3 | .x4 => 4 | .x5 => 5 | .x6 => 6 | .x7 => 7
  | .x8 => 8 | .x9 => 9 | .x10 => 10 | .x11 => 11 | .x12 => 12 | .x13 => 13 | .x14 => 14
  | .x15 => 15 | .x16 => 16 | .x17 => 17 | .x19 => 19 | .x20 => 20 | .x21 => 21
  | .x22 => 22 | .x23 => 23 | .x24 => 24 | .x25 => 25 | .x26 => 26 | .x27 => 27 | .x28 => 28
  | .x30 => 30

namespace Enc

/-- Register 31, the stack pointer or the zero register by context. -/
def r31 : Nat := 31

/-- `sf`: bit 31, 1 for the 64-bit form. -/
def sf : Size → Nat
  | .w => 0
  | .x => 1 <<< 31

/-- `N` (bit 22) of the bitfield and extract instructions: `sf`. -/
def nBit : Size → Nat
  | .w => 0
  | .x => 1 <<< 22

/-- `Rd`/`Rt` (4–0), `Rn` (9–5), `Rm` (20–16). -/
def rdnm (d n m : Nat) : Nat := m <<< 16 ||| n <<< 5 ||| d

/-- The condition codes (C1.2.4, "Condition code"). -/
def cond : CondCode → Nat
  | .eq => 0 | .ne => 1 | .hs => 2 | .lo => 3 | .mi => 4 | .pl => 5 | .vs => 6 | .vc => 7
  | .hi => 8 | .ls => 9 | .ge => 10 | .lt => 11 | .gt => 12 | .le => 13

/-- `ADD`/`SUB` (immediate), `imm < 4096` (`sh = 0`): `sf op S 100010 sh
imm12 Rn Rd`. -/
def addSubImm (base : Nat) (sz : Size) (d n imm : Nat) : Option Nat :=
  if imm < 4096 then some (base ||| sf sz ||| imm <<< 10 ||| n <<< 5 ||| d) else none

/-- The `size` field (23–22) of a vector instruction on the lanes of an
arrangement. -/
def vsize : VArr → Nat
  | .b16 => 0 | .h8 => 1 | .s4 => 2 | .d2 => 3

/-- `log2` of the lane size in bytes. -/
def vlog : VArr → Nat
  | .b16 => 0 | .h8 => 1 | .s4 => 2 | .d2 => 3

/-- The `imm5` of an element of the arrangement at index `i` (DUP, INS,
UMOV: `imm5 = i : 1 : 0…0`, the 1 at bit `log2 esize - 3`); `none` if `i` is
not a lane. -/
def imm5 (a : VArr) (i : Nat) : Option Nat :=
  if i < 16 >>> vlog a then some ((i <<< (vlog a + 1)) ||| (1 <<< vlog a)) else none

/-- A vector instruction `base` on `d`, `n`, `m`. -/
def v3 (base : Nat) (d n m : VReg) : Nat := base ||| rdnm d.index n.index m.index

/-- A vector instruction `base` on `d`, `n`. -/
def v2 (base : Nat) (d n : VReg) : Nat := base ||| n.index <<< 5 ||| d.index

end Enc

open Enc in
/-- The word of an AdvSIMD or cryptographic instruction (C7.2), its 128-bit
(`Q = 1`) form but where the arrangement is 64-bit (`umull`, `umlal`,
`pmull` of the low halves); `none` if an operand does not fit its field. -/
def VOp.encode : VOp → Option Nat
  -- "MOV (vector)": alias of ORR (vector) with `Rm = Rn`.
  | .mov d n => some (v3 0x4EA01C00 d n n)
  -- "MOVI", 64-bit variant `op = 1, cmode = 1110`, `Q = 1`, all bits 0.
  | .movi0 d => some (0x6F00E400 ||| d.index)
  -- "DUP (general)": `0 Q 0 01110000 imm5 0 0001 1 Rn Rd`.
  | .dup a d n => (imm5 a 0).map fun i => 0x4E000C00 ||| i <<< 16 ||| n.index <<< 5 ||| d.index
  -- "INS (general)" (alias MOV (from general)): `0 1 0 01110000 imm5 0 0011 1 Rn Rd`.
  | .ins a d i n => (imm5 a i).map fun i => 0x4E001C00 ||| i <<< 16 ||| n.index <<< 5 ||| d.index
  -- "DUP (element)", scalar (alias MOV (scalar)): `01 0 11110000 imm5 0 0000 1 Rn Rd`.
  | .dupS d n i => (imm5 .s4 i).map fun i => 0x5E000400 ||| i <<< 16 ||| n.index <<< 5 ||| d.index
  -- "DUP (element)", vector: `0 Q 0 01110000 imm5 0 0000 1 Rn Rd`.
  | .dupE a d n i => (imm5 a i).map fun i => 0x4E000400 ||| i <<< 16 ||| n.index <<< 5 ||| d.index
  -- "INS (element)" (alias MOV (element)): `0 1 1 01110000 imm5 0 imm4 1 Rn Rd`,
  -- `imm4 = j << log2 esize`.
  | .insE a d i n j => do
    let i5 ← imm5 a i
    if j < 16 >>> vlog a then
      some (0x6E000400 ||| i5 <<< 16 ||| (j <<< vlog a) <<< 11 ||| n.index <<< 5 ||| d.index)
    else none
  -- "CMEQ (register)".
  | .cmeq a d n m => some (v3 (0x6E208C00 ||| vsize a <<< 22) d n m)
  -- "CMHI (register)", "CMHS (register)".
  | .cmp .hi a d n m => some (v3 (0x6E203400 ||| vsize a <<< 22) d n m)
  | .cmp .hs a d n m => some (v3 (0x6E203C00 ||| vsize a <<< 22) d n m)
  -- "BSL", "BIT", "BIF".
  | .bsel .bsl d n m => some (v3 0x6E601C00 d n m)
  | .bsel .bit d n m => some (v3 0x6EA01C00 d n m)
  | .bsel .bif d n m => some (v3 0x6EE01C00 d n m)
  -- "AND (vector)", "ORR (vector, register)", "EOR (vector)", "BIC (vector,
  -- register)", "ORN (vector)".
  | .logic .and d n m => some (v3 0x4E201C00 d n m)
  | .logic .orr d n m => some (v3 0x4EA01C00 d n m)
  | .logic .eor d n m => some (v3 0x6E201C00 d n m)
  | .logic .bic d n m => some (v3 0x4E601C00 d n m)
  | .logic .orn d n m => some (v3 0x4EE01C00 d n m)
  -- "NOT" (alias MVN).
  | .not d n => some (v2 0x6E205800 d n)
  -- "ADD (vector)", "SUB (vector)".
  | .add a d n m => some (v3 (0x4E208400 ||| vsize a <<< 22) d n m)
  | .sub a d n m => some (v3 (0x6E208400 ||| vsize a <<< 22) d n m)
  -- "ADDV", "UADDLV": no `.2d` form.
  | .addv a d n => if a == .d2 then none else some (v2 (0x4E31B800 ||| vsize a <<< 22) d n)
  | .uaddlv a d n => if a == .d2 then none else some (v2 (0x6E303800 ||| vsize a <<< 22) d n)
  -- "SHL", "SLI": `immh:immb = esize + shift`, `shift < esize`; "USHR",
  -- "SRI", "SSHR": `immh:immb = 2 * esize - shift`, `1 ≤ shift ≤ esize`.
  | .shift op a d n sh =>
    let e := a.esize
    let left := fun (base : Nat) => if sh < e then some (v2 (base ||| (e + sh) <<< 16) d n) else none
    let right := fun (base : Nat) =>
      if 1 ≤ sh ∧ sh ≤ e then some (v2 (base ||| (2 * e - sh) <<< 16) d n) else none
    match op with
    | .shl => left 0x4F005400
    | .sli => left 0x6F005400
    | .ushr => right 0x6F000400
    | .sri => right 0x6F004400
    | .sshr => right 0x4F000400
  -- "EXT": `0 Q 101110 00 0 Rm 0 imm4 0 Rn Rd`, `imm < 16`.
  | .ext d n m imm => if imm < 16 then some (v3 (0x6E000000 ||| imm <<< 11) d n m) else none
  -- "REV32", "REV64".
  | .rev .rev32b d n => some (v2 0x6E200800 d n)
  | .rev .rev32h d n => some (v2 0x6E600800 d n)
  | .rev .rev64b d n => some (v2 0x4E200800 d n)
  | .rev .rev64s d n => some (v2 0x4EA00800 d n)
  -- "ZIP1", "ZIP2", "TRN1", "TRN2", "UZP1", "UZP2".
  | .perm op a d n m =>
    let base := match op with
      | .zip1 => 0x4E003800 | .zip2 => 0x4E007800 | .trn1 => 0x4E002800
      | .trn2 => 0x4E006800 | .uzp1 => 0x4E001800 | .uzp2 => 0x4E005800
    some (v3 (base ||| vsize a <<< 22) d n m)
  -- "TBL", "TBX": `0 Q 001110 000 Rm 0 len op 00 Rn Rd`, `1 ≤ len ≤ 4`.
  | .tbl d n m => some (v3 0x4E000000 d n m)
  | .tblN x len d n m =>
    if 1 ≤ len ∧ len ≤ 4 then
      some (v3 (0x4E000000 ||| (len - 1) <<< 13 ||| (if x then 1 <<< 12 else 0)) d n m)
    else none
  -- "UMULL, UMULL2", "UMLAL, UMLAL2" (`size = 10`, or `01` for the `H` forms).
  | .umull hi d n m => some (v3 (if hi then 0x6EA0C000 else 0x2EA0C000) d n m)
  | .umlal hi d n m => some (v3 (if hi then 0x6EA08000 else 0x2EA08000) d n m)
  | .umullH hi d n m => some (v3 (if hi then 0x6E60C000 else 0x2E60C000) d n m)
  | .umlalH hi d n m => some (v3 (if hi then 0x6E608000 else 0x2E608000) d n m)
  -- "MUL (vector)", "MLA (vector)", "MLS (vector)", "SQDMULH (vector)",
  -- "UMIN", `.4s`.
  | .mul d n m => some (v3 0x4EA09C00 d n m)
  | .mla d n m => some (v3 0x4EA09400 d n m)
  | .mls d n m => some (v3 0x6EA09400 d n m)
  | .sqdmulh d n m => some (v3 0x4EA0B400 d n m)
  | .umin d n m => some (v3 0x6EA06C00 d n m)
  -- The same and "SQRDMULH (vector)", `.8h`.
  | .mulH op d n m =>
    let base := match op with
      | .mul => 0x4E609C00 | .mla => 0x4E609400 | .mls => 0x6E609400
      | .sqdmulh => 0x4E60B400 | .sqrdmulh => 0x6E60B400
    some (v3 base d n m)
  -- "MUL (by element)", "MLA (by element)", "MLS (by element)", "SQDMULH (by
  -- element)", "SQRDMULH (by element)", `.8h` (`size = 01`): `Rm` is `v0`–`v15`
  -- (bits 19–16), the index `H:L:M` (bits 11, 21, 20).
  | .mulHE op d n m i =>
    if m.index < 16 ∧ i < 8 then
      let base := match op with
        | .mul => 0x4F408000 | .mla => 0x6F400000 | .mls => 0x6F404000
        | .sqdmulh => 0x4F40C000 | .sqrdmulh => 0x4F40D000
      some (base ||| (i >>> 2) <<< 11 ||| ((i >>> 1) % 2) <<< 21 ||| (i % 2) <<< 20 |||
        m.index <<< 16 ||| n.index <<< 5 ||| d.index)
    else none
  -- "PMULL, PMULL2", `size = 11` (`.1q` from `.1d`/`.2d`).
  | .pmull hi d n m => some (v3 (if hi then 0x4EE0E000 else 0x0EE0E000) d n m)
  -- "PMULL, PMULL2", `size = 00` (`.8h` from `.8b`/`.16b`): `0 Q 0 01110 size
  -- 1 Rm 1110 00 Rn Rd`.
  | .pmull8 hi d n m => some (v3 (if hi then 0x4E20E000 else 0x0E20E000) d n m)
  -- "AESE", "AESD", "AESMC", "AESIMC".
  | .aese d n => some (v2 0x4E284800 d n)
  | .aesd d n => some (v2 0x4E285800 d n)
  | .aesmc d n => some (v2 0x4E286800 d n)
  | .aesimc d n => some (v2 0x4E287800 d n)
  -- "SHA1C", "SHA1P", "SHA1M", "SHA1H", "SHA1SU0", "SHA1SU1".
  | .sha1 .c d n m => some (v3 0x5E000000 d n m)
  | .sha1 .p d n m => some (v3 0x5E001000 d n m)
  | .sha1 .m d n m => some (v3 0x5E002000 d n m)
  | .sha1h d n => some (v2 0x5E280800 d n)
  | .sha1su0 d n m => some (v3 0x5E003000 d n m)
  | .sha1su1 d n => some (v2 0x5E281800 d n)
  -- "SHA256H", "SHA256H2", "SHA256SU0", "SHA256SU1".
  | .sha256h d n m => some (v3 0x5E004000 d n m)
  | .sha256h2 d n m => some (v3 0x5E005000 d n m)
  | .sha256su0 d n => some (v2 0x5E282800 d n)
  | .sha256su1 d n m => some (v3 0x5E006000 d n m)
  -- "SHA512H", "SHA512H2", "SHA512SU0", "SHA512SU1".
  | .sha512h d n m => some (v3 0xCE608000 d n m)
  | .sha512h2 d n m => some (v3 0xCE608400 d n m)
  | .sha512su0 d n => some (v2 0xCEC08000 d n)
  | .sha512su1 d n m => some (v3 0xCE608800 d n m)
  -- "SM4E": `11001110 11000000 100001 Rn Rd`; "SM4EKEY": `11001110 011 Rm
  -- 110010 Rn Rd`.
  | .sm4e d n => some (v2 0xCEC08400 d n)
  | .sm4ekey d n m => some (v3 0xCE60C800 d n m)
  -- "SM3SS1": `11001110 010 Rm 0 Ra Rn Rd`; "SM3TT1A", "SM3TT1B", "SM3TT2A",
  -- "SM3TT2B": `11001110 010 Rm 10 imm2 opcode Rn Rd`, `opcode` 00, 01, 10,
  -- 11; "SM3PARTW1", "SM3PARTW2": `11001110 011 Rm 1100 opcode Rn Rd`,
  -- `opcode` 00, 01.
  | .sm3ss1 d n m a => some (v3 (0xCE400000 ||| a.index <<< 10) d n m)
  | .sm3tt op d n m i =>
    if i < 4 then
      let opcode := match op with | .tt1a => 0 | .tt1b => 1 | .tt2a => 2 | .tt2b => 3
      some (v3 (0xCE408000 ||| i <<< 12 ||| opcode <<< 10) d n m)
    else none
  | .sm3partw1 d n m => some (v3 0xCE60C000 d n m)
  | .sm3partw2 d n m => some (v3 0xCE60C400 d n m)
  -- "EOR3", "BCAX": `Ra` at bits 14–10; "RAX1"; "XAR": `imm6` at 15–10.
  | .eor3 d n m a => some (v3 (0xCE000000 ||| a.index <<< 10) d n m)
  | .bcax d n m a => some (v3 (0xCE200000 ||| a.index <<< 10) d n m)
  | .rax1 d n m => some (v3 0xCE608C00 d n m)
  | .xar d n m imm => if imm < 64 then some (v3 (0xCE800000 ||| imm <<< 10) d n m) else none
  -- SVE2 "XAR", `.s` (C8.2): `00000100 tszh 1 tszl imm3 001101 Zm Zdn`, with
  -- `tszh:tszl:imm3 = 2 * esize - rot`, `1 ≤ rot ≤ 32`.
  | .xarS d m rot =>
    if 1 ≤ rot ∧ rot ≤ 32 then
      let v := 64 - rot
      some (0x04203400 ||| (v >>> 5) <<< 22 ||| ((v >>> 3) % 4) <<< 19 ||| (v % 8) <<< 16 |||
        m.index <<< 5 ||| d.index)
    else none

open Enc in
/-- The words of an instruction, in order: one for each instruction
`Instr.asm` (`Print.lean`) names; `none` if an operand does not fit its
field, or for the instructions printed as text (`adrSym`, `align`). -/
def Instr.encode : Instr → Option (List Nat)
  -- "ADD (shifted register)", "SUB (shifted register)", "ADDS (shifted
  -- register)", "SUBS (shifted register)", no shift: `sf op S 01011 00 0 Rm
  -- 000000 Rn Rd`.
  | .add sz d n m => some [0x0B000000 ||| sf sz ||| rdnm d.index n.index m.index]
  | .sub sz d n m => some [0x4B000000 ||| sf sz ||| rdnm d.index n.index m.index]
  | .adds sz d n m => some [0x2B000000 ||| sf sz ||| rdnm d.index n.index m.index]
  | .subs sz d n m => some [0x6B000000 ||| sf sz ||| rdnm d.index n.index m.index]
  -- "ADC", "ADCS", "SBC", "SBCS": `sf op S 11010000 Rm 000000 Rn Rd`.
  | .adc sz d n m => some [0x1A000000 ||| sf sz ||| rdnm d.index n.index m.index]
  | .adcs sz d n m => some [0x3A000000 ||| sf sz ||| rdnm d.index n.index m.index]
  | .sbc sz d n m => some [0x5A000000 ||| sf sz ||| rdnm d.index n.index m.index]
  | .sbcs sz d n m => some [0x7A000000 ||| sf sz ||| rdnm d.index n.index m.index]
  -- "CSEL": `sf 0 0 11010100 Rm cond 00 Rn Rd`; "CSNEG": `sf 1 0 11010100 Rm
  -- cond 01 Rn Rd`.
  | .csel sz d n m => some [0x1A800000 ||| sf sz ||| cond .hs <<< 12 ||| rdnm d.index n.index m.index]
  | .cselc sz d n m c => some [0x1A800000 ||| sf sz ||| cond c <<< 12 ||| rdnm d.index n.index m.index]
  | .csneg sz d n m c => some [0x5A800400 ||| sf sz ||| cond c <<< 12 ||| rdnm d.index n.index m.index]
  -- "TST (shifted register)": alias of ANDS (shifted register) with `Rd = 31`.
  | .tst sz n m => some [0x6A000000 ||| sf sz ||| rdnm r31 n.index m.index]
  -- "CCMP (immediate)": `sf 1 1 11010010 imm5 cond 1 0 Rn 0 nzcv`.
  | .ccmp sz n imm nzcv c =>
    if imm < 32 ∧ nzcv < 16 then
      some [0x7A400800 ||| sf sz ||| imm <<< 16 ||| cond c <<< 12 ||| n.index <<< 5 ||| nzcv]
    else none
  -- "ADD (immediate)", "SUB (immediate)".
  | .addImm sz d n imm => (addSubImm 0x11000000 sz d.index n.index imm).map ([·])
  | .subImm sz d n imm => (addSubImm 0x51000000 sz d.index n.index imm).map ([·])
  | .addSp d imm => (addSubImm 0x11000000 .x d.index r31 imm).map ([·])
  | .alloc bytes => (addSubImm 0x51000000 .x r31 r31 bytes).map ([·])
  | .free bytes => (addSubImm 0x11000000 .x r31 r31 bytes).map ([·])
  -- "AND (shifted register)", "ORR (shifted register)", "EOR (shifted
  -- register)": `sf opc 01010 shift N Rm imm6 Rn Rd`; ROR is `shift = 11`;
  -- "BIC (shifted register)" is AND's with `N = 1`.
  | .logic op sz d n m =>
    let base := match op with | .and => 0x0A000000 | .orr => 0x2A000000 | .eor => 0x4A000000
    some [base ||| sf sz ||| rdnm d.index n.index m.index]
  | .logicRor op sz d n m sh =>
    let base := match op with | .and => 0x0A000000 | .orr => 0x2A000000 | .eor => 0x4A000000
    if sh < sz.bits then some [base ||| sf sz ||| 3 <<< 22 ||| sh <<< 10 ||| rdnm d.index n.index m.index]
    else none
  | .bicRor sz d n m sh =>
    if sh < sz.bits then
      some [0x0A200000 ||| sf sz ||| 3 <<< 22 ||| sh <<< 10 ||| rdnm d.index n.index m.index]
    else none
  -- "EXTR": `sf 00 100111 N 0 Rm imms Rn Rd`; "ROR (immediate)" is EXTR with
  -- `Rm = Rn`.
  | .extr sz d n m lsb =>
    if lsb < sz.bits then
      some [0x13800000 ||| sf sz ||| nBit sz ||| lsb <<< 10 ||| rdnm d.index n.index m.index]
    else none
  | .ror sz d n sh =>
    if sh < sz.bits then
      some [0x13800000 ||| sf sz ||| nBit sz ||| sh <<< 10 ||| rdnm d.index n.index n.index]
    else none
  -- "UBFM": `sf 10 100110 N immr imms Rn Rd`; "LSR (immediate)": `immr = sh`,
  -- `imms = size - 1`; "LSL (immediate)": `immr = -sh MOD size`, `imms =
  -- size - 1 - sh`.
  | .lsr sz d n sh =>
    if sh < sz.bits then
      some [0x53000000 ||| sf sz ||| nBit sz ||| sh <<< 16 ||| (sz.bits - 1) <<< 10 |||
        n.index <<< 5 ||| d.index]
    else none
  | .lsl sz d n sh =>
    if sh < sz.bits then
      some [0x53000000 ||| sf sz ||| nBit sz ||| ((sz.bits - sh) % sz.bits) <<< 16 |||
        (sz.bits - 1 - sh) <<< 10 ||| n.index <<< 5 ||| d.index]
    else none
  -- "MADD": `sf 00 11011 000 Rm 0 Ra Rn Rd`; "MUL" is MADD with `Ra = 31`.
  | .madd sz d n m a => some [0x1B000000 ||| sf sz ||| a.index <<< 10 ||| rdnm d.index n.index m.index]
  | .mul sz d n m => some [0x1B000000 ||| sf sz ||| r31 <<< 10 ||| rdnm d.index n.index m.index]
  -- "UMULH": `1 00 11011 110 Rm 0 11111 Rn Rd`.
  | .umulh d n m => some [0x9BC07C00 ||| rdnm d.index n.index m.index]
  -- "UMADDL": `1 00 11011 101 Rm 0 Ra Rn Rd`; "UMULL" is UMADDL with `Ra = 31`.
  | .umaddl d n m a => some [0x9BA00000 ||| a.index <<< 10 ||| rdnm d.index n.index m.index]
  | .umull d n m => some [0x9BA00000 ||| r31 <<< 10 ||| rdnm d.index n.index m.index]
  -- "CLZ", "RBIT", "REV" (32-bit: `opc = 10`; 64-bit: `opc = 11`).
  | .clz sz d n => some [0x5AC01000 ||| sf sz ||| n.index <<< 5 ||| d.index]
  | .rbit sz d n => some [0x5AC00000 ||| sf sz ||| n.index <<< 5 ||| d.index]
  | .rev32 d n => some [0x5AC00800 ||| n.index <<< 5 ||| d.index]
  | .rev d n => some [0xDAC00C00 ||| n.index <<< 5 ||| d.index]
  -- "MOVZ", "MOVK": `sf opc 100101 hw imm16 Rd`, `16 * hw < size`.
  | .movz sz d imm hw =>
    if 16 * hw < sz.bits then some [0x52800000 ||| sf sz ||| hw <<< 21 ||| imm.toNat <<< 5 ||| d.index]
    else none
  | .movk sz d imm hw =>
    if 16 * hw < sz.bits then some [0x72800000 ||| sf sz ||| hw <<< 21 ||| imm.toNat <<< 5 ||| d.index]
    else none
  -- "LDR (immediate)", "STR (immediate)", unsigned offset: `1x 111 0 01 opc
  -- imm12 Rn Rt`, `imm12 = off / size`, `off` a multiple of the size below
  -- `4096 * size`.
  | .ldr sz t n off => ldst (if sz == .x then 0xF9400000 else 0xB9400000) sz.bytes t.index n.index off
  | .str sz t n off => ldst (if sz == .x then 0xF9000000 else 0xB9000000) sz.bytes t.index n.index off
  | .ldrSp t off => ldst 0xF9400000 8 t.index r31 off
  | .strSp t off => ldst 0xF9000000 8 t.index r31 off
  -- "LDRB (immediate)", "STRB (immediate)", unsigned offset.
  | .ldrb t n off => ldst 0x39400000 1 t.index n.index off
  | .strb t n off => ldst 0x39000000 1 t.index n.index off
  -- "LDP", "STP", 64-bit, signed offset: `10 101 0 010 L imm7 Rt2 Rn Rt`,
  -- `imm7 = off / 8`, `off` a multiple of 8 at most 504.
  | .ldp t1 t2 n off =>
    if off % 8 = 0 ∧ off ≤ 504 then
      some [0xA9400000 ||| (off / 8) <<< 15 ||| t2.index <<< 10 ||| n.index <<< 5 ||| t1.index]
    else none
  | .stp t1 t2 n off =>
    if off % 8 = 0 ∧ off ≤ 504 then
      some [0xA9000000 ||| (off / 8) <<< 15 ||| t2.index <<< 10 ||| n.index <<< 5 ||| t1.index]
    else none
  -- "STR (immediate)", 64-bit, pre-index, `#-16`: `11 111 0 00 00 0 imm9 11
  -- Rn Rt`; "LDR (immediate)", 64-bit, post-index, `#16`: `… 01 0 imm9 01 Rn
  -- Rt`.
  -- C6.2 "BLR": `1101011 0 0 01 11111 0000 0 0 Rn 00000`.
  | .blr n => some [0xD63F0000 ||| n.index <<< 5]
  | .push r => some [0xF8000C00 ||| (512 - 16) <<< 12 ||| r31 <<< 5 ||| r.index]
  | .pop r => some [0xF8400400 ||| 16 <<< 12 ||| r31 <<< 5 ||| r.index]
  | .vop op => op.encode.map ([·])
  -- "LDR (immediate, SIMD&FP)", "STR (immediate, SIMD&FP)", 128-bit,
  -- unsigned offset: `00 111 1 01 opc imm12 Rn Rt`, `imm12 = off / 16`.
  | .ldrq t n off => ldst 0x3DC00000 16 t.index n.index off
  | .ldrqTbl t n off .. => ldst 0x3DC00000 16 t.index n.index off
  -- As `ldr`: "LDR (immediate)", unsigned offset.
  | .ldrTbl sz t n off .. => ldst (if sz == .x then 0xF9400000 else 0xB9400000) sz.bytes t.index n.index off
  | .strq t n off => ldst 0x3D800000 16 t.index n.index off
  -- "UMOV": `0 Q 0 01110000 imm5 0 0111 1 Rn Rd`, `.s` (`Q = 0`) or `.d`
  -- (`Q = 1`).
  | .umov .w d n i => (imm5 .s4 i).map fun i => [0x0E003C00 ||| i <<< 16 ||| n.index <<< 5 ||| d.index]
  | .umov .x d n i => (imm5 .d2 i).map fun i => [0x4E003C00 ||| i <<< 16 ||| n.index <<< 5 ||| d.index]
  -- "MRS": `1101010100 1 1 o0 op1 CRn CRm op2 Rt`, where `op0 = 0b1:o0`,
  -- with the encoding of the system register DIT (DDI 0601 2026-03, "DIT,
  -- Data Independent Timing", "Accessing DIT"): `op0 = 0b11`, `op1 =
  -- 0b011`, `CRn = 0b0100`, `CRm = 0b0010`, `op2 = 0b101`.
  | .mrsDit t => some [0xD5300000 ||| sysDit ||| t.index]
  -- "MSR (immediate)": `1101010100 0 00 op1 0100 CRm op2 11111`, with the
  -- PSTATE field DIT, `op1 = 0b011`, `op2 = 0b010`, and `CRm` the immediate.
  | .msrDitImm on => some [0xD500401F ||| 3 <<< 16 ||| on.toNat <<< 8 ||| 2 <<< 5]
  -- The barriers, `11010101000000110011 CRm 1 opc 11111` (DDI 0602 2026-03):
  -- "DSB" with `CRm = '1111'` (SY) and `opc = '00'`, "ISB" with `CRm =
  -- '1111'` (SY) and `opc = '10'`, "SB" with `CRm = '0000'` and `opc = '11'`.
  | .barrier .dsbSy => some [0xD5033F9F]
  | .barrier .isb => some [0xD5033FDF]
  | .barrier .sb => some [0xD50330FF]
  | .adrSym .. | .align _ => none
where
  /-- The fields `o0 op1 CRn CRm op2` (19–5) of the system register DIT. -/
  sysDit : Nat := 1 <<< 19 ||| 3 <<< 16 ||| 4 <<< 12 ||| 2 <<< 8 ||| 5 <<< 5
  /-- A load or store, unsigned offset, of `bytes` bytes: `base ||| imm12 <<
  10 ||| Rn ||| Rt`. -/
  ldst (base bytes t n off : Nat) : Option (List Nat) :=
    if off % bytes = 0 ∧ off / bytes < 4096 then
      some [base ||| (off / bytes) <<< 10 ||| n <<< 5 ||| t]
    else none

/-- `ret` ("RET", `Rn = x30`). -/
def retWord : Nat := 0xD65F03C0

/-- `w` as 8 hexadecimal digits, after `0x`. -/
def hex32 (w : Nat) : String :=
  let ds := Nat.toDigits 16 (w % 2 ^ 32)
  "0x" ++ String.ofList (List.replicate (8 - ds.length) '0' ++ ds)

/-- The assembler directive emitting the instruction `w` (`.inst`, which
emits a 32-bit instruction, marked as code for the tools that read mapping
symbols). -/
def instLine (w : Nat) : String := s!".inst {hex32 w}"

end VG.AArch64
