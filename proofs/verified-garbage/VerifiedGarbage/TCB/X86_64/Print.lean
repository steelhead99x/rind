module

public import VerifiedGarbage.TCB.X86_64.Encode
public import VerifiedGarbage.TCB.Print
public import VerifiedGarbage.TCB.X86_64.Target

/-!
# Intel-syntax printer for the x86-64 model

**Trusted.** Emits Intel syntax without register prefixes, which is the
default dialect of Rust's `asm!`/`naked_asm!` on x86-64.

Each straight-line instruction and the return are printed as their machine
code (`Encode.lean`), `.byte <bytes>`, each after a line `// <the
instruction's text>`, which the emitter writes in the module's assembly file, not in its code
(`Rust.assembly`): the assembler only copies the bytes. The branches
(`jcc`, `jmp`), the call and the address of a static (`symLines`) are
printed as text, for the assembler and linker to lay out.
-/

@[expose] public section

namespace VG.X86_64

def Reg.name : Reg → String
  | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx"
  | .rsp => "rsp" | .rbp => "rbp" | .rsi => "rsi" | .rdi => "rdi"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

/-- The 32-bit name of a register (its low 32 bits). -/
def Reg.name32 : Reg → String
  | .rax => "eax" | .rcx => "ecx" | .rdx => "edx" | .rbx => "ebx"
  | .rsp => "esp" | .rbp => "ebp" | .rsi => "esi" | .rdi => "edi"
  | .r8 => "r8d" | .r9 => "r9d" | .r10 => "r10d" | .r11 => "r11d"
  | .r12 => "r12d" | .r13 => "r13d" | .r14 => "r14d" | .r15 => "r15d"

/-- The 16-bit name of a register (its low 16 bits). -/
def Reg.name16 : Reg → String
  | .rax => "ax" | .rcx => "cx" | .rdx => "dx" | .rbx => "bx"
  | .rsp => "sp" | .rbp => "bp" | .rsi => "si" | .rdi => "di"
  | .r8 => "r8w" | .r9 => "r9w" | .r10 => "r10w" | .r11 => "r11w"
  | .r12 => "r12w" | .r13 => "r13w" | .r14 => "r14w" | .r15 => "r15w"

/-- The 8-bit name of a register (its low byte). -/
def Reg.name8 : Reg → String
  | .rax => "al" | .rcx => "cl" | .rdx => "dl" | .rbx => "bl"
  | .rsp => "spl" | .rbp => "bpl" | .rsi => "sil" | .rdi => "dil"
  | .r8 => "r8b" | .r9 => "r9b" | .r10 => "r10b" | .r11 => "r11b"
  | .r12 => "r12b" | .r13 => "r13b" | .r14 => "r14b" | .r15 => "r15b"

/-- `[base+index*scale+disp]` -/
def MemOp.addr (m : MemOp) : String :=
  let idx := match m.index with
    | none => ""
    | some i => s!"+{i.name}*{m.scale}"
  let d := if m.disp = 0 then "" else if m.disp > 0 then s!"+{m.disp}" else s!"{m.disp}"
  s!"[{m.base.name}{idx}{d}]"

def MemOp.str (m : MemOp) : String := s!"QWORD PTR {m.addr}"

def MemOp.str32 (m : MemOp) : String := s!"DWORD PTR {m.addr}"

def MemOp.str8 (m : MemOp) : String := s!"BYTE PTR {m.addr}"

def MemOp.str16 (m : MemOp) : String := s!"WORD PTR {m.addr}"

def MemOp.str128 (m : MemOp) : String := s!"XMMWORD PTR {m.addr}"

def XReg.name : XReg → String
  | .xmm0 => "xmm0" | .xmm1 => "xmm1" | .xmm2 => "xmm2" | .xmm3 => "xmm3"
  | .xmm4 => "xmm4" | .xmm5 => "xmm5" | .xmm6 => "xmm6" | .xmm7 => "xmm7"
  | .xmm8 => "xmm8" | .xmm9 => "xmm9" | .xmm10 => "xmm10" | .xmm11 => "xmm11"
  | .xmm12 => "xmm12" | .xmm13 => "xmm13" | .xmm14 => "xmm14" | .xmm15 => "xmm15"

/-- The name of the AVX register whose low 128 bits are `r`. -/
def XReg.yname (r : XReg) : String := "y" ++ (r.name.drop 1).toString

/-- A vector register's name at a VEX vector length. -/
def XReg.vname (r : XReg) : VLen → String
  | .l128 => r.name
  | .l256 => r.yname

def MemOp.str256 (m : MemOp) : String := s!"YMMWORD PTR {m.addr}"

def MemOp.str512 (m : MemOp) : String := s!"ZMMWORD PTR {m.addr}"

/-- The name of the AVX-512 register whose low 128 bits are `r`. -/
def XReg.zname (r : XReg) : String := "z" ++ (r.name.drop 1).toString

/-- A memory operand of a VEX vector length. -/
def MemOp.strV (m : MemOp) : VLen → String
  | .l128 => m.str128
  | .l256 => m.str256

def XBinOp.name : XBinOp → String
  | .movdqa => "movdqa" | .paddd => "paddd" | .pxor => "pxor" | .por => "por"
  | .punpckldq => "punpckldq" | .punpckhdq => "punpckhdq"
  | .punpcklqdq => "punpcklqdq" | .punpckhqdq => "punpckhqdq"
  | .pshufb => "pshufb" | .sha256msg1 => "sha256msg1" | .sha256msg2 => "sha256msg2"
  | .sha1msg1 => "sha1msg1" | .sha1msg2 => "sha1msg2" | .sha1nexte => "sha1nexte"
  | .pand => "pand" | .pandn => "pandn" | .paddq => "paddq" | .psubq => "psubq"
  | .pmuludq => "pmuludq"
  | .paddw => "paddw" | .psubw => "psubw" | .psubd => "psubd" | .pmullw => "pmullw"
  | .pmulhw => "pmulhw" | .packssdw => "packssdw" | .punpcklwd => "punpcklwd"
  | .punpckhwd => "punpckhwd"
  | .aesenc => "aesenc" | .aesenclast => "aesenclast" | .aesdec => "aesdec"
  | .aesdeclast => "aesdeclast" | .aesimc => "aesimc" | .pcmpeqd => "pcmpeqd"
  | .pmaddwd => "pmaddwd" | .pmulhrsw => "pmulhrsw" | .pcmpgtw => "pcmpgtw"
  | .packsswb => "packsswb"

def XShiftOp.name : XShiftOp → String
  | .pslld => "pslld" | .psrld => "psrld" | .psllq => "psllq" | .psrlq => "psrlq"
  | .pslldq => "pslldq" | .psrldq => "psrldq" | .psllw => "psllw" | .psrlw => "psrlw"
  | .psraw => "psraw" | .psrad => "psrad"

def XOp.asm : XOp → String
  | .bin op d r => s!"{op.name} {d.name}, {r.name}"
  | .shift op d n => s!"{op.name} {d.name}, {n.toNat}"
  | .pshufd d r o => s!"pshufd {d.name}, {r.name}, {o.toNat}"
  | .palignr d r n => s!"palignr {d.name}, {r.name}, {n.toNat}"
  | .pblendw d r n => s!"pblendw {d.name}, {r.name}, {n.toNat}"
  | .sha256rnds2 d r => s!"sha256rnds2 {d.name}, {r.name}, xmm0"
  | .sha1rnds4 d r n => s!"sha1rnds4 {d.name}, {r.name}, {n.toNat}"
  | .movq d r => s!"movq {d.name}, {r.name}"
  | .aeskeygenassist d r n => s!"aeskeygenassist {d.name}, {r.name}, {n.toNat}"
  | .pclmulqdq d r n => s!"pclmulqdq {d.name}, {r.name}, {n.toNat}"

def VBinOp.name : VBinOp → String
  | .vpaddd => "vpaddd" | .vpaddq => "vpaddq" | .vpxor => "vpxor" | .vpor => "vpor"
  | .vpand => "vpand" | .vpandn => "vpandn" | .vpshufb => "vpshufb" | .vpmuludq => "vpmuludq"
  | .vpunpckldq => "vpunpckldq" | .vpunpckhdq => "vpunpckhdq"
  | .vpunpcklqdq => "vpunpcklqdq" | .vpunpckhqdq => "vpunpckhqdq"
  | .vpaddw => "vpaddw" | .vpsubw => "vpsubw" | .vpsubd => "vpsubd" | .vpmullw => "vpmullw"
  | .vpmulhw => "vpmulhw" | .vpackssdw => "vpackssdw" | .vpunpcklwd => "vpunpcklwd"
  | .vpunpckhwd => "vpunpckhwd" | .vpsubq => "vpsubq"
  | .vaesenc => "vaesenc" | .vaesenclast => "vaesenclast" | .vaesdec => "vaesdec"
  | .vaesdeclast => "vaesdeclast" | .vpcmpeqd => "vpcmpeqd" | .vpmaddwd => "vpmaddwd"
  | .vpmulhrsw => "vpmulhrsw" | .vpcmpgtw => "vpcmpgtw" | .vpacksswb => "vpacksswb"

def VVarOp.name : VVarOp → String
  | .vpsllvd => "vpsllvd" | .vpsrlvd => "vpsrlvd" | .vpsllvq => "vpsllvq" | .vpsrlvq => "vpsrlvq"

def VOp.asm : VOp → String
  | .vbin op l d a b => s!"{op.name} {d.vname l}, {a.vname l}, {b.vname l}"
  | .vpclmulqdq l d a b n => s!"vpclmulqdq {d.vname l}, {a.vname l}, {b.vname l}, {n.toNat}"
  | .vmovdqa l d r => s!"vmovdqa {d.vname l}, {r.vname l}"
  | .vshift op l d r n => s!"v{op.name} {d.vname l}, {r.vname l}, {n.toNat}"
  | .vpshufd l d r o => s!"vpshufd {d.vname l}, {r.vname l}, {o.toNat}"
  | .vpalignr l d a b n => s!"vpalignr {d.vname l}, {a.vname l}, {b.vname l}, {n.toNat}"
  | .vpblendd l d a b n => s!"vpblendd {d.vname l}, {a.vname l}, {b.vname l}, {n.toNat}"
  | .vpblendw l d a b n => s!"vpblendw {d.vname l}, {a.vname l}, {b.vname l}, {n.toNat}"
  | .vvar op l d a b => s!"{op.name} {d.vname l}, {a.vname l}, {b.vname l}"
  | .vpbroadcastd l d r => s!"vpbroadcastd {d.vname l}, {r.name}"
  | .vpbroadcastq l d r => s!"vpbroadcastq {d.vname l}, {r.name}"
  | .vpermq d r o => s!"vpermq {d.yname}, {r.yname}, {o.toNat}"
  | .vpermd d i r => s!"vpermd {d.yname}, {i.yname}, {r.yname}"
  | .vperm2i128 d a b n => s!"vperm2i128 {d.yname}, {a.yname}, {b.yname}, {n.toNat}"
  | .vinserti128 d a b n => s!"vinserti128 {d.yname}, {a.yname}, {b.name}, {n.toNat}"
  | .vextracti128 d r n => s!"vextracti128 {d.name}, {r.yname}, {n.toNat}"
  | .vmovq d r => s!"vmovq {d.name}, {r.name}"
  | .vzeroupper => "vzeroupper"
  | .vsha512rnds2 d a b => s!"vsha512rnds2 {d.yname}, {a.yname}, {b.name}"
  | .vsha512msg1 d r => s!"vsha512msg1 {d.yname}, {r.name}"
  | .vsha512msg2 d r => s!"vsha512msg2 {d.yname}, {r.yname}"
  | .vpmadd52luq l d a b => s!"vpmadd52luq {d.vname l}, {a.vname l}, {b.vname l}"
  | .vpmadd52huq l d a b => s!"vpmadd52huq {d.vname l}, {a.vname l}, {b.vname l}"
  | .vprold l d r n => s!"vprold {d.vname l}, {r.vname l}, {n.toNat}"
  | .vpternlogd l d a b n => s!"vpternlogd {d.vname l}, {a.vname l}, {b.vname l}, {n.toNat}"
  | .vprorq l d r n => s!"vprorq {d.vname l}, {r.vname l}, {n.toNat}"

def ZBinOp.name : ZBinOp → String
  | .vpaddd => "vpaddd" | .vpxord => "vpxord"
  | .vpunpckldq => "vpunpckldq" | .vpunpckhdq => "vpunpckhdq"
  | .vpunpcklqdq => "vpunpcklqdq" | .vpunpckhqdq => "vpunpckhqdq"
  | .vpaddq => "vpaddq" | .vpmuludq => "vpmuludq" | .vpandq => "vpandq" | .vporq => "vporq"
  | .vpandnq => "vpandnq"
  | .vaesenc => "vaesenc" | .vaesenclast => "vaesenclast" | .vaesdec => "vaesdec"
  | .vaesdeclast => "vaesdeclast" | .vpshufb => "vpshufb"
  | .vpsubq => "vpsubq"

def ZShiftOp.name : ZShiftOp → String
  | .vpsllq => "vpsllq" | .vpsrlq => "vpsrlq"

def ZBcstOp.name : ZBcstOp → String
  | .vpmuludq => "vpmuludq" | .vpandq => "vpandq" | .vporq => "vporq"

def ZBcstDOp.name : ZBcstDOp → String
  | .vpaddd => "vpaddd"

def HReg.name : HReg → String
  | .xmm16 => "xmm16" | .xmm17 => "xmm17" | .xmm18 => "xmm18" | .xmm19 => "xmm19"
  | .xmm20 => "xmm20" | .xmm21 => "xmm21" | .xmm22 => "xmm22" | .xmm23 => "xmm23"
  | .xmm24 => "xmm24" | .xmm25 => "xmm25" | .xmm26 => "xmm26" | .xmm27 => "xmm27"
  | .xmm28 => "xmm28" | .xmm29 => "xmm29" | .xmm30 => "xmm30" | .xmm31 => "xmm31"

def HReg.zname (r : HReg) : String := "z" ++ (r.name.drop 1).toString

def ZKeyOp.name : ZKeyOp → String
  | .vpxord => "vpxord" | .vaesenc => "vaesenc" | .vaesenclast => "vaesenclast"
  | .vpaddd => "vpaddd"

def ZOp.asm : ZOp → String
  | .zbinH op d a b => s!"{op.name} {d.zname}, {a.zname}, {b.zname}"
  | .zbin op d a b => s!"{op.name} {d.zname}, {a.zname}, {b.zname}"
  | .vpclmulqdq d a b n => s!"vpclmulqdq {d.zname}, {a.zname}, {b.zname}, {n.toNat}"
  | .vprold d r n => s!"vprold {d.zname}, {r.zname}, {n.toNat}"
  | .vpshufd d r o => s!"vpshufd {d.zname}, {r.zname}, {o.toNat}"
  | .vshufi32x4 d a b n => s!"vshufi32x4 {d.zname}, {a.zname}, {b.zname}, {n.toNat}"
  | .vshift op d r n => s!"{op.name} {d.zname}, {r.zname}, {n.toNat}"
  | .vpslldq d r n => s!"vpslldq {d.zname}, {r.zname}, {n.toNat}"
  | .vpsrldq d r n => s!"vpsrldq {d.zname}, {r.zname}, {n.toNat}"
  | .vpbroadcastq d r => s!"vpbroadcastq {d.zname}, {r.name}"
  | .vmovdqa64 d r => s!"vmovdqa64 {d.zname}, {r.zname}"
  | .vpternlogd d a b n => s!"vpternlogd {d.zname}, {a.zname}, {b.zname}, {n.toNat}"
  | .vprorq d r n => s!"vprorq {d.zname}, {r.zname}, {n.toNat}"
  | .vpermq d r o => s!"vpermq {d.zname}, {r.zname}, {o.toNat}"
  | .vpmadd52 hi d a b =>
    s!"{if hi then "vpmadd52huq" else "vpmadd52luq"} {d.zname}, {a.zname}, {b.zname}"
  | .vpermw d a b => s!"vpermw {d.zname}, {a.zname}, {b.zname}"
  | .vpsrlvw d a b => s!"vpsrlvw {d.zname}, {a.zname}, {b.zname}"
  | .vextracti32x4 d r n => s!"vextracti32x4 {d.name}, {r.zname}, {n.toNat}"

/-- The name of the `xmm` register of a `VReg`. -/
def VReg.name : VReg → String
  | .lo r => r.name
  | .hi r => r.name

/-- The name of the `ymm` register of a `VReg`. -/
def VReg.yname (r : VReg) : String := "y" ++ (r.name.drop 1).toString
/-- The name of the `zmm` register of a `VReg`. -/
def VReg.zname (r : VReg) : String := "z" ++ (r.name.drop 1).toString

def EBinOp.name : EBinOp → String
  | .vpaddq => "vpaddq" | .vpsubq => "vpsubq" | .vpxorq => "vpxorq" | .vpandq => "vpandq" | .vporq => "vporq"

/-- The mnemonics of `Evex.lean`, which the assembler encodes with EVEX for
`ymm16`–`ymm31` and may encode with VEX for the others where a VEX form with
the same operation exists (`vpaddq`, `vpsubq`, `vpermq`, `vpbroadcastq`,
`vmovq`, the logical shifts): the VEX.256 forms compute the same 256 bits and zero bits
`MAXVL-1:256` too (see `State.setV`). -/
def EOp.asm : EOp → String
  | .bin op d a b => s!"{op.name} {d.yname}, {a.yname}, {b.yname}"
  | .shift op d r n => s!"{op.name} {d.yname}, {r.yname}, {n.toNat}"
  | .vpermq d r o => s!"vpermq {d.yname}, {r.yname}, {o.toNat}"
  | .valignq d a b n => s!"valignq {d.yname}, {a.yname}, {b.yname}, {n.toNat}"
  | .vpbroadcastq d r => s!"vpbroadcastq {d.yname}, {r.name}"
  | .vmovq d r => s!"vmovq {d.name}, {r.name}"
  | .vmovqx d r => s!"vmovq {d.name}, {r.name}"
  | .vpmadd52 hi d a b => s!"vpmadd52{if hi then "h" else "l"}uq {d.yname}, {a.yname}, {b.yname}"
  | .vpternlogq d a b n => s!"vpternlogq {d.yname}, {a.yname}, {b.yname}, {n.toNat}"
  | .vprorq d r n => s!"vprorq {d.yname}, {r.yname}, {n.toNat}"
  | .vpsraq d r n => s!"vpsraq {d.yname}, {r.yname}, {n.toNat}"
  | .vmovdqa64 d r => s!"vmovdqa64 {d.yname}, {r.yname}"

def E5Op.asm : E5Op → String
  | .bin op d a b => s!"{op.name} {d.zname}, {a.zname}, {b.zname}"
  | .shift op d r n => s!"{op.name} {d.zname}, {r.zname}, {n.toNat}"
  | .vpermq d r o => s!"vpermq {d.zname}, {r.zname}, {o.toNat}"
  | .vpmadd52 hi d a b => s!"vpmadd52{if hi then "h" else "l"}uq {d.zname}, {a.zname}, {b.zname}"
  | .vinserti64x4 d a b n => s!"vinserti64x4 {d.zname}, {a.zname}, {b.yname}, {n.toNat}"

def Src.str : Src → String
  | .reg r => r.name
  | .imm v => toString v.toInt
  | .mem m => m.str

/-- A 32-bit source operand. -/
def Src.str32 : Src → String
  | .reg r => r.name32
  | .imm v => toString v.toInt
  | .mem m => m.str32

def AluOp.name : AluOp → String
  | .add => "add" | .adc => "adc" | .sub => "sub" | .sbb => "sbb" | .and => "and"
  | .or => "or" | .xor => "xor" | .cmp => "cmp" | .test => "test"

def ShiftOp.name : ShiftOp → String
  | .ror => "ror" | .shr => "shr" | .shl => "shl"

def VarShiftOp.name : VarShiftOp → String
  | .shl => "shl" | .shr => "shr" | .sar => "sar"

def ShiftxOp.name : ShiftxOp → String
  | .shlx => "shlx" | .shrx => "shrx"

def Cond.name : Cond → String
  | .e => "e" | .ne => "ne" | .b => "b" | .ae => "ae"

def Instr.asm : Instr → List String
  | .mov d s => [s!"mov {d.name}, {s.str}"]
  | .store m r => [s!"mov {m.str}, {r.name}"]
  | .alu op d s => [s!"{op.name} {d.name}, {s.str}"]
  | .aluTbl op d m .. => [s!"{op.name} {d.name}, {m.str}"]
  | .mov32 d s => [s!"mov {d.name32}, {s.str32}"]
  | .store32 m r => [s!"mov {m.str32}, {r.name32}"]
  | .alu32 op d s => [s!"{op.name} {d.name32}, {s.str32}"]
  | .shift32 op d n => [s!"{op.name} {d.name32}, {n}"]
  | .bswap32 d => [s!"bswap {d.name32}"]
  | .rorx32 d r n => [s!"rorx {d.name32}, {r.name32}, {n}"]
  | .andn32 d a b => [s!"andn {d.name32}, {a.name32}, {b.name32}"]
  | .rorx d r n => [s!"rorx {d.name}, {r.name}, {n}"]
  | .andn d a b => [s!"andn {d.name}, {a.name}, {b.name}"]
  | .movzx8 d m => [s!"movzx {d.name32}, {m.str8}"]
  | .movzx16 d m => [s!"movzx {d.name32}, {m.str16}"]
  | .store8 m r => [s!"mov {m.str8}, {r.name8}"]
  | .store16 m r => [s!"mov {m.str16}, {r.name16}"]
  | .bswap d => [s!"bswap {d.name}"]
  | .shift op d n => [s!"{op.name} {d.name}, {n}"]
  | .shiftCl op d => [s!"{op.name} {d.name}, cl"]
  | .shiftx op d r c => [s!"{op.name} {d.name}, {r.name}, {c.name}"]
  -- `movabs` always selects the `REX.W + B8+rd io` encoding, whatever the value.
  | .movImm64 d v => [s!"movabs {d.name}, {v.toInt}"]
  | .leaSym d name => [s!"lea {d.name}, [rip + {name}]"]
  | .movdquLoad d m => [s!"movdqu {d.name}, {m.str128}"]
  | .movdquStore m r => [s!"movdqu {m.str128}, {r.name}"]
  | .movqR d r => [s!"movq {d.name}, {r.name}"]
  | .xop op => [op.asm]
  | .vop op => [op.asm]
  | .vmovdquLoad l d m => [s!"vmovdqu {d.vname l}, {m.strV l}"]
  | .vmovdquTbl d m .. => [s!"vmovdqu {d.vname .l256}, {m.strV .l256}"]
  | .movdquTbl d m .. => [s!"movdqu {d.name}, {m.str128}"]
  | .vmovdquStore l m r => [s!"vmovdqu {m.strV l}, {r.vname l}"]
  | .vbroadcasti128 d m => [s!"vbroadcasti128 {d.yname}, {m.str128}"]
  | .vbinLoad op l d a m => [s!"{op.name} {d.vname l}, {a.vname l}, {m.strV l}"]
  | .vpmovmskb l d r => [s!"vpmovmskb {d.name32}, {r.vname l}"]
  | .zop op => [op.asm]
  | .vmovdqu32Load d m => [s!"vmovdqu32 {d.zname}, {m.str512}"]
  | .vmovdqu32Store m r => [s!"vmovdqu32 {m.str512}, {r.zname}"]
  | .vbroadcasti32x4H d m => [s!"vbroadcasti32x4 {d.zname}, {m.str128}"]
  | .vbroadcasti32x4 d m => [s!"vbroadcasti32x4 {d.zname}, {m.str128}"]
  | .zbcst op d a m => [s!"{op.name} {d.zname}, {a.zname}, {m.str}" ++ "{1to8}"]
  | .vpbroadcastdZ d m => [s!"vpbroadcastd {d.zname}, {m.str32}"]
  | .zbcstd op d a m => [s!"{op.name} {d.zname}, {a.zname}, {m.str32}" ++ "{1to16}"]
  | .vpmadd52Load hi d a m =>
    [s!"vpmadd52{if hi then "h" else "l"}uq {d.vname .l256}, {a.vname .l256}, {m.strV .l256}"]
  | .eop op => [op.asm]
  | .evLoad d m => [s!"vmovdqu64 {d.yname}, {m.strV .l256}"]
  | .evStore m r => [s!"vmovdqu64 {m.strV .l256}, {r.yname}"]
  | .evMadd52Load hi d a m =>
    [s!"vpmadd52{if hi then "h" else "l"}uq {d.yname}, {a.yname}, {m.strV .l256}"]
  | .e5op op => [op.asm]
  | .evBroadcastLoad d m => [s!"vpbroadcastq {d.yname}, {m.str}"]
  | .e5InsertLoad d a m n => [s!"vinserti64x4 {d.zname}, {a.zname}, {m.strV .l256}, {n.toNat}"]
  | .e5ExtractStore m r n => [s!"vextracti64x4 {m.strV .l256}, {r.zname}, {n.toNat}"]
  | .kLoad k d m => [s!"kmovw k1, {k.name32}", s!"vmovdqu64 {d.zname} " ++ "{k1}{z}" ++ s!", {m.str512}"]
  | .kStore m k r => [s!"kmovw k1, {k.name32}", s!"vmovdqu64 {m.str512} " ++ "{k1}" ++ s!", {r.zname}"]
  | .kLoad8 k d m => [s!"kmovq k1, {k.name}", s!"vmovdqu8 {d.zname} " ++ "{k1}{z}" ++ s!", {m.str512}"]
  | .kStore8 m k r => [s!"kmovq k1, {k.name}", s!"vmovdqu8 {m.str512} " ++ "{k1}" ++ s!", {r.zname}"]
  | .vpcmpltuw d a b => [s!"vpcmpuw k1, {a.zname}, {b.zname}, 1", s!"kmovd {d.name32}, k1"]
  | .stmxcsr m => [s!"stmxcsr {m.str32}"]
  | .ldmxcsr m => [s!"ldmxcsr {m.str32}"]
  | .lfence => ["lfence"]
  | .mul r => [s!"mul {r.name}"]
  | .callr r => [s!"call {r.name}"]
  | .imul d r => [s!"imul {d.name}, {r.name}"]
  | .imul3 d r v => [s!"imul {d.name}, {r.name}, {v.toInt}"]
  | .shld d r n => [s!"shld {d.name}, {r.name}, {n}"]
  | .btr d n => [s!"btr {d.name}, {n}"]
  | .mulx hi lo s => [s!"mulx {hi.name}, {lo.name}, {s.str}"]
  | .adcx d s => [s!"adcx {d.name}, {s.str}"]
  | .adox d s => [s!"adox {d.name}, {s.str}"]
  | .cmov c d s => [s!"cmov{c.name} {d.name}, {s.str}"]
  | .push rs => rs.map fun r => s!"push {r.name}"
  | .pop r k => List.replicate k s!"pop {r.name}"
  | .alloc bytes => [s!"lea rsp, [rsp-{bytes}]"]
  | .free bytes => [s!"lea rsp, [rsp+{bytes}]"]

/-- Whether the displacement of `m` fits in the 32-bit field it is encoded
in, which the processor sign-extends: `-2^31 ≤ disp < 2^31`. SDM Vol. 2
§2.1.5, "Addressing-Mode Encoding of ModR/M and SIB Bytes" (Tables 2-2 and
2-3: the displacement of a ModR/M or SIB memory operand is `disp8` or
`disp32`), and §2.2.1.3, "Displacement", on 64-bit mode: "The ModR/M and
SIB displacement sizes do not change. They remain 8 bits or 32 bits and are
sign-extended to 64 bits." The model adds `disp` to the address as an
unbounded integer (`State.ea`), and an assembler given a wider one may
silently truncate it (LLVM before 22 does), so such an operand must not be
printed. -/
def MemOp.dispOk (m : MemOp) : Bool := decide (-2 ^ 31 ≤ m.disp ∧ m.disp < 2 ^ 31)

def Src.memOps : Src → List MemOp
  | .reg _ | .imm _ => []
  | .mem m => [m]

/-- The memory operands of an instruction. -/
def Instr.memOps : Instr → List MemOp
  | .mov _ s | .alu _ _ s | .mov32 _ s | .alu32 _ _ s | .mulx _ _ s | .adcx _ s | .adox _ s
  | .cmov _ _ s => s.memOps
  | .aluTbl _ _ m .. => [m]
  | .store m _ | .store32 m _ | .movzx8 _ m | .movzx16 _ m | .store8 m _ | .store16 m _ | .movdquLoad _ m
  | .movdquStore m _ | .movdquTbl _ m ..
  | .vmovdquLoad _ _ m | .vmovdquStore _ m _ | .vmovdquTbl _ m .. | .vbroadcasti128 _ m | .vbinLoad _ _ _ _ m
  | .vmovdqu32Load _ m | .vmovdqu32Store m _ | .vbroadcasti32x4 _ m | .vbroadcasti32x4H _ m | .zbcst _ _ _ m | .vpmadd52Load _ _ _ m
  | .vpbroadcastdZ _ m | .zbcstd _ _ _ m
  | .evLoad _ m | .evStore m _ | .evMadd52Load _ _ _ m | .kLoad _ _ m | .kStore m _ _
  | .kLoad8 _ _ m | .kStore8 m _ _ | .evBroadcastLoad _ m | .e5InsertLoad _ _ m _ | .e5ExtractStore m _ _
  | .stmxcsr m | .ldmxcsr m => [m]
  | .shift32 .. | .bswap32 _ | .rorx32 .. | .andn32 .. | .rorx .. | .andn .. | .bswap _
  | .shift .. | .shiftCl .. | .shiftx .. | .movImm64 .. | .leaSym .. | .movqR .. | .xop _ | .vop _
  | .vpmovmskb .. | .zop _ | .eop _ | .e5op _ | .vpcmpltuw ..
  | .lfence | .mul _ | .imul .. | .imul3 .. | .shld .. | .btr ..
  | .push _ | .pop .. | .alloc _ | .free _ | .callr _ => []

/-- The lines of an instruction: each of its instructions' text (`asm`) as a
comment, then that instruction's bytes (`encode`); its text if it has no
encoding (`leaSym`, printed by `symLines`, or an instruction that
`unencodable` reports, which the emitter refuses). -/
def Instr.code (i : Instr) : List String :=
  match i.encode with
  | some bs => (i.asm.zip bs).flatMap fun (t, b) => [s!"// {t}", byteLine b]
  | none => i.asm

/-- The mnemonics of Intel's list of the instructions MXCSR-configuration-dependent
timing affects ("MCDT Data Operand Independent Timing Instructions", Table 1),
as `ci/check_mcdt.py` lists them; the model has only some of them (see "MCDT"
in `Isa.lean`). -/
def mcdtMnemonics : List String :=
  ["pmaddubsw", "pmaddwd", "pmuldq", "pmulhrsw", "pmulhuw", "pmulhw", "pmulld", "pmullw",
    "pmuludq", "vplzcntd", "vplzcntq", "vpmadd52huq", "vpmadd52luq", "vpmaddubsw", "vpmaddwd",
    "vpmuldq", "vpmulhrsw", "vpmulhuw", "vpmulhw", "vpmulld", "vpmullq", "vpmullw", "vpmuludq"]

/-- Whether the text of `i` (`asm`) has an instruction of Intel's list: one
whose mnemonic, its first word, is among `mcdtMnemonics`. -/
def Instr.mcdt (i : Instr) : Bool :=
  i.asm.any fun t => mcdtMnemonics.contains ((t.splitOn " ").headD "")

/-- `test eax, eax` and a branch on `e` (`je`), after a call of `vg_mcdt_enter`:
the branch is taken exactly when it returned 0 (ZF is set exactly when
`eax`, its `u32` result, is 0), so that the code it skips runs only once it
has returned 1 (`Printer.mcdtGuard`). -/
def Instr.mcdtGuard : Instr → Cond → Bool
  | .alu32 .test .rax (.reg .rax), .e => true
  | _, _ => false

def printer : Printer isa where
  instr := Instr.code
  branch c l := [s!"j{c.name} {l}"]
  jump l := s!"jmp {l}"
  ret := ["// ret", byteLine retBytes]
  call := "call"
  -- The static's RIP-relative address, which `TCB/Rust.lean` writes with
  -- its symbol; `asm` gives the same text, for reading.
  symLines
    | .leaSym d name => some [.sym s!"lea {d.name}, " .ripRel name]
    | _ => none
  tables
    | .aluTbl _ _ _ name ws => [(name, ws)]
    | .vmovdquTbl _ _ name ws => [(name, ws)]
    | .movdquTbl _ _ name ws => [(name, ws)]
    | _ => []
  /- Every function starts on a 64-byte boundary, a cache line: the unit
  AMD's op cache builds its entries from (Zen 4 Software Optimization Guide,
  57647, §2.9.1), and one of the 16- and 32-byte windows Intel's decoders and
  decoded ICache work in. So where a function's code, and its loops, lie
  relative to them is fixed by the function alone: a change to other code
  cannot move them, and with them its performance. -/
  funcAlign := [".p2align 6"]
  mcdt := Instr.mcdt
  mcdtGuard := Instr.mcdtGuard
  unencodable
    | .leaSym .. => none
    | i => match i.memOps.filter (!·.dispOk) with
      | [] => if i.encode.isNone then some "an operand does not fit its field" else none
      | m :: _ => some s!"the displacement of the memory operand {m.addr} does not fit in 32 bits"

/-- What the emitter needs of the target (`Emitter`): its printer, its Rust `cfg`
and ABI string, and how documentation names its calling convention's
argument area and reserved memory (`abi`'s `argArea` and `reserved`). -/
instance : Emitter isa where
  printer := printer
  -- x32 targets (`x86_64-unknown-linux-gnux32`) have 32-bit pointers. The
  -- model's baseline includes SSE2 (see `Instr.requires`), which
  -- `x86_64-unknown-none` and `x86_64-unknown-uefi` turn off; there the Rust
  -- caller would also not save the SSE registers, of which UEFI's convention
  -- (the Microsoft x64 one) makes `xmm6`–`xmm15` callee-saved.
  rustCfg := "all(target_arch = \"x86_64\", target_pointer_width = \"64\", \
    target_feature = \"sse2\")"
  rustAbi := "sysv64"
  argAreaDoc ws := if ws.length - argRegs.length = 0 then none else
    some ("the arguments on the stack", false)
  reservedDoc n := some (if n = 0 then "the return address on the stack" else
    s!"the return address on the stack or the {n} bytes of stack below it")

end VG.X86_64
