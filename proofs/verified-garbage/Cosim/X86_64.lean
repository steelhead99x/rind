import Cosim.Common
import VerifiedGarbage.TCB.X86_64.Print

/-!
# Cosimulating VG's x86-64 model

Each instruction of VG's code, as its assembly file prints it, is parsed
back into every `Instr` whose text (`Instr.asm`) is exactly that line: so
which instruction of the model the text means is VG's printer's, not this
parser's, which may be loose. Each is then run in the model from random
states, and the runner runs its machine code from the same states.
-/

namespace Cosim.X86_64

open VG VG.X86_64

def regs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]
def xregs : List XReg :=
  [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7,
    .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14, .xmm15]
def hregs : List HReg :=
  [.xmm16, .xmm17, .xmm18, .xmm19, .xmm20, .xmm21, .xmm22, .xmm23,
    .xmm24, .xmm25, .xmm26, .xmm27, .xmm28, .xmm29, .xmm30, .xmm31]
def vregs : List VReg := xregs.map .lo ++ hregs.map .hi

def aluOps : List AluOp := [.add, .adc, .sub, .sbb, .and, .or, .xor, .cmp, .test]
def shiftOps : List ShiftOp := [.ror, .shr, .shl]
def varShiftOps : List VarShiftOp := [.shl, .shr, .sar]
def shiftxOps : List ShiftxOp := [.shlx, .shrx]
def conds : List Cond := [.e, .ne, .b, .ae]
def xBinOps : List XBinOp :=
  [.movdqa, .paddd, .pxor, .por, .punpckldq, .punpckhdq, .punpcklqdq, .punpckhqdq,
    .pshufb, .sha256msg1, .sha256msg2, .sha1msg1, .sha1msg2, .sha1nexte,
    .pand, .pandn, .paddq, .psubq, .pmuludq,
    .paddw, .psubw, .psubd, .pmullw, .pmulhw, .packssdw, .punpcklwd, .punpckhwd,
    .pmaddwd, .pmulhrsw, .pcmpgtw, .packsswb,
    .aesenc, .aesenclast, .aesdec, .aesdeclast, .aesimc, .pcmpeqd]
def xShiftOps : List XShiftOp :=
  [.pslld, .psrld, .psllq, .psrlq, .pslldq, .psrldq, .psllw, .psrlw, .psraw, .psrad]
def vBinOps : List VBinOp :=
  [.vpaddd, .vpaddq, .vpxor, .vpor, .vpand, .vpandn, .vpshufb, .vpmuludq,
    .vpunpckldq, .vpunpckhdq, .vpunpcklqdq, .vpunpckhqdq,
    .vpaddw, .vpsubw, .vpsubd, .vpmullw, .vpmulhw, .vpackssdw, .vpunpcklwd, .vpunpckhwd,
    .vpmaddwd, .vpmulhrsw, .vpcmpgtw, .vpacksswb, .vpsubq,
    .vaesenc, .vaesenclast, .vaesdec, .vaesdeclast, .vpcmpeqd]
def vVarOps : List VVarOp := [.vpsllvd, .vpsrlvd, .vpsllvq, .vpsrlvq]
def zBinOps : List ZBinOp :=
  [.vpaddd, .vpxord, .vpunpckldq, .vpunpckhdq, .vpunpcklqdq, .vpunpckhqdq,
    .vpaddq, .vpmuludq, .vpandq, .vporq, .vpandnq,
    .vaesenc, .vaesenclast, .vaesdec, .vaesdeclast, .vpshufb, .vpsubq]
def zShiftOps : List ZShiftOp := [.vpsllq, .vpsrlq]
def zKeyOps : List ZKeyOp := [.vpxord, .vaesenc, .vaesenclast, .vpaddd]
def zBcstOps : List ZBcstOp := [.vpmuludq, .vpandq, .vporq]
def eBinOps : List EBinOp := [.vpaddq, .vpsubq, .vpxorq, .vpandq, .vporq]
def lens : List VLen := [.l128, .l256]
def bools : List Bool := [false, true]

def _root_.VG.X86_64.Reg.idx (r : Reg) : Nat := regs.idxOf r
def _root_.VG.X86_64.XReg.idx (r : XReg) : Nat := xregs.idxOf r
def _root_.VG.X86_64.HReg.idx (r : HReg) : Nat := hregs.idxOf r

/-! ## Parsing -/

/-- The values of `xs` that `name` prints as `s`. -/
def named {α} (xs : List α) (name : α → String) (s : String) : List α := xs.filter (name · == s)

def imm8 (s : String) : List (BitVec 8) :=
  match s.toNat? with
  | some n => if n < 256 then [BitVec.ofNat 8 n] else []
  | none => []

def nat (s : String) : List Nat := s.toNat?.toList

def int32 (s : String) : List (BitVec 32) := (parseInt s).toList.map (BitVec.ofInt 32)
def int64 (s : String) : List (BitVec 64) := (parseInt s).toList.map (BitVec.ofInt 64)

/-- `SIZE PTR [base+index*scale+disp]`, the size and the operand; the
printer's own text decides whether this read it right. -/
def memOp (s : String) : List (String × MemOp) := Id.run do
  let some (size, rest) := (match s.splitOn " PTR [" with
    | [size, rest] => some (size, rest) | _ => none) | return []
  let some inner := rest.dropEnd 1 |>.toString |> fun i => if rest.endsWith "]" then some i else none
    | return []
  -- Split before each `+` or `-`, keeping the sign.
  let mut parts : List String := []
  let mut cur := ""
  for c in inner.toList do
    if (c == '+' || c == '-') && cur != "" then
      parts := parts ++ [cur]
      cur := if c == '-' then "-" else ""
    else
      cur := cur.push c
  parts := parts ++ [cur]
  match parts with
  | [] => return []
  | b :: more =>
    let some base := regs.find? (·.name == b) | return []
    let mut index : Option Reg := none
    let mut scale := 1
    let mut disp : Int := 0
    for p in more do
      match p.splitOn "*" with
      | [i, sc] =>
        let some r := regs.find? (·.name == i) | return []
        let some n := sc.toNat? | return []
        index := some r
        scale := n
      | _ =>
        let some d := parseInt p | return []
        disp := d
    return [(size, { base, index, scale, disp })]

def mem (size : String) (s : String) : List MemOp :=
  (memOp s).filterMap fun (z, m) => if z == size then some m else none

/-- A source operand: a register, an immediate or a quadword (or, with
`w32`, a doubleword and 32-bit register). -/
def src (w32 : Bool) (s : String) : List Src :=
  (named regs (if w32 then Reg.name32 else Reg.name) s).map .reg ++
  (int32 s).map .imm ++ (mem (if w32 then "DWORD" else "QWORD") s).map .mem

/-- The register and vector length of an `xmm` or `ymm` name. -/
def vlen (s : String) : List (XReg × VLen) :=
  (named xregs XReg.name s).map (·, .l128) ++ (named xregs XReg.yname s).map (·, .l256)

/-- The placeholder static of a table instruction: the case gives its
address and words. -/
def tbl : String := "T"

/-- Every instruction one line of text can be, that `Instr.asm` prints as
it. -/
def single (line : String) : List Instr := Id.run do
  let (m, rest) := match line.splitOn " " with
    | [] => ("", "")
    | m :: r => (m, " ".intercalate r)
  let a := if rest == "" then [] else fields rest ","
  let r64 := named regs Reg.name
  let r32 := named regs Reg.name32
  let r16 := named regs Reg.name16
  let r8 := named regs Reg.name8
  let x := named xregs XReg.name
  let y := named xregs XReg.yname
  let z := named xregs XReg.zname
  let hz := named hregs HReg.zname
  let vx := named vregs VReg.name
  let vy := named vregs VReg.yname
  let vz := named vregs VReg.zname
  let mut c : List Instr := []
  match a with
  | [] =>
    c := c ++ [.lfence, .vop .vzeroupper]
  | [o] =>
    c := c ++ (r32 o).map .bswap32 ++ (r64 o).map .bswap ++ (r64 o).map .mul ++ (r64 o).map .callr
    c := c ++ (mem "DWORD" o).map .stmxcsr ++ (mem "DWORD" o).map .ldmxcsr
    c := c ++ (r64 o).map (.push [·]) ++ (r64 o).map (.pop · 1)
  | [d, s] =>
    c := c ++ (do let d ← r64 d; let s ← src false s; [.mov d s])
    c := c ++ (do let m ← mem "QWORD" d; let r ← r64 s; [.store m r])
    c := c ++ (do let op ← named aluOps AluOp.name m; let d ← r64 d; let s ← src false s
                  [.alu op d s] ++ (match s with
                    | .mem mo => [.aluTbl op d mo tbl []]
                    | _ => []))
    c := c ++ (do let d ← r32 d; let s ← src true s; [.mov32 d s])
    c := c ++ (do let m ← mem "DWORD" d; let r ← r32 s; [.store32 m r])
    c := c ++ (do let op ← named aluOps AluOp.name m; let d ← r32 d; let s ← src true s; [.alu32 op d s])
    c := c ++ (do let op ← named shiftOps ShiftOp.name m; let d ← r32 d; let n ← nat s; [.shift32 op d n])
    c := c ++ (do let op ← named shiftOps ShiftOp.name m; let d ← r64 d; let n ← nat s; [.shift op d n])
    c := c ++ (do let op ← named varShiftOps VarShiftOp.name m; let d ← r64 d
                  if s == "cl" then [.shiftCl op d] else [])
    c := c ++ (do let d ← r32 d; let mo ← mem "BYTE" s; [.movzx8 d mo])
    c := c ++ (do let d ← r32 d; let mo ← mem "WORD" s; [.movzx16 d mo])
    c := c ++ (do let mo ← mem "BYTE" d; let r ← r8 s; [.store8 mo r])
    c := c ++ (do let mo ← mem "WORD" d; let r ← r16 s; [.store16 mo r])
    c := c ++ (do let d ← r64 d; let v ← int64 s; [.movImm64 d v])
    c := c ++ (do let d ← x d; let mo ← mem "XMMWORD" s; [.movdquLoad d mo, .movdquTbl d mo tbl []])
    c := c ++ (do let mo ← mem "XMMWORD" d; let r ← x s; [.movdquStore mo r])
    c := c ++ (do let d ← r64 d; let r ← x s; [.movqR d r])
    c := c ++ (do let d ← x d; let r ← r64 s; [.xop (.movq d r)])
    c := c ++ (do let op ← named xShiftOps XShiftOp.name m; let d ← x d; let n ← imm8 s; [.xop (.shift op d n)])
    c := c ++ (do let op ← named xBinOps XBinOp.name m; let d ← x d; let r ← x s; [.xop (.bin op d r)])
    c := c ++ (do let (d, l) ← vlen d; let mo ← mem (if l == .l128 then "XMMWORD" else "YMMWORD") s
                  [.vmovdquLoad l d mo] ++ (if l == .l256 then [.vmovdquTbl d mo tbl []] else []))
    c := c ++ (do let mo ← memOp d; let (r, l) ← vlen s
                  if mo.1 == (if l == .l128 then "XMMWORD" else "YMMWORD") then [.vmovdquStore l mo.2 r]
                  else [])
    c := c ++ (do let d ← y d; let mo ← mem "XMMWORD" s; [.vbroadcasti128 d mo])
    c := c ++ (do let d ← r32 d; let (r, l) ← vlen s; [.vpmovmskb l d r])
    c := c ++ (do let d ← z d; let mo ← mem "ZMMWORD" s; [.vmovdqu32Load d mo])
    c := c ++ (do let mo ← mem "ZMMWORD" d; let r ← z s; [.vmovdqu32Store mo r])
    c := c ++ (do let d ← hz d; let mo ← mem "XMMWORD" s; [.vbroadcasti32x4H d mo])
    c := c ++ (do let d ← z d; let mo ← mem "XMMWORD" s; [.vbroadcasti32x4 d mo])
    c := c ++ (do let d ← z d; let mo ← mem "DWORD" s; [.vpbroadcastdZ d mo])
    c := c ++ (do let d ← vy d; let mo ← mem "YMMWORD" s; [.evLoad d mo])
    c := c ++ (do let mo ← mem "YMMWORD" d; let r ← vy s; [.evStore mo r])
    c := c ++ (do let d ← vy d; let mo ← mem "QWORD" s; [.evBroadcastLoad d mo])
    c := c ++ (do let d ← r64 d; let r ← r64 s; [.imul d r])
    c := c ++ (do let d ← r64 d; let n ← nat s; [.btr d n])
    c := c ++ (do let d ← r64 d; let s ← src false s; [.adcx d s, .adox d s])
    c := c ++ (do let cc ← named conds (fun c => "cmov" ++ c.name) m; let d ← r64 d; let s ← src false s
                  [.cmov cc d s])
    -- `lea rsp, [rsp-N]` and `lea rsp, [rsp+N]`, which `memOp` reads without its size.
    c := c ++ (do let n ← nat ((s.drop "[rsp-".length).dropEnd 1).toString; [.alloc n])
    c := c ++ (do let n ← nat ((s.drop "[rsp+".length).dropEnd 1).toString; [.free n])
    -- VOp, ZOp, EOp and E5Op of two registers.
    c := c ++ (do let (d, l) ← vlen d; let (r, l') ← vlen s
                  if l != l' then [] else [.vop (.vmovdqa l d r)])
    c := c ++ (do let (d, l) ← vlen d; let r ← x s; [.vop (.vpbroadcastd l d r), .vop (.vpbroadcastq l d r)])
    c := c ++ (do let d ← x d; let r ← r64 s; [.vop (.vmovq d r)])
    c := c ++ (do let d ← y d; let r ← x s; [.vop (.vsha512msg1 d r)])
    c := c ++ (do let d ← y d; let r ← y s; [.vop (.vsha512msg2 d r)])
    c := c ++ (do let d ← z d; let r ← x s; [.zop (.vpbroadcastq d r)])
    c := c ++ (do let d ← z d; let r ← z s; [.zop (.vmovdqa64 d r)])
    c := c ++ (do let d ← vy d; let r ← vx s; [.eop (.vpbroadcastq d r)])
    c := c ++ (do let d ← vx d; let r ← r64 s; [.eop (.vmovq d r)])
    c := c ++ (do let d ← vx d; let r ← vx s; [.eop (.vmovqx d r)])
    c := c ++ (do let d ← vy d; let r ← vy s; [.eop (.vmovdqa64 d r)])
  | [d, s, t] =>
    c := c ++ (do let d ← r32 d; let r ← r32 s; let n ← nat t; [.rorx32 d r n])
    c := c ++ (do let d ← r32 d; let a ← r32 s; let b ← r32 t; [.andn32 d a b])
    c := c ++ (do let d ← r64 d; let r ← r64 s; let n ← nat t; [.rorx d r n, .shld d r n])
    c := c ++ (do let d ← r64 d; let a ← r64 s; let b ← r64 t; [.andn d a b])
    c := c ++ (do let op ← named shiftxOps ShiftxOp.name m; let d ← r64 d; let r ← r64 s; let cn ← r64 t
                  [.shiftx op d r cn])
    c := c ++ (do let d ← r64 d; let r ← r64 s; let v ← int32 t; [.imul3 d r v])
    c := c ++ (do let hi ← r64 d; let lo ← r64 s; let s ← src false t; [.mulx hi lo s])
    -- XOp with an immediate.
    c := c ++ (do let d ← x d; let r ← x s; let n ← imm8 t
                  [.xop (.pshufd d r n), .xop (.palignr d r n), .xop (.pblendw d r n), .xop (.sha1rnds4 d r n),
                    .xop (.aeskeygenassist d r n), .xop (.pclmulqdq d r n)])
    c := c ++ (do let d ← x d; let r ← x s; if t == "xmm0" then [.xop (.sha256rnds2 d r)] else [])
    -- VOp of three registers or two and an immediate.
    c := c ++ (do let (d, l) ← vlen d; let (a, la) ← vlen s; let (b, lb) ← vlen t
                  if l != la || l != lb then [] else
                  (named vBinOps VBinOp.name m).map (fun op => .vop (.vbin op l d a b)) ++
                  (named vVarOps VVarOp.name m).map (fun op => .vop (.vvar op l d a b)) ++
                  [.vop (.vpmadd52luq l d a b), .vop (.vpmadd52huq l d a b)])
    c := c ++ (do let (d, l) ← vlen d; let (r, l') ← vlen s; let n ← imm8 t
                  if l != l' then [] else
                  (named xShiftOps XShiftOp.name (m.drop 1).toString).map (fun op => .vop (.vshift op l d r n)) ++
                  [.vop (.vpshufd l d r n), .vop (.vprold l d r n), .vop (.vprorq l d r n)])
    c := c ++ (do let (d, l) ← vlen d; let (a, la) ← vlen s; let mo ← mem (if l == .l128 then "XMMWORD" else "YMMWORD") t
                  if l != la then [] else (named vBinOps VBinOp.name m).map (fun op => .vbinLoad op l d a mo))
    c := c ++ (do let d ← y d; let r ← y s; let n ← imm8 t; [.vop (.vpermq d r n)])
    c := c ++ (do let d ← y d; let i ← y s; let r ← y t; [.vop (.vpermd d i r)])
    c := c ++ (do let d ← x d; let r ← y s; let n ← imm8 t; [.vop (.vextracti128 d r n)])
    c := c ++ (do let d ← y d; let a ← y s; let b ← x t; [.vop (.vsha512rnds2 d a b)])
    c := c ++ (do let hi ← bools; let d ← y d; let a ← y s; let mo ← mem "YMMWORD" t; [.vpmadd52Load hi d a mo])
    -- ZOp.
    c := c ++ (do let d ← z d; let a ← z s; let b ← z t
                  (named zBinOps ZBinOp.name m).map (fun op => .zop (.zbin op d a b)) ++
                  [.zop (.vpmadd52 false d a b), .zop (.vpmadd52 true d a b), .zop (.vpermw d a b),
                    .zop (.vpsrlvw d a b)])
    c := c ++ (do let d ← z d; let a ← z s; let b ← hz t
                  (named zKeyOps ZKeyOp.name m).map (fun op => .zop (.zbinH op d a b)))
    c := c ++ (do let d ← z d; let r ← z s; let n ← imm8 t
                  (named zShiftOps ZShiftOp.name m).map (fun op => .zop (.vshift op d r n)) ++
                  [.zop (.vprold d r n), .zop (.vpshufd d r n), .zop (.vpslldq d r n), .zop (.vpsrldq d r n),
                    .zop (.vprorq d r n), .zop (.vpermq d r n)])
    c := c ++ (do let d ← x d; let r ← z s; let n ← imm8 t; [.zop (.vextracti32x4 d r n)])
    c := c ++ (do let d ← z d; let a ← z s
                  let mo ← mem "QWORD" ((t.dropEnd "{1to8}".length).toString)
                  if t.endsWith "{1to8}" then (named zBcstOps ZBcstOp.name m).map (fun op => .zbcst op d a mo)
                  else [])
    c := c ++ (do let d ← z d; let a ← z s
                  let mo ← mem "DWORD" ((t.dropEnd "{1to16}".length).toString)
                  if t.endsWith "{1to16}" && m == "vpaddd" then [.zbcstd .vpaddd d a mo] else [])
    -- EOp and E5Op.
    c := c ++ (do let d ← vy d; let a ← vy s; let b ← vy t
                  (named eBinOps EBinOp.name m).map (fun op => .eop (.bin op d a b)) ++
                  [.eop (.vpmadd52 false d a b), .eop (.vpmadd52 true d a b)])
    c := c ++ (do let d ← vy d; let r ← vy s; let n ← imm8 t
                  (named zShiftOps ZShiftOp.name m).map (fun op => .eop (.shift op d r n)) ++
                  [.eop (.vpermq d r n), .eop (.vprorq d r n), .eop (.vpsraq d r n)])
    c := c ++ (do let hi ← bools; let d ← vy d; let a ← vy s; let mo ← mem "YMMWORD" t; [.evMadd52Load hi d a mo])
    c := c ++ (do let d ← vz d; let a ← vz s; let b ← vz t
                  (named eBinOps EBinOp.name m).map (fun op => .e5op (.bin op d a b)) ++
                  [.e5op (.vpmadd52 false d a b), .e5op (.vpmadd52 true d a b)])
    c := c ++ (do let d ← vz d; let r ← vz s; let n ← imm8 t
                  (named zShiftOps ZShiftOp.name m).map (fun op => .e5op (.shift op d r n)) ++
                  [.e5op (.vpermq d r n)])
    c := c ++ (do let mo ← mem "YMMWORD" d; let r ← vz s; let n ← imm8 t; [.e5ExtractStore mo r n])
  | [d, s, t, u] =>
    c := c ++ (do let (d, l) ← vlen d; let (a, la) ← vlen s; let (b, lb) ← vlen t; let n ← imm8 u
                  if l != la || l != lb then [] else
                  [.vop (.vpclmulqdq l d a b n), .vop (.vpalignr l d a b n), .vop (.vpblendd l d a b n),
                    .vop (.vpblendw l d a b n), .vop (.vpternlogd l d a b n)])
    c := c ++ (do let d ← y d; let a ← y s; let b ← y t; let n ← imm8 u; [.vop (.vperm2i128 d a b n)])
    c := c ++ (do let d ← y d; let a ← y s; let b ← x t; let n ← imm8 u; [.vop (.vinserti128 d a b n)])
    c := c ++ (do let d ← z d; let a ← z s; let b ← z t; let n ← imm8 u
                  [.zop (.vpclmulqdq d a b n), .zop (.vshufi32x4 d a b n), .zop (.vpternlogd d a b n)])
    c := c ++ (do let d ← vy d; let a ← vy s; let b ← vy t; let n ← imm8 u
                  [.eop (.valignq d a b n), .eop (.vpternlogq d a b n)])
    c := c ++ (do let d ← vz d; let a ← vz s; let b ← vy t; let n ← imm8 u; [.e5op (.vinserti64x4 d a b n)])
    c := c ++ (do let d ← vz d; let a ← vz s; let mo ← mem "YMMWORD" t; let n ← imm8 u; [.e5InsertLoad d a mo n])
  | _ => pure ()
  return c

/-- The instructions a group of lines can be: a single line's, or a masked
move with the `kmov` before it, or `vpcmpuw` with the `kmovd` after it, or
a frame's pushes or pops. -/
def candidates (lines : List String) : List Instr :=
  let raw : List Instr := match lines with
    | [l] => single l
    | [k, l] =>
      let kr := match k.splitOn ", " with
        | [_, r] => named regs Reg.name32 r ++ named regs Reg.name r
        | _ => []
      -- `vmovdqu64 zmm0 {k1}{z}, ZMMWORD PTR [rdi]` or
      -- `vmovdqu64 ZMMWORD PTR [rdi] {k1}, zmm0`.
      let ops := match (l.splitOn " ").drop 1 |> " ".intercalate |>.splitOn ", " with
        | [a, b] => some (a, b)
        | _ => none
      let masked : List Instr := match ops with
        | some (a, b) =>
          let dst := (a.splitOn " ").headD ""
          let mo := if a.endsWith " {k1}" then (a.dropEnd " {k1}".length).toString else a
          (do let k ← kr; let d ← named xregs XReg.zname dst; let mo ← mem "ZMMWORD" b
              [.kLoad k d mo, .kLoad8 k d mo]) ++
          (do let k ← kr; let mo ← mem "ZMMWORD" mo; let r ← named xregs XReg.zname b
              [.kStore mo k r, .kStore8 mo k r])
        | none => []
      let cmp : List Instr := match k.splitOn ", " with
        | [_, a, b, _] =>
          match l.splitOn ", " with
          | [d, _] => do
            let a ← named xregs XReg.zname a; let b ← named xregs XReg.zname b
            let d ← named regs Reg.name32 ((d.drop "kmovd ".length).toString)
            [.vpcmpltuw d a b]
          | _ => []
        | _ => []
      masked ++ cmp ++ frames lines
    | _ => frames lines
  raw.filter (·.asm == lines)
where
  /-- A run of `push r` lines, or of the same `pop r`. -/
  frames (lines : List String) : List Instr :=
    let rs := lines.filterMap fun l => regs.find? (fun r => l == "push " ++ r.name)
    let ps := lines.filterMap fun l => regs.find? (fun r => l == "pop " ++ r.name)
    (if rs.length == lines.length then [.push rs] else []) ++
    (match ps with
      | r :: _ => if ps.length == lines.length then [.pop r ps.length] else []
      | [] => [])

/-! ## States -/

/-- What the runner loads and stores: the general-purpose registers (in
`regs`' order), CF, ZF, SF and OF, MXCSR, `zmm0`–`zmm31`, and the data. -/
structure Img where
  gpr : Array (BitVec 64)
  cf : Bool
  zf : Bool
  sf : Bool
  of : Bool
  mxcsr : BitVec 32
  zmm : Array (BitVec 512)
  data : ByteArray

def stateLen : Nat := 16 * 8 + 4 + 4 + 32 * 64 + dataLen

def Img.encode (i : Img) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity stateLen
  for v in i.gpr do
    b := pushBV b v
  let fl := (if i.cf then 1 else 0) + (if i.zf then 2 else 0) + (if i.sf then 4 else 0) + (if i.of then 8 else 0)
  b := pushLE b fl 4
  b := pushBV b i.mxcsr
  for v in i.zmm do
    b := pushBV b v
  return b ++ i.data

def window : Region := ⟨BitVec.ofNat 64 windowBase, windowLen⟩

/-- The model's state of `i`, which may access only the window. -/
def Img.state (i : Img) (ret : Nat := 0) : State :=
  let data := i.data
  { gpr := fun r => i.gpr[r.idx]!
    cf := some i.cf, zf := some i.zf, sf := some i.sf, of := some i.of
    xmm := fun r => (i.zmm[r.idx]!).extractLsb' 0 128
    ymmHi := fun r => (i.zmm[r.idx]!).extractLsb' 128 128
    zmmHi := fun r => (i.zmm[r.idx]!).extractLsb' 256 256
    ymmH := fun r => (i.zmm[16 + r.idx]!).extractLsb' 0 256
    zmmHiH := fun r => (i.zmm[16 + r.idx]!).extractLsb' 256 256
    mxcsr := i.mxcsr
    mem := fun a =>
      let o := (a - BitVec.ofNat 64 dataBase).toNat
      if o < dataLen then BitVec.ofNat 8 (data.get! o).toNat else 0
    rd := []
    wr := [window]
    unknowns := fun n => if n = 0 then BitVec.ofNat 64 ret else 0
    syms := fun _ => 0 }

/-- The image of the model's state `s`, and which of its flags are defined
(bit 0 CF, 1 ZF, 2 SF, 3 OF). -/
def ofState (s : State) : Img × Nat :=
  let flag (f : Option Bool) := f.getD false
  let mask := (if s.cf.isSome then 1 else 0) + (if s.zf.isSome then 2 else 0) +
    (if s.sf.isSome then 4 else 0) + (if s.of.isSome then 8 else 0)
  let data := Id.run do
    let mut d := ByteArray.emptyWithCapacity dataLen
    for o in [0:dataLen] do
      d := d.push (s.mem (BitVec.ofNat 64 (dataBase + o))).toNat.toUInt8
    return d
  ({ gpr := regs.toArray.map s.gpr
     cf := flag s.cf, zf := flag s.zf, sf := flag s.sf, of := flag s.of
     mxcsr := s.mxcsr
     zmm := xregs.toArray.map s.zmm ++ hregs.toArray.map fun r => s.zmmHiH r ++ s.ymmH r
     data }, mask)

def randomImg : Gen Img := do
  let mut gpr := #[]
  for _ in regs do
    gpr := gpr.push (← val64)
  let mut zmm := #[]
  for _ in [0:32] do
    zmm := zmm.push (← bits 512)
  -- Within the window, so a push, a call or a stack access stays in it.
  gpr := gpr.set! (Reg.idx .rsp) (BitVec.ofNat 64 (windowBase + windowLen / 2 + 8 * (← below 16) - 64))
  return { gpr, cf := ← bool, zf := ← bool, sf := ← bool, of := ← bool
           mxcsr := BitVec.ofNat 32 ((← below 65536))
           zmm, data := ← bytes dataLen }

def Img.setReg (i : Img) (r : Reg) (v : Nat) : Img := { i with gpr := i.gpr.set! r.idx (BitVec.ofNat 64 v) }

def Img.poke (i : Img) (a : Nat) (v : Nat) (n : Nat) : Img := Id.run do
  let mut d := i.data
  let mut v := v
  for j in [0:n] do
    d := d.set! (a - dataBase + j) (v % 256).toUInt8
    v := v / 256
  return { i with data := d }

/-- The memory operands of `i` (`Instr.memOps`). -/
def memOps (i : Instr) : List MemOp := i.memOps

/-- Points the memory operand `m` of a case at the window, by its base
register: the access at `ea` of up to 64 bytes, at a random offset. -/
def placeMem (img : Img) (m : MemOp) : Gen Img := do
  let a := windowBase + (← below (windowLen - 64))
  let idx := match m.index with
    | some r => (img.gpr[r.idx]!).toNat * m.scale
    | none => 0
  return img.setReg m.base (((a : Int) - m.disp - idx) % 2 ^ 64).toNat

/-- The offsets into its table a table instruction's operand `m` can read
a word at: a non-negative multiple of 8, from its displacement and, with an
index other than its base, the index scaled, up to 32 words past the
displacement. None for any other operand, which is not one VG's code can
hold, so that reading of the text has no case. -/
def tblOffsets (m : MemOp) : List Nat :=
  match m.index with
  | none => if m.disp ≥ 0 ∧ m.disp % 8 = 0 then [m.disp.toNat] else []
  | some r =>
    if r == m.base then [] else
    let first := (max m.disp 0).toNat / 8 * 8
    ((List.range 34).map fun j => first + 8 * j).filter fun (o : Nat) =>
      decide ((o : Int) ≥ m.disp) && ((o : Int) - m.disp) % (m.scale : Int) == 0

/-- The words of a table instruction's static, at `m`'s base: random, and
in memory at the address read, so the CPU reads what the model does. -/
def placeTbl (img : Img) (m : MemOp) (need : Nat) : Gen (Option (Img × List (BitVec 64))) := do
  let offs := tblOffsets m
  if offs.isEmpty then return none
  let off := offs[← below offs.length]!
  let mut img := img
  if let some r := m.index then
    img := img.setReg r (((off : Int) - m.disp) / (m.scale : Int)).toNat
  let a := windowBase + 8 * (← below ((windowLen - 64) / 8))
  let words := off / 8 + need + (← below 4)
  let mut ws := #[]
  for _ in [0:words] do
    ws := ws.push (← val64)
  for j in [0:need] do
    img := img.poke (a + 8 * j) ws[off / 8 + j]!.toNat 8
  return some (img.setReg m.base (a - off), ws.toList)

/-- The table of a table instruction, its operand and the words it reads. -/
def tblOf : Instr → Option (MemOp × Nat)
  | .aluTbl _ _ m .. => some (m, 1)
  | .movdquTbl _ m .. => some (m, 2)
  | .vmovdquTbl _ m .. => some (m, 4)
  | _ => none

def withWords (i : Instr) (ws : List (BitVec 64)) : Instr :=
  match i with
  | .aluTbl op d m n _ => .aluTbl op d m n ws
  | .movdquTbl d m n _ => .movdquTbl d m n ws
  | .vmovdquTbl d m n _ => .vmovdquTbl d m n ws
  | i => i

/-- What the model says `i` leaves, run from `s` (the frame instructions by
the push and pop of a frame, which also check the frame's bookkeeping). A
frame's release takes its unknowns all zero, the outcome where every
released byte keeps its value (`lose`), as each does on the CPU, where nothing
else writes memory between two instructions; a `free` may release bytes
outside the window. -/
def run (i : Instr) (s : State) : Option State :=
  match i with
  | .push _ | .alloc _ => push i s
  | .pop _ k => let s₁ := { s with unknowns := fun _ => 0, wr := ⟨s.gpr .rsp, 8 * k⟩ :: s.wr }; pop i s₁ s₁
  | .free n => let s₁ := { s with unknowns := fun _ => 0, wr := ⟨s.gpr .rsp, n⟩ :: s.wr }; pop i s₁ s₁
  | _ => exec i s

/-- A case of the straight-line instruction `i`: a start image and the
model's end image with its defined flags. Retries a state the model faults
in, as one whose memory operand wraps into its index. -/
def insnCase (i : Instr) : Gen (Option (Instr × Img × Img × Nat)) := do
  for _ in [0:32] do
    let mut img ← randomImg
    let mut i := i
    let mut ok := true
    match tblOf i with
    | some (m, need) =>
      match ← placeTbl img m need with
      | some (img', ws) => img := img'; i := withWords i ws
      | none => ok := false
    | none =>
      for m in memOps i do
        img ← placeMem img m
    -- A frame's pushes from the top of the window, its pops from the bottom.
    match i with
    | .push _ => img := img.setReg .rsp (windowBase + windowLen - 8 * (← below 4))
    | .pop _ _ => img := img.setReg .rsp (windowBase + 8 * (← below 4))
    | _ => pure ()
    if let .ldmxcsr m := i then
      -- A value with its reserved bits clear, which the model loads.
      img := img.poke ((img.state.ea m).toNat) (← below 65536) 4
    if !ok then continue
    let s := match tblOf i with
      | some (m, _) => { img.state with syms := fun _ => img.state.gpr m.base }
      | none => img.state
    if let some s' := run i s then
      let (out, mask) := ofState s'
      return some (i, img, out, mask)
  return none

/-- A case of a branch on `c`: taken or not, and nothing else changed. -/
def branchCase (c : Cond) : Gen (Option (Img × Bool)) := do
  let img ← randomImg
  return (eval c img.state).map (img, ·)

/-- A case of a call, from `code` at `insnAddr` to `targetAddr`, where a
`ret` returns; `r` holds the target of an indirect call. -/
def callCase (code : ByteArray) (r : Option Reg) : Gen (Option (Img × Img)) := do
  let mut img ← randomImg
  if let some r := r then
    img := img.setReg r targetAddr
  let s := img.state (insnAddr + code.size)
  if let some r := r then
    if icall (.callr r) s != some (BitVec.ofNat 64 targetAddr) then return none
  let some s₁ := call s | return none
  let some s' := ret s₁ s₁ | return none
  return some (img, (ofState s').1)

def rel32 (from_ : Nat) : ByteArray := pushLE .empty (((targetAddr : Int) - from_) % 2 ^ 32).toNat 4

/-- `jcc rel32` (`0F 80+cc`, SDM Vol. 2 "Jcc"): je 84, jne 85, jb 82, jae 83. -/
def jcc (c : Cond) : ByteArray :=
  let op : UInt8 := match c with | .e => 0x84 | .ne => 0x85 | .b => 0x82 | .ae => 0x83
  ByteArray.mk #[0x0F, op] ++ rel32 (insnAddr + 6)

/-- `call rel32` (`E8`, SDM Vol. 2 "CALL"). -/
def callRel : ByteArray := ByteArray.mk #[0xE8] ++ rel32 (insnAddr + 5)

def caseBytes (start out : Img) (marker : Bool) (mask : Nat) : ByteArray :=
  (start.encode ++ out.encode).push (if marker then 1 else 0) |>.push mask.toUInt8

/-- The blocks of one group of lines of VG's code, with the CPU features
each needs, `n` cases each; or why there are none. Lines that only the
linker or the assembler give meaning (a static's address, a jump) have
none. -/
def blocks (kind : String) (lines : List String) (code : ByteArray) (n : Nat) :
    Gen (Except String (List (Block × List String))) := do
  let text := "; ".intercalate lines
  match kind, lines with
  | "branch", [l] =>
    match conds.filter (fun c => l.startsWith ("j" ++ c.name ++ " ")) with
    | [c] =>
      let mut cases := #[]
      for _ in [0:n] do
        let some (img, taken) ← branchCase c | return .error s!"{text}: the model's condition is undefined"
        cases := cases.push (caseBytes img img taken 15)
      return .ok [({ text, kind := .branch, code := jcc c, cases }, [])]
    | _ => return .error s!"{text}: not a branch the model has"
  | "call", [_] =>
    let mut cases := #[]
    for _ in [0:n] do
      let some (img, out) ← callCase callRel none | return .error s!"{text}: the model's call faults"
      cases := cases.push (caseBytes img out false 15)
    return .ok [({ text := "call (direct); ret", kind := .call, code := callRel, cases }, [])]
  | "insn", _ =>
    let cs := candidates lines
    if cs.isEmpty then return .error s!"{text}: no instruction of the model prints as this"
    let mut out := []
    for i in cs do
      if let .callr r := i then
        let mut cases := #[]
        for _ in [0:n] do
          let some (img, o) ← callCase code r | return .error s!"{text}: the model's call faults"
          cases := cases.push (caseBytes img o false 15)
        out := out ++ [({ text := text ++ "; ret", kind := .call, code, cases }, [])]
        continue
      if let some (m, _) := tblOf i then
        if (tblOffsets m).isEmpty then continue
      let mut cases := #[]
      for _ in [0:n] do
        let some (_, img, o, mask) ← insnCase i
          | return .error s!"{text}: the model faults in every state tried ({repr i})"
        cases := cases.push (caseBytes img o false mask)
      out := out ++ [({ text, kind := .insn, code, cases }, i.requires)]
    if out.isEmpty then return .error s!"{text}: the model faults in every state tried"
    return .ok out
  | _, _ => return .error s!"{text}: unknown kind {kind}"

end Cosim.X86_64
