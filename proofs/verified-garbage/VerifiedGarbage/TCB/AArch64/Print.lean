module

public import VerifiedGarbage.TCB.AArch64.Encode
public import VerifiedGarbage.TCB.Print
public import VerifiedGarbage.TCB.AArch64.Target

/-!
# Printer for the AArch64 model

**Trusted.** Emits the GNU/LLVM assembler syntax used by Rust's
`asm!`/`naked_asm!` on AArch64.

Each straight-line instruction, and the return, is printed as its machine
code (`Encode.lean`), `.inst <word>`, after a line `// <the instruction's
text>`, which the emitter writes in the module's assembly file, not in its code
(`Rust.assembly`): the
assembler only copies the words. The branches (`cbz`, `cbnz`, `b`), the call
(`bl`), the address of a static (`adrp` and `add`, `symLines`) and
alignment (`.p2align`) are printed as text, for the assembler and linker to
lay out.

`align k` (`Isa.lean`) prints as `.p2align k`, which the assembler fills, in
a code section, with NOPs (`HINT #0`, `0xD503201F`: every A64 instruction is
four bytes, and every offset in a function a multiple of four, so NOPs
cover any padding). Unlike the padding after a function's `ret`
(`funcAlign`), this padding is executed when the code before it falls
through, so `align` is a NOP in the model: DDI 0487 C6.2, "NOP": "No
Operation does nothing, other than advance the value of the program counter
by 4. This instruction can be used for instruction alignment purposes." NOP
is in the base A64 instruction set, so `align` requires no feature. The
printer refuses any `k` but 4, 5 and 6 (16-, 32- and 64-byte boundaries):
padding to more than a function's own 64-byte alignment (`funcAlign`) would
not align anything relative to it.
-/

@[expose] public section

namespace VG.AArch64

/-- A condition code's mnemonic suffix. -/
def CondCode.name : CondCode → String
  | .eq => "eq" | .ne => "ne" | .hs => "hs" | .lo => "lo" | .mi => "mi" | .pl => "pl"
  | .vs => "vs" | .vc => "vc" | .hi => "hi" | .ls => "ls" | .ge => "ge" | .lt => "lt"
  | .gt => "gt" | .le => "le"

/-- `w<n>` or `x<n>`. -/
def Reg.name (sz : Size) (r : Reg) : String :=
  match sz with
  | .w => s!"w{r.index}"
  | .x => s!"x{r.index}"

/-- `v<n>.<t>` -/
def VReg.arr (r : VReg) (t : String) : String := s!"v{r.index}.{t}"

/-- `v<n>.16b` -/
def VReg.b (r : VReg) : String := r.arr "16b"

/-- `q<n>` -/
def VReg.q (r : VReg) : String := s!"q{r.index}"

/-- `s<n>` -/
def VReg.s (r : VReg) : String := s!"s{r.index}"

def VArr.name : VArr → String
  | .s4 => "4s" | .d2 => "2d" | .b16 => "16b" | .h8 => "8h"

/-- The element size of an arrangement, in an element operand (`v<n>.<t>[i]`). -/
def VArr.elem : VArr → String
  | .s4 => "s" | .d2 => "d" | .b16 => "b" | .h8 => "h"

def VLogicOp.name : VLogicOp → String
  | .and => "and" | .orr => "orr" | .eor => "eor" | .bic => "bic" | .orn => "orn"

def VShiftOp.name : VShiftOp → String
  | .shl => "shl" | .ushr => "ushr" | .sri => "sri" | .sli => "sli" | .sshr => "sshr"

def VSelOp.name : VSelOp → String
  | .bsl => "bsl" | .bit => "bit" | .bif => "bif"

/-- `{vn.16b, …}`: the `len` registers from `n`. -/
def tableList (n : VReg) (len : Nat) : String :=
  "{" ++ ", ".intercalate ((List.range len).map fun i => (Nat.repeat VReg.succ i n).b) ++ "}"

def VPermOp.name : VPermOp → String
  | .zip1 => "zip1" | .zip2 => "zip2" | .trn1 => "trn1" | .trn2 => "trn2" | .uzp1 => "uzp1"
  | .uzp2 => "uzp2"

def VMulHOp.name : VMulHOp → String
  | .mul => "mul" | .mla => "mla" | .mls => "mls" | .sqdmulh => "sqdmulh" | .sqrdmulh => "sqrdmulh"

def VCmpOp.name : VCmpOp → String
  | .hi => "cmhi" | .hs => "cmhs"

/-- The scalar register of a lane of the arrangement (`b<n>`, `h<n>`, `s<n>`,
`d<n>`), or of twice its size if `long`, as in ADDV and UADDLV. -/
def VReg.scalar (r : VReg) (a : VArr) (long : Bool) : String :=
  let p := match a, long with
    | .b16, false => "b" | .h8, false | .b16, true => "h" | .s4, false | .h8, true => "s"
    | .d2, false | .s4, true => "d" | .d2, true => "q"
  s!"{p}{r.index}"

def Sha1Op.name : Sha1Op → String
  | .c => "sha1c" | .p => "sha1p" | .m => "sha1m"

def VOp.asm : VOp → String
  | .mov d n => s!"mov {d.b}, {n.b}"
  | .movi0 d => s!"movi {d.arr "2d"}, #0"
  | .dup .s4 d n => s!"dup {d.arr "4s"}, {n.name .w}"
  | .dup .d2 d n => s!"dup {d.arr "2d"}, {n.name .x}"
  | .ins .s4 d i n => s!"mov v{d.index}.s[{i}], {n.name .w}"
  | .ins .d2 d i n => s!"mov v{d.index}.d[{i}], {n.name .x}"
  | .dup .b16 d n => s!"dup {d.b}, {n.name .w}"
  | .ins .b16 d i n => s!"mov v{d.index}.b[{i}], {n.name .w}"
  | .dup .h8 d n => s!"dup {d.arr "8h"}, {n.name .w}"
  | .ins .h8 d i n => s!"mov v{d.index}.h[{i}], {n.name .w}"
  | .dupS d n i => s!"dup {d.s}, v{n.index}.s[{i}]"
  | .dupE a d n i => s!"dup {d.arr a.name}, v{n.index}.{a.elem}[{i}]"
  | .insE a d i n j => s!"mov v{d.index}.{a.elem}[{i}], v{n.index}.{a.elem}[{j}]"
  | .cmeq a d n m => s!"cmeq {d.arr a.name}, {n.arr a.name}, {m.arr a.name}"
  | .cmp op a d n m => s!"{op.name} {d.arr a.name}, {n.arr a.name}, {m.arr a.name}"
  | .bsel op d n m => s!"{op.name} {d.b}, {n.b}, {m.b}"
  | .logic op d n m => s!"{op.name} {d.b}, {n.b}, {m.b}"
  | .not d n => s!"not {d.b}, {n.b}"
  | .add a d n m => s!"add {d.arr a.name}, {n.arr a.name}, {m.arr a.name}"
  | .sub a d n m => s!"sub {d.arr a.name}, {n.arr a.name}, {m.arr a.name}"
  | .addv a d n => s!"addv {d.scalar a false}, {n.arr a.name}"
  | .uaddlv a d n => s!"uaddlv {d.scalar a true}, {n.arr a.name}"
  | .shift op a d n sh => s!"{op.name} {d.arr a.name}, {n.arr a.name}, #{sh}"
  | .ext d n m imm => s!"ext {d.b}, {n.b}, {m.b}, #{imm}"
  | .rev .rev32b d n => s!"rev32 {d.b}, {n.b}"
  | .rev .rev32h d n => s!"rev32 {d.arr "8h"}, {n.arr "8h"}"
  | .rev .rev64b d n => s!"rev64 {d.b}, {n.b}"
  | .rev .rev64s d n => s!"rev64 {d.arr "4s"}, {n.arr "4s"}"
  | .perm op a d n m => s!"{op.name} {d.arr a.name}, {n.arr a.name}, {m.arr a.name}"
  | .tbl d n m => s!"tbl {d.b}, \{{n.b}}, {m.b}"
  | .tblN x len d n m => s!"{if x then "tbx" else "tbl"} {d.b}, {tableList n len}, {m.b}"
  | .umull false d n m => s!"umull {d.arr "2d"}, {n.arr "2s"}, {m.arr "2s"}"
  | .umull true d n m => s!"umull2 {d.arr "2d"}, {n.arr "4s"}, {m.arr "4s"}"
  | .umlal false d n m => s!"umlal {d.arr "2d"}, {n.arr "2s"}, {m.arr "2s"}"
  | .umlal true d n m => s!"umlal2 {d.arr "2d"}, {n.arr "4s"}, {m.arr "4s"}"
  | .umullH false d n m => s!"umull {d.arr "4s"}, {n.arr "4h"}, {m.arr "4h"}"
  | .umullH true d n m => s!"umull2 {d.arr "4s"}, {n.arr "8h"}, {m.arr "8h"}"
  | .umlalH false d n m => s!"umlal {d.arr "4s"}, {n.arr "4h"}, {m.arr "4h"}"
  | .umlalH true d n m => s!"umlal2 {d.arr "4s"}, {n.arr "8h"}, {m.arr "8h"}"
  | .mul d n m => s!"mul {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .mla d n m => s!"mla {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .mls d n m => s!"mls {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .sqdmulh d n m => s!"sqdmulh {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .umin d n m => s!"umin {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .mulH op d n m => s!"{op.name} {d.arr "8h"}, {n.arr "8h"}, {m.arr "8h"}"
  | .mulHE op d n m i => s!"{op.name} {d.arr "8h"}, {n.arr "8h"}, v{m.index}.h[{i}]"
  | .pmull false d n m => s!"pmull {d.arr "1q"}, {n.arr "1d"}, {m.arr "1d"}"
  | .pmull true d n m => s!"pmull2 {d.arr "1q"}, {n.arr "2d"}, {m.arr "2d"}"
  | .pmull8 false d n m => s!"pmull {d.arr "8h"}, {n.arr "8b"}, {m.arr "8b"}"
  | .pmull8 true d n m => s!"pmull2 {d.arr "8h"}, {n.arr "16b"}, {m.arr "16b"}"
  | .aese d n => s!"aese {d.b}, {n.b}"
  | .aesd d n => s!"aesd {d.b}, {n.b}"
  | .aesmc d n => s!"aesmc {d.b}, {n.b}"
  | .aesimc d n => s!"aesimc {d.b}, {n.b}"
  | .sha1 op d n m => s!"{op.name} {d.q}, {n.s}, {m.arr "4s"}"
  | .sha1h d n => s!"sha1h {d.s}, {n.s}"
  | .sha1su0 d n m => s!"sha1su0 {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .sha1su1 d n => s!"sha1su1 {d.arr "4s"}, {n.arr "4s"}"
  | .sha256h d n m => s!"sha256h {d.q}, {n.q}, {m.arr "4s"}"
  | .sha256h2 d n m => s!"sha256h2 {d.q}, {n.q}, {m.arr "4s"}"
  | .sha256su0 d n => s!"sha256su0 {d.arr "4s"}, {n.arr "4s"}"
  | .sha256su1 d n m => s!"sha256su1 {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .sha512h d n m => s!"sha512h {d.q}, {n.q}, {m.arr "2d"}"
  | .sha512h2 d n m => s!"sha512h2 {d.q}, {n.q}, {m.arr "2d"}"
  | .sha512su0 d n => s!"sha512su0 {d.arr "2d"}, {n.arr "2d"}"
  | .sha512su1 d n m => s!"sha512su1 {d.arr "2d"}, {n.arr "2d"}, {m.arr "2d"}"
  | .sm4e d n => s!"sm4e {d.arr "4s"}, {n.arr "4s"}"
  | .sm4ekey d n m => s!"sm4ekey {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .sm3ss1 d n m a => s!"sm3ss1 {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}, {a.arr "4s"}"
  | .sm3tt op d n m i =>
    let name := match op with
      | .tt1a => "sm3tt1a" | .tt1b => "sm3tt1b" | .tt2a => "sm3tt2a" | .tt2b => "sm3tt2b"
    s!"{name} {d.arr "4s"}, {n.arr "4s"}, v{m.index}.s[{i}]"
  | .sm3partw1 d n m => s!"sm3partw1 {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .sm3partw2 d n m => s!"sm3partw2 {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .eor3 d n m a => s!"eor3 {d.b}, {n.b}, {m.b}, {a.b}"
  | .bcax d n m a => s!"bcax {d.b}, {n.b}, {m.b}, {a.b}"
  | .rax1 d n m => s!"rax1 {d.arr "2d"}, {n.arr "2d"}, {m.arr "2d"}"
  | .xar d n m imm => s!"xar {d.arr "2d"}, {n.arr "2d"}, {m.arr "2d"}, #{imm}"
  | .xarS d m rot => s!"xar z{d.index}.s, z{d.index}.s, z{m.index}.s, #{rot}"

def LogicOp.name : LogicOp → String
  | .and => "and" | .orr => "orr" | .eor => "eor"

def Instr.asm : Instr → List String
  | .add sz d n m => [s!"add {d.name sz}, {n.name sz}, {m.name sz}"]
  | .sub sz d n m => [s!"sub {d.name sz}, {n.name sz}, {m.name sz}"]
  | .adds sz d n m => [s!"adds {d.name sz}, {n.name sz}, {m.name sz}"]
  | .adcs sz d n m => [s!"adcs {d.name sz}, {n.name sz}, {m.name sz}"]
  | .subs sz d n m => [s!"subs {d.name sz}, {n.name sz}, {m.name sz}"]
  | .sbcs sz d n m => [s!"sbcs {d.name sz}, {n.name sz}, {m.name sz}"]
  | .adc sz d n m => [s!"adc {d.name sz}, {n.name sz}, {m.name sz}"]
  | .sbc sz d n m => [s!"sbc {d.name sz}, {n.name sz}, {m.name sz}"]
  | .csel sz d n m => [s!"csel {d.name sz}, {n.name sz}, {m.name sz}, hs"]
  | .tst sz n m => [s!"tst {n.name sz}, {m.name sz}"]
  | .ccmp sz n imm nzcv cond => [s!"ccmp {n.name sz}, #{imm}, #{nzcv}, {cond.name}"]
  | .cselc sz d n m cond => [s!"csel {d.name sz}, {n.name sz}, {m.name sz}, {cond.name}"]
  | .csneg sz d n m cond => [s!"csneg {d.name sz}, {n.name sz}, {m.name sz}, {cond.name}"]
  | .adrSym d name => [s!"adrp {d.name .x}, {name}", s!"add {d.name .x}, {d.name .x}, :lo12:{name}"]
  | .addImm sz d n imm => [s!"add {d.name sz}, {n.name sz}, #{imm}"]
  | .subImm sz d n imm => [s!"sub {d.name sz}, {n.name sz}, #{imm}"]
  | .logic op sz d n m => [s!"{op.name} {d.name sz}, {n.name sz}, {m.name sz}"]
  | .logicRor op sz d n m sh =>
    [s!"{op.name} {d.name sz}, {n.name sz}, {m.name sz}, ror #{sh}"]
  | .bicRor sz d n m sh =>
    [s!"bic {d.name sz}, {n.name sz}, {m.name sz}, ror #{sh}"]
  | .ror sz d n sh => [s!"ror {d.name sz}, {n.name sz}, #{sh}"]
  | .extr sz d n m lsb => [s!"extr {d.name sz}, {n.name sz}, {m.name sz}, #{lsb}"]
  | .lsr sz d n sh => [s!"lsr {d.name sz}, {n.name sz}, #{sh}"]
  | .lsl sz d n sh => [s!"lsl {d.name sz}, {n.name sz}, #{sh}"]
  | .madd sz d n m a => [s!"madd {d.name sz}, {n.name sz}, {m.name sz}, {a.name sz}"]
  | .mul sz d n m => [s!"mul {d.name sz}, {n.name sz}, {m.name sz}"]
  | .umulh d n m => [s!"umulh {d.name .x}, {n.name .x}, {m.name .x}"]
  | .umaddl d n m a => [s!"umaddl {d.name .x}, {n.name .w}, {m.name .w}, {a.name .x}"]
  | .umull d n m => [s!"umull {d.name .x}, {n.name .w}, {m.name .w}"]
  | .clz sz d n => [s!"clz {d.name sz}, {n.name sz}"]
  | .rbit sz d n => [s!"rbit {d.name sz}, {n.name sz}"]
  | .rev32 d n => [s!"rev {d.name .w}, {n.name .w}"]
  | .rev d n => [s!"rev {d.name .x}, {n.name .x}"]
  | .movz sz d imm hw => [s!"movz {d.name sz}, #{imm.toNat}, lsl #{16 * hw}"]
  | .movk sz d imm hw => [s!"movk {d.name sz}, #{imm.toNat}, lsl #{16 * hw}"]
  | .ldr sz t n off => [s!"ldr {t.name sz}, [{n.name .x}, #{off}]"]
  | .str sz t n off => [s!"str {t.name sz}, [{n.name .x}, #{off}]"]
  | .ldrb t n off => [s!"ldrb {t.name .w}, [{n.name .x}, #{off}]"]
  | .strb t n off => [s!"strb {t.name .w}, [{n.name .x}, #{off}]"]
  | .ldp t1 t2 n off => [s!"ldp {t1.name .x}, {t2.name .x}, [{n.name .x}, #{off}]"]
  | .stp t1 t2 n off => [s!"stp {t1.name .x}, {t2.name .x}, [{n.name .x}, #{off}]"]
  | .blr n => [s!"blr {n.name .x}"]
  | .push r => [s!"str {r.name .x}, [sp, #-16]!"]
  | .pop r => [s!"ldr {r.name .x}, [sp], #16"]
  | .addSp d imm => [s!"add {d.name .x}, sp, #{imm}"]
  | .alloc bytes => [s!"sub sp, sp, #{bytes}"]
  | .free bytes => [s!"add sp, sp, #{bytes}"]
  | .ldrSp t off => [s!"ldr {t.name .x}, [sp, #{off}]"]
  | .strSp t off => [s!"str {t.name .x}, [sp, #{off}]"]
  | .vop op => [op.asm]
  | .ldrq t n off => [s!"ldr {t.q}, [{n.name .x}, #{off}]"]
  | .ldrqTbl t n off .. => [s!"ldr {t.q}, [{n.name .x}, #{off}]"]
  | .ldrTbl sz t n off .. => [s!"ldr {t.name sz}, [{n.name .x}, #{off}]"]
  | .strq t n off => [s!"str {t.q}, [{n.name .x}, #{off}]"]
  | .umov .w d n i => [s!"umov {d.name .w}, v{n.index}.s[{i}]"]
  | .umov .x d n i => [s!"umov {d.name .x}, v{n.index}.d[{i}]"]
  | .mrsDit t => [s!"mrs {t.name .x}, DIT"]
  | .msrDitImm on => [s!"msr DIT, #{on.toNat}"]
  | .barrier .dsbSy => ["dsb sy"]
  | .barrier .isb => ["isb"]
  | .barrier .sb => ["sb"]
  | .align k => [s!".p2align {k}"]

/-- The lines of an instruction: each of its instructions' text (`asm`) as a
comment, then that instruction's word (`encode`); its text if it has no
encoding (`align`, `adrSym`, printed by `symLines`, or an instruction that
`unencodable` reports, which the emitter refuses). -/
def Instr.code (i : Instr) : List String :=
  match i.encode with
  | some ws => (i.asm.zip ws).flatMap fun (t, w) => [s!"// {t}", instLine w]
  | none => i.asm

def printer : Printer isa where
  instr := Instr.code
  branch c l := match c with
    | .zero sz r => [s!"cbz {r.name sz}, {l}"]
    | .nonzero sz r => [s!"cbnz {r.name sz}, {l}"]
  jump l := s!"b {l}"
  ret := ["// ret", instLine retWord]
  call := "bl"
  -- The static's page and offset, in the syntax of the object format
  -- (`TCB/Rust.lean`); `asm` gives ELF's, for reading.
  symLines
    | .adrSym d name => some [.sym s!"adrp {d.name .x}, " .page name,
        .sym s!"add {d.name .x}, {d.name .x}, " .pageOff name]
    | _ => none
  tables
    | .ldrqTbl _ _ _ name ws => [(name, ws)]
    | .ldrTbl _ _ _ _ name ws => [(name, ws)]
    | _ => []
  /- Every function starts on a 64-byte boundary, a cache line, and so on
  the 32-byte boundaries the Arm Neoverse N1 Software Optimization Guide
  (§4.8, "Branch instruction alignment") recommends for subroutine entry
  points, for the fetch after the branch to them. So where a function's
  code, and its loops, lie relative to the fetch blocks and cache lines is
  fixed by the function alone: a change to other code cannot move them,
  and with them its performance. -/
  funcAlign := [".p2align 6"]
  unencodable
    | .align k =>
      if k ∈ [4, 5, 6] then none else some s!"`.p2align {k}`: only 4, 5 and 6 are allowed"
    | .adrSym .. => none
    | i => if i.encode.isNone then some "an operand does not fit its field" else none

/-- What the emitter needs of the target (`Emitter`): its printer, its Rust `cfg`
and ABI string, and how documentation names its calling convention's
argument area and reserved memory (`abi`'s `argArea` and `reserved`). -/
instance : Emitter isa where
  printer := printer
  -- `aarch64_be` targets are big-endian, and ILP32 ones (`aarch64-unknown-linux-gnu_ilp32`)
  -- have 32-bit pointers. The model's baseline includes AdvSIMD (NEON: see
  -- `Instr.requires`), which `aarch64-unknown-none-softfloat` turns off.
  rustCfg := "all(target_arch = \"aarch64\", target_endian = \"little\", \
    target_pointer_width = \"64\", target_feature = \"neon\")"
  rustAbi := "C"
  argAreaDoc ws := if ws.length - argRegs.length = 0 then none else
    some ("the arguments on the stack", false)
  reservedDoc n := if n = 0 then none else some s!"the {n} bytes of stack below the stack pointer"

end VG.AArch64
