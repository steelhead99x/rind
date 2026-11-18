module

public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.TCB.AArch64.Simd

/-!
# AArch64 machine model

**Trusted.** A model of the subset of AArch64 (A64) used by our
implementations. Each instruction's semantics here must agree with the Arm
Architecture Reference Manual for A-profile (DDI 0487), chapter C6 ("A64
Base Instruction Descriptions") and, for the AdvSIMD and cryptographic
instructions, chapter C7 ("A64 Advanced SIMD and Floating-point Instruction
Descriptions"); when adding an instruction, cite the section whose
pseudocode it transcribes.

Modelling choices:
* Registers are `x0`–`x17`, `x19`–`x28` and `x30`. `x18` is not modelled, so no
  code can use it: it is the platform register (AAPCS64 §6.1.1, "r18 …
  The Platform Register, if needed; otherwise a temporary register", and
  "software developers creating platform-independent code are advised to
  avoid using r18 if at all possible"). Apple's platforms reserve it ("The
  platform reserves register x18. Don't use this register.", *Writing ARM64
  code for Apple platforms*) and Windows points it at the thread's TEB
  (*Overview of ARM64 ABI conventions*), so it may change under a function
  that writes it, and restoring it before returning is not enough.
* `x29` is not modelled either: the portable target keeps the inherited
  frame pointer intact throughout execution. AAPCS64 section 6.4.6 delegates
  frame-chain requirements to the platform; Apple requires `x29` to always
  address a valid frame record, even when a leaf function omits its own
  record (*Writing ARM64 code for Apple platforms*, "Respect the purpose of
  specific CPU registers"). Saving and restoring an arbitrary temporary in
  `x29` would not satisfy that requirement.
  https://developer.apple.com/documentation/xcode/writing-arm64-code-for-apple-platforms
* The stack pointer is separate. Only frame delimiters (`push`/`pop` and
  `alloc`/`free`) write it. `addSp` computes a stack-relative pointer, and
  `ldrSp` loads a 64-bit word from `[sp, #off]` (including arguments passed
  on the stack), and `strSp` stores one there (into a frame). Register number 31, SP or the zero register, is otherwise
  never an operand.
  Each operand is a 32-bit (`w`) or a 64-bit (`x`) register; a 32-bit
  result is zero-extended into the 64-bit register (DDI 0487, the pseudocode
  accessor `X[n, width] = value` sets `_R[n] = ZeroExtend(value, 64)`).
* The condition flags PSTATE.N, Z, C and V: ADDS/ADCS/SUBS/SBCS, TST and
  CCMP write them; ADCS/SBCS/ADC/SBC and CSEL with the condition HS read C,
  and CCMP, CSEL and CSNEG with a condition code (`CondCode`) read all four.
  Control flow uses `cbz`/`cbnz`, never the flags. A call makes NZCV
  unknown, since it is undefined at a public interface (AAPCS64 §6.1.1).
* Immediates that the instruction cannot encode make the instruction fault,
  so verified code only ever contains encodable instructions.
* Memory accesses (32-bit, 64-bit, and single bytes via `ldrb`/`strb`) must
  lie within the state's permitted regions: loads within `rd ++ wr`, stores
  within `wr`; otherwise the instruction faults. Memory is little-endian.
* Instructions whose timing depends on their operands (e.g. `udiv`) must never
  be added: the constant-time leakage model assumes they do not exist. The
  multiplies (`madd`, `mul`, `umaddl`, `umull`) and the shifts (`lsl`, `lsr`: UBFM) are among the
  data-processing instructions that Arm specifies to take a time independent
  of their data when PSTATE.DIT is 1 (DDI 0487, "About PSTATE.DIT", FEAT_DIT,
  which lists MADD and UBFM, as it does the other modelled data-processing
  instructions that read a register: ADD, SUB, AND, BIC, EOR, ORR, EXTR, REV and
  MOVK, ADDS, ADCS, SUBS, SBCS, ADC, SBC, CSEL, CSNEG, CCMP, TST, UMULH, CLZ and
  RBIT; the
  description of UMADDL, of which UMULL is an alias, says "This instruction is a
  data-independent-time instruction as described in About PSTATE.DIT": DDI
  0602, A64 ISA XML 2025-12, `umaddl.xml`). Arm guarantees their timing only
  while PSTATE.DIT is 1, which verified code does not ensure itself (see
  PSTATE.DIT below), for these as for the others.
* PSTATE.DIT, `State.dit`: `mrsDit` (`mrs xt, DIT`) reads it and `msrDitImm`
  (`msr DIT, #imm`) writes it, both requiring FEAT_DIT; no other instruction
  reads or writes it, and the semantics and the leakage (the addresses
  accessed and the branch conditions) of every other instruction are the same
  whatever its value. When it is 0, "The architecture makes no statement about
  the timing properties of any instructions"; when it is 1, "The architecture
  requires that the execution time of a data-independent-time sequence of
  code must be independent of all data-independent-time values" (DDI 0601
  2026-03, "DIT, Data Independent Timing", which lists the
  data-independent-time instructions). So the leakage model's assumption that
  the other instructions' timing depends on nothing but what they leak is what
  Arm specifies for code run with PSTATE.DIT 1, and the model does not check
  that it is. `Target.abiPreserved` says nothing about it. The calling
  convention gives it as the mode (`Abi.mode`, `TCB/AArch64/Target.lean`),
  which a contract may make public.
* Barriers, `barrier` (DSB SY, ISB and SB): the model has no memory ordering,
  pipeline or speculation, which is all they act on, so each leaves the state
  as it is and leaks nothing (DDI 0602 2026-03: "DSB", whose operation for
  `CRm = '1111'` is `DataSynchronizationBarrier(scope, types, nXS)`; "ISB",
  `InstructionSynchronizationBarrier()`; "SB", `SpeculationBarrier()`). They
  have no operands: their time depends only on the instructions before them,
  whose leakage the model already accounts for. Code uses
  them after setting PSTATE.DIT, as Apple's documentation asks ("To ensure
  that subsequent instruction timing reflects the updated DIT processor
  state, add a speculation barrier after turning on DIT", Writing ARM64 code
  for Apple platforms, "Enable DIT for constant-time cryptographic
  operations"), with DSB SY and ISB in place of SB where FEAT_SB is missing,
  as Apple's corecrypto does (`cc/src/cc_timing_safe.c`).
* Calls are `bl`, or indirect through a register, `blr` (`icall`, the
  instruction of an indirect call, `Code.icall`), and returns `ret` (DDI
  0487, C6.2 "BL", "BLR", "RET"). The return addresses are the next of the
  state's `unknowns`, which nothing constrains (see `TCB/Code.lean`). A
  linker veneer between a `bl` and its target may change `x16` and `x17`
  (IP0, IP1: AAPCS64 §6.1.1, "Use of IP0 and IP1 by the linker"), so a call
  leaves unknown values in them too (and the model's indirect call, which
  takes no veneer, does as well: a superset of what it changes). The
  function of each name is at the address of its symbol, `State.syms name`,
  as a static is (`ISA.fnAddr`). No function the emitter writes begins with
  a `bti c` landing pad, so code calling them indirectly must not run with
  branch target enforcement (FEAT_BTI, guarded pages): the emitted objects
  carry no `GNU_PROPERTY_AARCH64_FEATURE_1_BTI` note, without which the
  linker and loader leave it off.
* A `static` the code reads (`Artifact.consts`) is at the address
  `State.syms name`, where `name` is its name, which `adrSym` (`adrp` and
  `add`, resolved by the linker) puts in a register. No instruction changes
  `syms`: a static's address is fixed for the run of the program.
* A table of constants an instruction carries (`ldrqTbl` and `ldrTbl`, its
  name and its words) is the `static` of that name the emitter writes from it
  (`TCB/Rust.lean`), as x86-64's `aluTbl` and `vmovdquTbl` are
  (`TCB/X86_64/Isa.lean`): for the whole run of the program it is mapped
  readable at `State.syms name` and holds exactly those words, 8 bytes each,
  little-endian, and does not wrap around the address space; and no memory
  any code writes overlaps it: no region a contract lets a function write,
  nor the stack. This is what a Rust `static` without interior mutability
  is: an immutable object, which the linker places in read-only memory,
  apart from every other object and from the stack, and which no `&mut`
  (safe Rust cannot make one to it) nor any other pointer the program may
  write through can reach. So the model reads the words from the
  instruction rather than from `State.mem`, whose writes never reach it,
  and no contract states any of this. Unlike x86-64's forms, whose operand
  the printer writes with the symbol, the printed `ldr` reads wherever its
  base register points, so the model faults unless that register holds
  `State.syms name`: an instruction that executes reads the static.
* The stack pointer is always 16-byte aligned (AAPCS64 §6.4.5.1, "SP mod 16
  = 0"), and a frame moves it by 16 bytes, so the model does not check the
  stack alignment that the push and pop of a frame require.
* The SIMD and floating-point registers are `v0`–`v31`, 128 bits each
  (DDI 0487 B1.2.1). The low 64 bits of `v8`–`v15` are callee-saved
  (AAPCS64 §6.1.2); `Target.abiPreserved` requires their preservation.
  Their upper 64 bits, like all bits of the other vectors, are caller-saved. A write of a
  scalar (`S`) register sets the other bits of its vector register to zero
  (the pseudocode accessor `V[n, width] = value` sets `_Z[n] =
  ZeroExtend(value, MAX_VL)`), and the modelled vector forms all write 128
  bits, so no upper bits beyond 128 (SVE's `Z` registers) are observable to
  the model; with SVE, those are also zeroed.
* The one SVE instruction, SVE2's XAR (`xarS`), is unpredicated and acts on
  each 32-bit element of the `CurrentVL()` bits of `Z[dn]` and `Z[m]`
  independently, whatever the vector length (DDI 0602, "SVE Instructions",
  "XAR"; the A64 ISA XML, `xar_z_zzi`):
  https://developer.arm.com/documentation/ddi0602/2025-09/SVE-Instructions/XAR--Bitwise-exclusive-OR-and-rotate-right-by-immediate-
  So the low 128 bits of its result, `V[dn]`, depend only on the low 128
  bits of its sources, `V[dn]` and `V[m]`. The model computes those 128
  bits and does not model the rest of `Z[dn]`. That is exact for everything
  the model observes: no modelled instruction reads a `Z` register beyond
  its low 128 bits, and those upper bits are caller-saved (AAPCS64 §6.1.3,
  "Scalable vector registers": unless a subroutine takes or returns
  scalable vectors or predicates, "only the low 64 bits of z8-z15 are
  Callee-saved"). The generated functions have AAPCS64's non-streaming
  PSTATE.SM interface (PSTATE.SM is 0 on entry and on return), so the
  instruction runs in non-streaming mode. The model has no SVE predicate
  registers, first fault register, loads or stores.
* No modelled AdvSIMD instruction is a floating-point one, and the one
  saturating instruction, SQDMULH, faults in the model where it would
  saturate (and set FPSR.QC), so verified code never saturates: no modelled
  instruction reads FPCR or writes FPSR, and neither is modelled. The loads and
  stores of a vector register (`LDR`/`STR (immediate, SIMD&FP)`) need no
  alignment: they access Normal memory, and alignment is checked only if
  `SCTLR_ELx.A` is 1 (DDI 0487 B2.5.2, "Alignment of data accesses"), which
  Linux, macOS and Windows leave 0 for user code.
* The AdvSIMD data-processing instructions modelled here (MOV = ORR, MOVI,
  DUP, INS, UMOV, AND, ORR, EOR, BIC, ORN, NOT, BSL, BIT, BIF, CMEQ, CMHI,
  CMHS, ADD, SUB, ADDV, UADDLV, SHL, USHR, SSHR, SRI, SLI, EXT, REV32, REV64,
  ZIP1, ZIP2, TRN1, TRN2, UZP1, UZP2, TBL, TBX, UMULL, UMLAL, PMULL, MUL, MLA, MLS, SQDMULH, UMIN), and the cryptographic ones
  (AESE, AESD, AESMC, AESIMC, SHA1C, SHA1P, SHA1M, SHA1H, SHA1SU0, SHA1SU1,
  SHA256H, SHA256H2, SHA256SU0, SHA256SU1, SHA512H, SHA512H2, SHA512SU0,
  SHA512SU1, EOR3, BCAX, RAX1, XAR, SM4E, SM4EKEY, SM3SS1, SM3TT1A, SM3TT1B,
  SM3TT2A, SM3TT2B, SM3PARTW1, SM3PARTW2), and SVE2's XAR, are all among those whose
  timing Arm specifies to be independent of their data when PSTATE.DIT is 1
  (DDI 0487, "About PSTATE.DIT"; the description of SVE2's XAR says "This
  instruction is a data-independent-time instruction as described in About
  PSTATE.DIT", and so do those of SM4E, SM4EKEY and the seven SM3
  instructions in the A64 ISA XML 2025-12, and that of PMULL and PMULL2, for
  every element size, in the A64 ISA XML 2026-03). CMHI, CMHS, ADDV and UADDLV are in the list of
  data-independent-time instructions of DDI 0487 M.b C5.2.4, "DIT, Data
  Independent Timing" (also DDI 0601 2026-09): "Advanced SIMD three same: ADD,
  ADDP, AND, …, CMEQ, CMGE, CMGT, CMHI, CMHS, …" and "Advanced SIMD across
  lanes: ADDV, SADDLV, SMAXV, SMINV, UADDLV, UMAXV, and UMINV.", and their
  descriptions in the A64 ISA XML 2026-09 say "This instruction is a
  data-independent-time instruction as described in About PSTATE.DIT". As
  above, Arm guarantees this while PSTATE.DIT is 1.
-/

@[expose] public section

namespace VG.AArch64

inductive Reg
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x19 | x20 | x21 | x22 | x23 | x24 | x25 | x26 | x27 | x28 | x30
  deriving DecidableEq, Repr, Inhabited

/-- The 32 SIMD and floating-point registers (DDI 0487 B1.2.1). -/
inductive VReg
  | v0 | v1 | v2 | v3 | v4 | v5 | v6 | v7
  | v8 | v9 | v10 | v11 | v12 | v13 | v14 | v15
  | v16 | v17 | v18 | v19 | v20 | v21 | v22 | v23 | v24 | v25 | v26 | v27 | v28 | v29 | v30 | v31
  deriving DecidableEq, Repr, Inhabited

/-- The next register, `(n + 1) MOD 32`: the table registers of a TBL or
TBX of more than one register follow `n` in this order (DDI 0487 C7.2,
"TBL": `n = (n + 1) MOD 32`). -/
def VReg.succ : VReg → VReg
  | .v0 => .v1 | .v1 => .v2 | .v2 => .v3 | .v3 => .v4 | .v4 => .v5 | .v5 => .v6
  | .v6 => .v7 | .v7 => .v8 | .v8 => .v9 | .v9 => .v10 | .v10 => .v11 | .v11 => .v12
  | .v12 => .v13 | .v13 => .v14 | .v14 => .v15 | .v15 => .v16 | .v16 => .v17
  | .v17 => .v18 | .v18 => .v19 | .v19 => .v20 | .v20 => .v21 | .v21 => .v22
  | .v22 => .v23 | .v23 => .v24 | .v24 => .v25 | .v25 => .v26 | .v26 => .v27
  | .v27 => .v28 | .v28 => .v29 | .v29 => .v30 | .v30 => .v31 | .v31 => .v0

/-- The number `n` of `v<n>`. -/
def VReg.index : VReg → Nat
  | .v0 => 0 | .v1 => 1 | .v2 => 2 | .v3 => 3 | .v4 => 4 | .v5 => 5 | .v6 => 6 | .v7 => 7
  | .v8 => 8 | .v9 => 9 | .v10 => 10 | .v11 => 11 | .v12 => 12 | .v13 => 13 | .v14 => 14
  | .v15 => 15
  | .v16 => 16 | .v17 => 17 | .v18 => 18 | .v19 => 19 | .v20 => 20 | .v21 => 21 | .v22 => 22
  | .v23 => 23 | .v24 => 24 | .v25 => 25 | .v26 => 26 | .v27 => 27 | .v28 => 28 | .v29 => 29
  | .v30 => 30 | .v31 => 31

/-- Operand size: 32-bit (`w` registers) or 64-bit (`x` registers). -/
inductive Size | w | x
  deriving DecidableEq, Repr

abbrev Size.bits : Size → Nat
  | .w => 32
  | .x => 64

structure State where
  gpr : Reg → BitVec 64
  sp : BitVec 64
  /-- PSTATE.C: unsigned carry, or no borrow after subtraction. -/
  c : Bool := false
  /-- PSTATE.N: the result's top bit. -/
  nf : Bool := false
  /-- PSTATE.Z: the result is zero. -/
  zf : Bool := false
  /-- PSTATE.V: signed overflow. -/
  vf : Bool := false
  /-- PSTATE.DIT, data independent timing (FEAT_DIT): only `mrsDit` reads it
  and only `msrDitImm` writes it. -/
  dit : Bool := false
  /-- The SIMD and floating-point registers (`V[n]`, 128 bits). -/
  v : VReg → BitVec 128 := fun _ => 0
  mem : Mem
  /-- Regions the code may read (in addition to `wr`). -/
  rd : List Region
  /-- Regions the code may read and write. -/
  wr : List Region
  /-- Values the model does not know, used in order: the return address each
  call stores, on the ARM targets what a linker veneer may leave in the
  intra-procedure-call scratch registers (see `TCB/Code.lean`), and what a
  released frame's bytes hold (`lose`). -/
  unknowns : Nat → BitVec 64 := fun _ => 0
  /-- The address of each `static` the code can name (`adrSym`), by name. -/
  syms : String → BitVec 64 := fun _ => 0

inductive LogicOp | and | orr | eor
  deriving DecidableEq, Repr

/-- The arrangement of a vector of 32-bit (`.4s`), 64-bit (`.2d`), 8-bit
(`.16b`) or 16-bit (`.8h`) lanes. -/
inductive VArr | s4 | d2 | b16 | h8
  deriving DecidableEq, Repr

/-- The size of a lane of an arrangement. -/
abbrev VArr.esize : VArr → Nat
  | .s4 => 32
  | .d2 => 64
  | .b16 => 8
  | .h8 => 16

/-- Bitwise operations on whole vectors (`.16b`). -/
inductive VLogicOp | and | orr | eor | bic | orn
  deriving DecidableEq, Repr

/-- Shifts of each lane by an immediate. -/
inductive VShiftOp | shl | ushr | sri | sli | sshr
  deriving DecidableEq, Repr

/-- Permutations of the lanes of two vectors. -/
inductive VPermOp | zip1 | zip2 | trn1 | trn2 | uzp1 | uzp2
  deriving DecidableEq, Repr

/-- Reversals of the elements within each container: `rev32 .16b` (bytes in
each word), `rev32 .8h` (halfwords in each word), `rev64 .16b` (bytes in each
doubleword), `rev64 .4s` (words in each doubleword). -/
inductive VRevOp | rev32b | rev32h | rev64b | rev64s
  deriving DecidableEq, Repr

/-- The products of 16-bit lanes (`.8h`): MUL, MLA, MLS, SQDMULH and SQRDMULH. -/
inductive VMulHOp | mul | mla | mls | sqdmulh | sqrdmulh
  deriving DecidableEq, Repr

/-- The unsigned comparisons of lanes CMHI (higher) and CMHS (higher or
same). -/
inductive VCmpOp | hi | hs
  deriving DecidableEq, Repr

/-- The bitwise selects BSL, BIT and BIF. -/
inductive VSelOp | bsl | bit | bif
  deriving DecidableEq, Repr

/-- The functions of SHA1C (`SHAchoose`), SHA1P (`SHAparity`) and SHA1M
(`SHAmajority`). -/
inductive Sha1Op | c | p | m
  deriving DecidableEq, Repr

/-- SM3TT1A, SM3TT1B, SM3TT2A and SM3TT2B. -/
inductive Sm3TtOp | tt1a | tt1b | tt2a | tt2b
  deriving DecidableEq, Repr

/-- AdvSIMD and cryptographic instructions that write only a vector
register (and access no memory). -/
inductive VOp
  /-- `mov vd.16b, vn.16b` (alias of ORR (vector, register) with both sources `n`) -/
  | mov (d n : VReg)
  /-- `movi vd.2d, #0` -/
  | movi0 (d : VReg)
  /-- `dup vd.4s, wn` / `dup vd.2d, xn` / `dup vd.16b, wn` / `dup vd.8h, wn` (DUP (general)) -/
  | dup (a : VArr) (d : VReg) (n : Reg)
  /-- `mov vd.s[i], wn` / `mov vd.d[i], xn` / `mov vd.b[i], wn` / `mov vd.h[i], wn` (alias of
  INS (general)) -/
  | ins (a : VArr) (d : VReg) (i : Nat) (n : Reg)
  /-- `dup sd, vn.s[i]` (DUP (element), scalar) -/
  | dupS (d n : VReg) (i : Nat)
  /-- `dup vd.<a>, vn.<t>[i]` (DUP (element), vector) -/
  | dupE (a : VArr) (d n : VReg) (i : Nat)
  /-- `mov vd.<t>[i], vn.<t>[j]` (alias of INS (element)) -/
  | insE (a : VArr) (d : VReg) (i : Nat) (n : VReg) (j : Nat)
  /-- `cmeq vd.<a>, vn.<a>, vm.<a>` (CMEQ (register)) -/
  | cmeq (a : VArr) (d n m : VReg)
  /-- `cmhi`/`cmhs vd.<a>, vn.<a>, vm.<a>` (CMHI (register), CMHS (register), DDI 0487
  C7.2.34, C7.2.35) -/
  | cmp (op : VCmpOp) (a : VArr) (d n m : VReg)
  /-- `bsl`/`bit`/`bif vd.16b, vn.16b, vm.16b` -/
  | bsel (op : VSelOp) (d n m : VReg)
  /-- `and`/`orr`/`eor`/`bic`/`orn vd.16b, vn.16b, vm.16b` -/
  | logic (op : VLogicOp) (d n m : VReg)
  /-- `not vd.16b, vn.16b` -/
  | not (d n : VReg)
  /-- `add vd.<a>, vn.<a>, vm.<a>` (ADD (vector)) -/
  | add (a : VArr) (d n m : VReg)
  /-- `sub vd.<a>, vn.<a>, vm.<a>` (SUB (vector)) -/
  | sub (a : VArr) (d n m : VReg)
  /-- `addv bd, vn.16b` / `addv hd, vn.8h` / `addv sd, vn.4s` (ADDV): the sum of
  the lanes, a scalar of the lane size (`.2d` faults: no such form) -/
  | addv (a : VArr) (d n : VReg)
  /-- `uaddlv hd, vn.16b` / `uaddlv sd, vn.8h` / `uaddlv dd, vn.4s` (UADDLV): the
  unsigned sum of the lanes, a scalar of twice the lane size (`.2d` faults: no
  such form) -/
  | uaddlv (a : VArr) (d n : VReg)
  /-- `shl`/`ushr`/`sri`/`sli vd.<a>, vn.<a>, #sh` -/
  | shift (op : VShiftOp) (a : VArr) (d n : VReg) (sh : Nat)
  /-- `ext vd.16b, vn.16b, vm.16b, #imm` -/
  | ext (d n m : VReg) (imm : Nat)
  /-- `rev32`/`rev64 vd.<T>, vn.<T>` -/
  | rev (op : VRevOp) (d n : VReg)
  /-- `zip1`/`zip2`/`trn1`/`trn2`/`uzp1`/`uzp2 vd.<a>, vn.<a>, vm.<a>` -/
  | perm (op : VPermOp) (a : VArr) (d n m : VReg)
  /-- `tbl vd.16b, {vn.16b}, vm.16b` (a table of one register) -/
  | tbl (d n m : VReg)
  /-- `tbl vd.16b, {vn.16b, …}, vm.16b` (`tbx` if `x`), a table of `len`
  registers: `vn` and the `len - 1` that follow it (`VReg.succ`) -/
  | tblN (x : Bool) (len : Nat) (d n m : VReg)
  /-- `umull vd.2d, vn.2s, vm.2s`, or `umull2 vd.2d, vn.4s, vm.4s` if `hi` -/
  | umull (hi : Bool) (d n m : VReg)
  /-- `umlal vd.2d, vn.2s, vm.2s`, or `umlal2 vd.2d, vn.4s, vm.4s` if `hi` -/
  | umlal (hi : Bool) (d n m : VReg)
  /-- `umull vd.4s, vn.4h, vm.4h`, or `umull2 vd.4s, vn.8h, vm.8h` if `hi` (UMULL (vector),
  `size = 01`) -/
  | umullH (hi : Bool) (d n m : VReg)
  /-- `umlal vd.4s, vn.4h, vm.4h`, or `umlal2 vd.4s, vn.8h, vm.8h` if `hi` (UMLAL (vector),
  `size = 01`) -/
  | umlalH (hi : Bool) (d n m : VReg)
  /-- `mul vd.4s, vn.4s, vm.4s` (MUL (vector)) -/
  | mul (d n m : VReg)
  /-- `mla vd.4s, vn.4s, vm.4s` (MLA (vector)) -/
  | mla (d n m : VReg)
  /-- `mls vd.4s, vn.4s, vm.4s` (MLS (vector)) -/
  | mls (d n m : VReg)
  /-- `sqdmulh vd.4s, vn.4s, vm.4s` (SQDMULH (vector)) -/
  | sqdmulh (d n m : VReg)
  /-- `umin vd.4s, vn.4s, vm.4s` -/
  | umin (d n m : VReg)
  /-- `mul`/`mla`/`mls`/`sqdmulh`/`sqrdmulh vd.8h, vn.8h, vm.8h` (MUL, MLA, MLS,
  SQDMULH and SQRDMULH (vector), 16-bit lanes) -/
  | mulH (op : VMulHOp) (d n m : VReg)
  /-- `mul`/`mla`/`mls`/`sqdmulh`/`sqrdmulh vd.8h, vn.8h, vm.h[i]` (MUL, MLA, MLS,
  SQDMULH and SQRDMULH (by element), 16-bit lanes): the second operand of every
  lane is lane `i` of `vm`, which must be one of `v0`–`v15` -/
  | mulHE (op : VMulHOp) (d n m : VReg) (i : Nat)
  /-- `pmull vd.1q, vn.1d, vm.1d`, or `pmull2 vd.1q, vn.2d, vm.2d` if `hi` -/
  | pmull (hi : Bool) (d n m : VReg)
  /-- `pmull vd.8h, vn.8b, vm.8b`, or `pmull2 vd.8h, vn.16b, vm.16b` if `hi`
  (PMULL, PMULL2 with 8-bit source elements, `size = 00`) -/
  | pmull8 (hi : Bool) (d n m : VReg)
  /-- `aese vd.16b, vn.16b` -/
  | aese (d n : VReg)
  /-- `aesd vd.16b, vn.16b` -/
  | aesd (d n : VReg)
  /-- `aesmc vd.16b, vn.16b` -/
  | aesmc (d n : VReg)
  /-- `aesimc vd.16b, vn.16b` -/
  | aesimc (d n : VReg)
  /-- `sha1c`/`sha1p`/`sha1m qd, sn, vm.4s` -/
  | sha1 (op : Sha1Op) (d n m : VReg)
  /-- `sha1h sd, sn` -/
  | sha1h (d n : VReg)
  /-- `sha1su0 vd.4s, vn.4s, vm.4s` -/
  | sha1su0 (d n m : VReg)
  /-- `sha1su1 vd.4s, vn.4s` -/
  | sha1su1 (d n : VReg)
  /-- `sha256h qd, qn, vm.4s` -/
  | sha256h (d n m : VReg)
  /-- `sha256h2 qd, qn, vm.4s` -/
  | sha256h2 (d n m : VReg)
  /-- `sha256su0 vd.4s, vn.4s` -/
  | sha256su0 (d n : VReg)
  /-- `sha256su1 vd.4s, vn.4s, vm.4s` -/
  | sha256su1 (d n m : VReg)
  /-- `sha512h qd, qn, vm.2d` -/
  | sha512h (d n m : VReg)
  /-- `sha512h2 qd, qn, vm.2d` -/
  | sha512h2 (d n m : VReg)
  /-- `sha512su0 vd.2d, vn.2d` -/
  | sha512su0 (d n : VReg)
  /-- `sha512su1 vd.2d, vn.2d, vm.2d` -/
  | sha512su1 (d n m : VReg)
  /-- `sm4e vd.4s, vn.4s` -/
  | sm4e (d n : VReg)
  /-- `sm4ekey vd.4s, vn.4s, vm.4s` -/
  | sm4ekey (d n m : VReg)
  /-- `sm3ss1 vd.4s, vn.4s, vm.4s, va.4s` -/
  | sm3ss1 (d n m a : VReg)
  /-- `sm3tt1a`/`sm3tt1b`/`sm3tt2a`/`sm3tt2b vd.4s, vn.4s, vm.s[i]` -/
  | sm3tt (op : Sm3TtOp) (d n m : VReg) (i : Nat)
  /-- `sm3partw1 vd.4s, vn.4s, vm.4s` -/
  | sm3partw1 (d n m : VReg)
  /-- `sm3partw2 vd.4s, vn.4s, vm.4s` -/
  | sm3partw2 (d n m : VReg)
  /-- `eor3 vd.16b, vn.16b, vm.16b, va.16b` -/
  | eor3 (d n m a : VReg)
  /-- `bcax vd.16b, vn.16b, vm.16b, va.16b` -/
  | bcax (d n m a : VReg)
  /-- `rax1 vd.2d, vn.2d, vm.2d` -/
  | rax1 (d n m : VReg)
  /-- `xar vd.2d, vn.2d, vm.2d, #imm` -/
  | xar (d n m : VReg) (imm : Nat)
  /-- `xar zd.s, zd.s, zm.s, #rot` (SVE2 XAR, 32-bit elements; the low 128
  bits of `Z[d]`, see the modelling choices above) -/
  | xarS (d m : VReg) (rot : Nat)
  deriving DecidableEq, Repr

/-- The condition codes of conditional instructions (DDI 0487 C1.2.4, Table
C1-1; `al` and `nv` are not modelled). -/
inductive CondCode | eq | ne | hs | lo | mi | pl | vs | vc | hi | ls | ge | lt | gt | le
  deriving DecidableEq, Repr

/-- DDI 0487 J1.3 shared pseudocode `ConditionHolds(cond)`: `cond<3:1>`
selects the test (EQ: Z; HS: C; MI: N; VS: V; HI: C and not Z; GE: N = V; GT:
N = V and not Z), and `cond<0>` (and not `'1111'`) inverts it. -/
def CondCode.holds (s : State) : CondCode → Bool
  | .eq => s.zf
  | .ne => !s.zf
  | .hs => s.c
  | .lo => !s.c
  | .mi => s.nf
  | .pl => !s.nf
  | .vs => s.vf
  | .vc => !s.vf
  | .hi => s.c && !s.zf
  | .ls => !(s.c && !s.zf)
  | .ge => s.nf == s.vf
  | .lt => s.nf != s.vf
  | .gt => s.nf == s.vf && !s.zf
  | .le => !(s.nf == s.vf && !s.zf)

/-- The barriers (DDI 0602, "DSB", "ISB", "SB"). -/
inductive Barrier
  /-- `dsb sy`: DSB with `CRm = '1111'`, the full system, all accesses. -/
  | dsbSy
  /-- `isb` (ISB SY, `CRm = '1111'`). -/
  | isb
  /-- `sb`, FEAT_SB. -/
  | sb
  deriving DecidableEq, Repr

inductive Instr
  /-- `add d, n, m` (ADD (shifted register), no shift) -/
  | add (sz : Size) (d n m : Reg)
  /-- `sub d, n, m` (SUB (shifted register), no shift) -/
  | sub (sz : Size) (d n m : Reg)
  /-- ADDS (shifted register), no shift; writes the carry flag. -/
  | adds (sz : Size) (d n m : Reg)
  /-- ADCS: add both operands and PSTATE.C, writing the carry flag. -/
  | adcs (sz : Size) (d n m : Reg)
  /-- SUBS (shifted register), no shift; C is the no-borrow flag. -/
  | subs (sz : Size) (d n m : Reg)
  /-- SBCS: subtract the second operand and NOT(PSTATE.C). -/
  | sbcs (sz : Size) (d n m : Reg)
  /-- ADC: add both operands and PSTATE.C; the flags are not set. -/
  | adc (sz : Size) (d n m : Reg)
  /-- SBC: subtract the second operand and NOT(PSTATE.C); the flags are not
  set. -/
  | sbc (sz : Size) (d n m : Reg)
  /-- `csel d, n, m, hs` (CSEL with the condition HS, "carry set"): `n` if
  PSTATE.C is set, else `m`; the flags are not set. (`lo` is `hs` with the
  sources swapped.) -/
  | csel (sz : Size) (d n m : Reg)
  /-- `tst n, m` (TST (shifted register), no shift: ANDS with the zero
  register as destination): N and Z of `n AND m`, C and V cleared. -/
  | tst (sz : Size) (n m : Reg)
  /-- `ccmp n, #imm, #nzcv, cond` (CCMP (immediate), `imm < 32`, `nzcv < 16`):
  the flags of `n - imm` if `cond` holds, else `nzcv`. -/
  | ccmp (sz : Size) (n : Reg) (imm nzcv : Nat) (cond : CondCode)
  /-- `csel d, n, m, cond` (CSEL): `n` if `cond` holds, else `m`; the flags
  are not set. -/
  | cselc (sz : Size) (d n m : Reg) (cond : CondCode)
  /-- `csneg d, n, m, cond` (CSNEG): `n` if `cond` holds, else `-m`; the flags
  are not set. -/
  | csneg (sz : Size) (d n m : Reg) (cond : CondCode)
  /-- `adrp d, name` then `add d, d, :lo12:name` (ADRP, ADD (immediate), no
  shift): the address of the `static` `name`, `State.syms name`. -/
  | adrSym (d : Reg) (name : String)
  /-- `add d, n, #imm` (ADD (immediate), `imm < 4096`, no shift) -/
  | addImm (sz : Size) (d n : Reg) (imm : Nat)
  /-- `sub d, n, #imm` (SUB (immediate), `imm < 4096`, no shift) -/
  | subImm (sz : Size) (d n : Reg) (imm : Nat)
  /-- `and`/`orr`/`eor d, n, m` (shifted register, no shift) -/
  | logic (op : LogicOp) (sz : Size) (d n m : Reg)
  /-- `and`/`orr`/`eor d, n, m, ror #sh`, `sh < size` (shifted register). -/
  | logicRor (op : LogicOp) (sz : Size) (d n m : Reg) (sh : Nat)
  /-- `bic d, n, m, ror #sh`, `sh < size` (shifted register). -/
  | bicRor (sz : Size) (d n m : Reg) (sh : Nat)
  /-- `ror d, n, #sh` (alias of EXTR d, n, n, #sh), `sh < size` -/
  | ror (sz : Size) (d n : Reg) (sh : Nat)
  /-- `extr d, n, m, #lsb` (EXTR), `lsb < size`: bits `lsb + size - 1 : lsb`
  of the concatenation `n:m` -/
  | extr (sz : Size) (d n m : Reg) (lsb : Nat)
  /-- `lsr d, n, #sh` (alias of UBFM), `sh < size` -/
  | lsr (sz : Size) (d n : Reg) (sh : Nat)
  /-- `lsl d, n, #sh` (LSL (immediate), alias of UBFM), `sh < size` -/
  | lsl (sz : Size) (d n : Reg) (sh : Nat)
  /-- `madd d, n, m, a` (MADD): `a + n * m`, modulo `2 ^ size` -/
  | madd (sz : Size) (d n m a : Reg)
  /-- `mul d, n, m` (MUL, the alias of MADD with the zero register as the
  addend): `n * m`, modulo `2 ^ size` -/
  | mul (sz : Size) (d n m : Reg)
  /-- UMULH: bits 127:64 of the unsigned 64-by-64-bit product. -/
  | umulh (d n m : Reg)
  /-- `blr xn` (BLR): the indirect call of the function at the address in
  `n` (see `icall`). It only occurs as the instruction of an indirect call
  (`Code.icall`): as a straight-line instruction it faults. -/
  | blr (n : Reg)
  /-- `umaddl xd, wn, wm, xa` (UMADDL): `a + n<31:0> * m<31:0>`, the
  product of the low 32 bits of `n` and `m`, zero-extended, modulo `2 ^ 64` -/
  | umaddl (d n m a : Reg)
  /-- `umull xd, wn, wm` (UMULL, the alias of UMADDL with the zero register as
  the addend): `n<31:0> * m<31:0>`, zero-extended -/
  | umull (d n m : Reg)
  /-- `clz d, n` (CLZ): the number of zero bits of `n` above its highest one
  bit, `size` if `n` is zero -/
  | clz (sz : Size) (d n : Reg)
  /-- `rbit d, n` (RBIT): the bits of `n` in reverse order -/
  | rbit (sz : Size) (d n : Reg)
  /-- `rev wd, wn` (REV, 32-bit): reverse the bytes of the low 32 bits -/
  | rev32 (d n : Reg)
  /-- `rev xd, xn` (REV, 64-bit): reverse the bytes of all 64 bits -/
  | rev (d n : Reg)
  /-- `movz d, #imm, lsl #(16 * hw)` -/
  | movz (sz : Size) (d : Reg) (imm : BitVec 16) (hw : Nat)
  /-- `movk d, #imm, lsl #(16 * hw)` -/
  | movk (sz : Size) (d : Reg) (imm : BitVec 16) (hw : Nat)
  /-- `ldr t, [n, #off]` (LDR (immediate), unsigned offset: a multiple of the
  access size, less than 4096 times it) -/
  | ldr (sz : Size) (t n : Reg) (off : Nat)
  /-- `str t, [n, #off]` (STR (immediate), unsigned offset, as for `ldr`) -/
  | str (sz : Size) (t n : Reg) (off : Nat)
  /-- `ldrb wt, [n, #off]` (LDRB (immediate), unsigned offset, `off < 4096`):
  the byte, zero-extended into the 64-bit register -/
  | ldrb (t n : Reg) (off : Nat)
  /-- `strb wt, [n, #off]` (STRB (immediate), unsigned offset, `off < 4096`):
  the low byte of `t` -/
  | strb (t n : Reg) (off : Nat)
  /-- `ldp xt1, xt2, [n, #off]` (LDP, 64-bit, signed offset, with a
  non-negative offset: a multiple of 8, at most 504): the 64-bit words at
  `n + off` and `n + off + 8` into `t1` and `t2`, which must differ -/
  | ldp (t1 t2 n : Reg) (off : Nat)
  /-- `stp xt1, xt2, [n, #off]` (STP, 64-bit, signed offset, as for `ldp`):
  `t1` at `n + off` and `t2` at `n + off + 8` -/
  | stp (t1 t2 n : Reg) (off : Nat)
  /-- `str xr, [sp, #-16]!` (STR (immediate), 64-bit, pre-index): the push
  of a frame of 16 bytes (see `push`) -/
  | push (r : Reg)
  /-- `ldr xr, [sp], #16` (LDR (immediate), 64-bit, post-index): the pop of a
  frame of 16 bytes (see `pop`) -/
  | pop (r : Reg)
  /-- `ldr xt, [sp, #off]` (LDR (immediate), 64-bit, unsigned offset, base
  register SP: a multiple of 8, less than 32768) -/
  | ldrSp (t : Reg) (off : Nat)
  /-- `str xt, [sp, #off]` (STR (immediate), 64-bit, unsigned offset, base
  register SP: a multiple of 8, less than 32768) -/
  | strSp (t : Reg) (off : Nat)
  /-- `add xd, sp, #imm`, 64-bit ADD (immediate), without shifting. -/
  | addSp (d : Reg) (imm : Nat)
  /-- `sub sp, sp, #bytes`, opening an aligned frame (only `push`). -/
  | alloc (bytes : Nat)
  /-- `add sp, sp, #bytes`, closing that frame (only `pop`). -/
  | free (bytes : Nat)
  /-- An AdvSIMD or cryptographic instruction that writes only a vector register. -/
  | vop (op : VOp)
  /-- `ldr qt, [n, #off]` (LDR (immediate, SIMD&FP), 128-bit, unsigned offset:
  a multiple of 16, less than 65536) -/
  | ldrq (t : VReg) (n : Reg) (off : Nat)
  /-- `str qt, [n, #off]` (STR (immediate, SIMD&FP), 128-bit, unsigned offset,
  as for `ldrq`) -/
  | strq (t : VReg) (n : Reg) (off : Nat)
  /-- `ldr qt, [n, #off]` (as `ldrq`), whose base register holds the address
  of the `static` `name`, whose words are `words`: the emitter writes that
  static from this instruction (`TCB/Rust.lean`), as for x86-64's
  `vmovdquTbl`. -/
  | ldrqTbl (t : VReg) (n : Reg) (off : Nat) (name : String) (words : List (BitVec 64))
  /-- `ldr xt, [n, #off]` / `ldr wt, [n, #off]` (as `ldr`: LDR (immediate),
  unsigned offset), whose base register holds the address of the `static`
  `name`, whose words are `words`: the emitter writes that static from this
  instruction (`TCB/Rust.lean`), as for `ldrqTbl`. -/
  | ldrTbl (sz : Size) (t n : Reg) (off : Nat) (name : String) (words : List (BitVec 64))
  /-- `umov wd, vn.s[i]` / `umov xd, vn.d[i]` (UMOV) -/
  | umov (sz : Size) (d : Reg) (n : VReg) (i : Nat)
  /-- `mrs xt, DIT` (MRS of the system register DIT): PSTATE.DIT, in bit 24
  of `t`, the other bits zero (see `exec`). -/
  | mrsDit (t : Reg)
  /-- `msr DIT, #imm` (MSR (immediate), the PSTATE field DIT, with `imm` 0 or
  1): PSTATE.DIT becomes `on` (see `exec`). -/
  | msrDitImm (on : Bool)
  /-- A barrier (DSB SY, ISB or SB): no effect on the model's state (see
  `exec`). -/
  | barrier (b : Barrier)
  /-- Padding to the next multiple of `2 ^ k` bytes with NOPs (NOP, `HINT
  #0`), printed as `.p2align k` for `k` 4, 5 or 6 only: it has no effect,
  accesses no memory and requires no feature (DDI 0487 C6.2, "NOP"; see
  `Print.lean`). -/
  | align (k : Nat)
  deriving DecidableEq, Repr

/-- Branch conditions. -/
inductive Cond
  /-- `cbz r, …`: the register (of the given size) is zero -/
  | zero (sz : Size) (r : Reg)
  /-- `cbnz r, …`: the register (of the given size) is not zero -/
  | nonzero (sz : Size) (r : Reg)
  deriving DecidableEq, Repr

namespace State

/-- Read a register at the operand size (`W[n]` or `X[n]`). -/
def read (s : State) (sz : Size) (r : Reg) : BitVec sz.bits := (s.gpr r).setWidth sz.bits

/-- Write a register at the operand size, zero-extending a 32-bit value. -/
def write (s : State) (sz : Size) (r : Reg) (v : BitVec sz.bits) : State :=
  { s with gpr := fun r' => if r' = r then v.setWidth 64 else s.gpr r' }

/-- DDI 0487 J1.1 shared pseudocode `AddWithCarry(x, y, carry_in)`: the
result is the low `size` bits of `UInt(x) + UInt(y) + UInt(carry_in)`; N is
its top bit, Z that it is zero, C that the unsigned sum does not fit (`UInt(result)
!= unsigned_sum`) and V that the signed sum does not (`SInt(result) !=
SInt(x) + SInt(y) + UInt(carry_in)`). -/
def flagsAdd (s : State) {w : Nat} (a b : BitVec w) (carry : Bool) : State :=
  { s with
    nf := (a + b + BitVec.ofNat w carry.toNat).msb
    zf := decide (a + b + BitVec.ofNat w carry.toNat = 0)
    c := decide (2 ^ w ≤ a.toNat + b.toNat + carry.toNat)
    vf := decide ((a + b + BitVec.ofNat w carry.toNat).toInt ≠ a.toInt + b.toInt + carry.toNat) }

/-- DDI 0487 C6.2, ADDS/ADCS/SUBS/SBCS: `(result, nzcv) = AddWithCarry(...)`,
`X[d] = result`, `PSTATE.<N,Z,C,V> = nzcv` (`flagsAdd`). SUBS uses `(a,
NOT(b), 1)` and SBCS uses `(a, NOT(b), PSTATE.C)`. All four are baseline A64
instructions. https://developer.arm.com/documentation/ddi0487/latest -/
def addWithCarry (s : State) (sz : Size) (d : Reg)
    (a b : BitVec sz.bits) (carry : Bool) : State :=
  { s.write sz d (a + b + BitVec.ofNat sz.bits carry.toNat) with
    c := decide (2 ^ sz.bits ≤ a.toNat + b.toNat + carry.toNat)
    nf := (a + b + BitVec.ofNat sz.bits carry.toNat).msb
    zf := decide (a + b + BitVec.ofNat sz.bits carry.toNat = 0)
    vf := decide ((a + b + BitVec.ofNat sz.bits carry.toNat).toInt ≠ a.toInt + b.toInt + carry.toNat) }

/-- Write a vector register (`V[n] = value`, 128 bits). -/
def setV (s : State) (r : VReg) (x : BitVec 128) : State :=
  { s with v := fun r' => if r' = r then x else s.v r' }

/-- Load `n` bytes, faulting if not permitted. -/
def load (s : State) (a : Addr) (n : Nat) : Option (BitVec (8 * n)) :=
  if InRegions (s.rd ++ s.wr) a n then some (s.mem.read a n) else none

/-- Store `n` bytes, faulting if not permitted. -/
def store (s : State) (a : Addr) (n : Nat) (v : BitVec (8 * n)) : Option State :=
  if InRegions s.wr a n then some { s with mem := s.mem.write a n v } else none

end State

abbrev Size.bytes : Size → Nat
  | .w => 4
  | .x => 8

/-- The address of `[n, #off]` for an access of `bytes` bytes, if `off` is
encodable (DDI 0487 C6.2, "LDR (immediate)"/"STR (immediate)" and "LDRB
(immediate)"/"STRB (immediate)", unsigned offset: `offset = LSL(imm12,
scale)`, where `bytes = 2 ^ scale`, and `scale = 0` for the byte forms). -/
def addr (s : State) (bytes : Nat) (n : Reg) (off : Nat) : Option Addr :=
  if off % bytes = 0 ∧ off < 4096 * bytes then some (s.gpr n + BitVec.ofNat 64 off)
  else none

/-- `REV` (32-bit): `result<7:0> = X<31:24>` etc. (DDI 0487 C6.2, "REV"). -/
def rev32 (a : BitVec 32) : BitVec 32 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8

/-- `REV` (64-bit): `Reverse(X[n, 64], 8)`, i.e. `result<7:0> = X<63:56>`,
`result<15:8> = X<55:48>`, …, `result<63:56> = X<7:0>` (DDI 0487 C6.2,
"REV"). -/
def rev64 (a : BitVec 64) : BitVec 64 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8 ++
    a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.extractLsb' 56 8

/-! ### AdvSIMD and cryptographic instructions

The semantics of `VOp`, transcribing DDI 0487 C7.2 (lanes as in
`TCB/AArch64/Simd.lean`: lane `e` of size `esize` is bits
`(e+1)*esize-1 : e*esize`). -/

/-- `x` with lane `i` of size `w` (bits `(i+1)*w-1 : i*w`) replaced by `v`. -/
def setLane (x : BitVec 128) (w i : Nat) (v : BitVec w) : BitVec 128 :=
  (x &&& ~~~((BitVec.allOnes w).setWidth 128 <<< (w * i))) ||| (v.setWidth 128 <<< (w * i))

/-- The vector whose lane `e` of the arrangement `a` is `f esize (lane e of x)
(lane e of y)`, for a function `f` on lanes of any size. -/
def VArr.map2 (a : VArr) (f : (w : Nat) → BitVec w → BitVec w → BitVec w)
    (x y : BitVec 128) : BitVec 128 :=
  match a with
  | .s4 => ofVWords (f 32 (vword x 0) (vword y 0)) (f 32 (vword x 1) (vword y 1))
      (f 32 (vword x 2) (vword y 2)) (f 32 (vword x 3) (vword y 3))
  | .d2 => ofVDwords (f 64 (vdword x 0) (vdword y 0)) (f 64 (vdword x 1) (vdword y 1))
  | .b16 => ofVBytes fun e => f 8 (vbyte x e) (vbyte y e)
  | .h8 => ofVHalves fun e => f 16 (vhalf x e) (vhalf y e)

/-- The lanes of `x` in the arrangement `a`, lowest first. -/
def VArr.lanes (a : VArr) (x : BitVec 128) : List (BitVec 128) :=
  match a with
  | .s4 => [(vword x 0).setWidth 128, (vword x 1).setWidth 128, (vword x 2).setWidth 128,
      (vword x 3).setWidth 128]
  | .d2 => [(vdword x 0).setWidth 128, (vdword x 1).setWidth 128]
  | .b16 => (List.range 16).map fun e => (vbyte x e).setWidth 128
  | .h8 => (List.range 8).map fun e => (vhalf x e).setWidth 128

/-- The vector of the arrangement `a` whose lanes are `ls`, lowest first. -/
def VArr.ofLanes (a : VArr) (ls : List (BitVec 128)) : BitVec 128 :=
  let l (e : Nat) : BitVec 128 := ls.getD e 0
  match a with
  | .s4 => ofVWords ((l 0).setWidth 32) ((l 1).setWidth 32) ((l 2).setWidth 32) ((l 3).setWidth 32)
  | .d2 => ofVDwords ((l 0).setWidth 64) ((l 1).setWidth 64)
  | .b16 => ofVBytes fun e => (l e).setWidth 8
  | .h8 => ofVHalves fun e => (l e).setWidth 16

/-- The test of CMHI (`element1 > element2`) and CMHS (`element1 >=
element2`) on lanes `x` of `V[n]` and `y` of `V[m]`, as unsigned integers. -/
def VCmpOp.test {w : Nat} (op : VCmpOp) (x y : BitVec w) : Bool :=
  match op with
  | .hi => decide (x.toNat > y.toNat)
  | .hs => decide (x.toNat ≥ y.toNat)

/-- The sum of the lanes of `x` in the arrangement `a`, each as an unsigned
integer. -/
def VArr.laneSum (a : VArr) (x : BitVec 128) : Nat :=
  ((a.lanes x).map BitVec.toNat).sum

/-- DDI 0487 C7.2, "ZIP1", "ZIP2", "TRN1", "TRN2", "UZP1", "UZP2", with
`operand1 = V[n]` (lanes `n`) and `operand2 = V[m]` (lanes `m`), and `pairs`
the number of lane pairs (`elements / 2`):
* ZIP1/ZIP2: `base = part * pairs; for p = 0 to pairs-1: Elem[result, 2*p+0]
  = Elem[operand1, base+p]; Elem[result, 2*p+1] = Elem[operand2, base+p]`
  (`part` 0 or 1);
* TRN1/TRN2: `for p = 0 to pairs-1: Elem[result, 2*p+0] = Elem[operand1,
  2*p+part]; Elem[result, 2*p+1] = Elem[operand2, 2*p+part]`;
* UZP1/UZP2: `zipped = operand2:operand1; for e = 0 to elements-1:
  Elem[result, e] = Elem[zipped, 2*e+part]`. -/
def VPermOp.eval (op : VPermOp) (a : VArr) (x y : BitVec 128) : BitVec 128 :=
  let n := a.lanes x
  let m := a.lanes y
  let pairs := n.length / 2
  let g (l : List (BitVec 128)) (i : Nat) : BitVec 128 := l.getD i 0
  a.ofLanes <| match op with
  | .zip1 => (List.range pairs).flatMap fun p => [g n p, g m p]
  | .zip2 => (List.range pairs).flatMap fun p => [g n (pairs + p), g m (pairs + p)]
  | .trn1 => (List.range pairs).flatMap fun p => [g n (2 * p), g m (2 * p)]
  | .trn2 => (List.range pairs).flatMap fun p => [g n (2 * p + 1), g m (2 * p + 1)]
  | .uzp1 => (List.range n.length).map fun e => g (n ++ m) (2 * e)
  | .uzp2 => (List.range n.length).map fun e => g (n ++ m) (2 * e + 1)

/-- The vector whose word `e` is `f` of word `e` of `x`, `y` and `z`. -/
def mapWords3 (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) (x y z : BitVec 128) :
    BitVec 128 :=
  ofVWords (f (vword x 0) (vword y 0) (vword z 0)) (f (vword x 1) (vword y 1) (vword z 1))
    (f (vword x 2) (vword y 2) (vword z 2)) (f (vword x 3) (vword y 3) (vword z 3))

/-- One lane of SQDMULH (`.4s`), DDI 0487 C7.2, "SQDMULH (vector)":
`element1 = SInt(Elem[operand1, e]); element2 = SInt(Elem[operand2, e]);
product = 2 * element1 * element2; product = RShr(product, esize, FALSE)`
(`product >> 32`, rounding towards minus infinity); `(Elem[result, e], sat)
= SignedSatQ(product, esize)`, which saturates, and sets FPSR.QC, exactly
when both elements are `-2 ^ 31`. `none` there: the model faults rather
than saturate. -/
def sqdmulhLane (a b : BitVec 32) : Option (BitVec 32) :=
  if a = 0x80000000#32 ∧ b = 0x80000000#32 then none
  else some (BitVec.ofInt 32 ((2 * a.toInt * b.toInt) >>> 32))

/-- One lane of SQDMULH (`rnd` false) or SQRDMULH (`rnd` true) on 16-bit
lanes, DDI 0487 C7.2, "SQDMULH (vector)" and "SQRDMULH (vector)":
`round_const = if rounding then 1 << (esize - 1) else 0; element1 =
SInt(Elem[operand1, e]); element2 = SInt(Elem[operand2, e]); product = (2 *
element1 * element2) + round_const; (Elem[result, e], sat) =
SignedSatQ(product >> esize, esize)` (`>>` rounding towards minus infinity),
which saturates, and sets FPSR.QC, exactly when both elements are `-2 ^ 15`.
`none` there: the model faults rather than saturate. -/
def sqdmulhHLane (rnd : Bool) (a b : BitVec 16) : Option (BitVec 16) :=
  if a = 0x8000#16 ∧ b = 0x8000#16 then none
  else some (BitVec.ofInt 16 ((2 * a.toInt * b.toInt + if rnd then 2 ^ 15 else 0) >>> 16))

/-- One lane of the products of 16-bit lanes, DDI 0487 C7.2, with `operand1 =
V[n]`, `operand2 = V[m]` and, for MLA and MLS, `operand3 = V[d]` (lane `a`):
* MUL (vector): `Elem[result, e] = (element1 * element2)<esize-1:0>`;
* MLA (vector): `Elem[result, e] = Elem[operand3, e] + product`, `product =
  (UInt(element1) * UInt(element2))<esize-1:0>`;
* MLS (vector): `Elem[result, e] = Elem[operand3, e] - product`;
* SQDMULH, SQRDMULH (vector): `sqdmulhHLane`.
The (by element) forms (DDI 0487 C7.2, "MUL (by element)", "MLA (by
element)", "MLS (by element)", "SQDMULH (by element)", "SQRDMULH (by
element)") compute the same lanes with `element2 = Elem[operand2, index,
esize]` in every lane: for 16-bit elements `index = UInt(H:L:M)` (0 to 7) and
`Rm` has four bits (`m = UInt('0':Rm)`), so `Vm` is one of V0–V15. -/
def VMulHOp.lane : VMulHOp → BitVec 16 → BitVec 16 → BitVec 16 → Option (BitVec 16)
  | .mul, _, x, y => some (x * y)
  | .mla, a, x, y => some (a + x * y)
  | .mls, a, x, y => some (a - x * y)
  | .sqdmulh, _, x, y => sqdmulhHLane false x y
  | .sqrdmulh, _, x, y => sqdmulhHLane true x y

/-- DDI 0487 C7.2, "REV32" and "REV64" (`Reverse` of the elements within
each container): byte `i` of the result is byte `rev i` of the operand. -/
def VRevOp.eval (op : VRevOp) (x : BitVec 128) : BitVec 128 :=
  ofVBytes fun i => vbyte x <| match op with
    | .rev32b => 4 * (i / 4) + (3 - i % 4)
    | .rev32h => 4 * (i / 4) + (i % 4 + 2) % 4
    | .rev64b => 8 * (i / 8) + (7 - i % 8)
    | .rev64s => 8 * (i / 8) + (i % 8 + 4) % 8

/-- Whether the shift `sh` is encodable for `op` on lanes of `esize` bits:
`0 ≤ sh < esize` for SHL and SLI, `1 ≤ sh ≤ esize` for USHR, SSHR and SRI. -/
def VShiftOp.ok (op : VShiftOp) (esize sh : Nat) : Bool :=
  match op with
  | .shl | .sli => sh < esize
  | .ushr | .sri | .sshr => 1 ≤ sh && sh ≤ esize

/-- DDI 0487 C7.2, the shifts by an immediate of one lane `a` of the
destination and `b` of the source (`operand = V[n]`, `operand2 = V[d]`):
* SHL: `Elem[result, e] = LSL(Elem[operand, e], shift)`;
* USHR: `Elem[result, e] = LSR(Elem[operand, e], shift)` (the unsigned,
  unrounded form of `ShiftRight`);
* SSHR: `Elem[result, e] = ASR(Elem[operand, e], shift)` (the signed,
  unrounded form of `ShiftRight`: `(SInt(element) >> shift)<esize-1:0>`,
  so a shift by `esize` leaves copies of the sign bit);
* SRI: `mask = LSR(Ones(esize), shift); shifted = LSR(Elem[operand, e],
  shift); Elem[result, e] = (Elem[operand2, e] AND NOT(mask)) OR shifted`;
* SLI: `mask = LSL(Ones(esize), shift); shifted = LSL(Elem[operand, e],
  shift); Elem[result, e] = (Elem[operand2, e] AND NOT(mask)) OR shifted`. -/
def VShiftOp.eval (op : VShiftOp) (sh w : Nat) (a b : BitVec w) : BitVec w :=
  match op with
  | .shl => b <<< sh
  | .ushr => b >>> sh
  | .sshr => b.sshiftRight sh
  | .sri => (a &&& ~~~(BitVec.allOnes w >>> sh)) ||| (b >>> sh)
  | .sli => (a &&& ~~~(BitVec.allOnes w <<< sh)) ||| (b <<< sh)

/-- DDI 0487 C7.2, "BSL", "BIT" and "BIF": `V[d] = operand1 EOR ((operand1
EOR operand4) AND operand3)`, with `operand4 = V[n]` and
* BSL: `operand1 = V[m]`, `operand3 = V[d]` (`V[d]` selects `V[n]` where
  it is 1 and `V[m]` where it is 0);
* BIT: `operand1 = V[d]`, `operand3 = V[m]` (`V[n]` inserted where `V[m]` is 1);
* BIF: `operand1 = V[d]`, `operand3 = NOT(V[m])` (`V[n]` inserted where
  `V[m]` is 0). -/
def VSelOp.eval (op : VSelOp) (d n m : BitVec 128) : BitVec 128 :=
  let (op1, op3) := match op with
    | .bsl => (m, d)
    | .bit => (d, m)
    | .bif => (d, ~~~m)
  op1 ^^^ ((op1 ^^^ n) &&& op3)

/-- Byte `idx` of the table of `len` registers from `n` (DDI 0487 C7.2,
"TBL": `table<i*128+127:i*128> = V[n]; n = (n + 1) MOD 32` for `i` from 0
to `len - 1`), for `idx < 16 * len`. -/
def tableByte (v : VReg → BitVec 128) (n : VReg) (idx : Nat) : BitVec 8 :=
  vbyte (v (Nat.repeat VReg.succ (idx / 16) n)) (idx % 16)

/-- The function of SHA1C, SHA1P or SHA1M. -/
def Sha1Op.f : Sha1Op → BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32
  | .c => shaChoose
  | .p => shaParity
  | .m => shaMajority

/-- The new value of the destination, given the state. DDI 0487 C7.2:
* "MOV (vector)" = "ORR (vector, register)" with both sources `n`: `V[n]`;
  "MOVI" (64-bit variant, `imm = 0`): zeros;
* "DUP (general)": `element = X[n, esize]`, in every lane; "INS (general)":
  `element = X[n, esize]; result = V[d]; Elem[result, index, esize] =
  element`; "DUP (element)", scalar: `element = Elem[V[n], index, esize];
  V[d] = element` (the other bits of `V[d]` zero); "DUP (element)", vector:
  `element = Elem[V[n], index, esize]`, in every lane; "INS (element)":
  `element = Elem[V[n], src_index, esize]; result = V[d]; Elem[result,
  dst_index, esize] = element`;
* "CMEQ (register)": `test_passed = (element1 == element2); Elem[result,
  e, esize] = if test_passed then Ones(esize) else Zeros(esize)`;
* "CMHI (register)" (DDI 0487 M.b C7.2.34) and "CMHS (register)" (C7.2.35),
  as in the A64 ISA XML 2026-09: `element1 = UInt(operand1[e*:esize]);
  element2 = UInt(operand2[e*:esize]); result[e*:esize] = if element1 >
  element2 then Ones{esize} else Zeros{esize}` (`>=` for CMHS), with
  `operand1 = V{}(n)`, `operand2 = V{}(m)`, `V{datasize}(d) = result`;
* "BSL", "BIT", "BIF": `VSelOp.eval`;
* "AND", "ORR", "EOR", "BIC" (`operand1 AND NOT(operand2)`), "ORN"
  (`operand1 OR NOT(operand2)`) and "NOT" (vector, `.16b`);
* "ADD (vector)", "SUB (vector)": lane-wise, modulo `2 ^ esize`;
* "ADDV" (C7.2.6): `V{esize}(d) = IntReduce{esize, datasize}(ReduceOp_ADD,
  operand)`, the sum of the lanes modulo `2 ^ esize` (`IntReduce` adds the
  halves recursively, in `bits(esize)`); "UADDLV" (C7.2.408): `sum = UInt` of
  each lane, added as integers, then `V{2*esize}(d) = sum[2*esize-1:0]`. Each
  writes a scalar register, so the other bits of `V[d]` are zero (`V[n, width]
  = value` zero-extends). `size == '11'` is `Decode_UNDEF`, so `.2d` faults;
* the shifts (`VShiftOp.eval`), the permutations (`VPermOp.eval`) and the
  reversals (`VRevOp.eval`);
* "EXT": `concat = operand2:operand1; result = concat<position+127:position>`
  with `operand1 = V[n]`, `operand2 = V[m]`, `position = imm * 8`;
* "TBL" (one register): `index = UInt(Elem[indices, i, 8]); if index < 16
  then Elem[result, i, 8] = Elem[table, index, 8] else 0`, with `table =
  V[n]`, `indices = V[m]`;
* "TBL" and "TBX", `regs = len` from 1 to 4 (`len = UInt(len) + 1`): `table`
  the `len` registers from `n` (`tableByte`); `result = if is_tbl then
  Zeros() else V[d]`; `index = UInt(Elem[indices, i, 8]); if index < 16 *
  regs then Elem[result, i, 8] = Elem[table, index, 8]`;
* "UMULL", "UMULL2", "UMLAL", "UMLAL2": `part` 0, or 1 for the `2` forms,
  selects the lower or upper half of the sources: `element1 =
  Elem[operand1, e, 32]; element2 = Elem[operand2, e, 32]; product =
  element1 * element2` (unsigned, 64 bits), then `Elem[result, e, 64] =
  product` (UMULL) or `Elem[operand3, e, 64] + product` (UMLAL, `operand3 =
  V[d]`);
  with `size = 01` (`esize = 16`, `umullH`, `umlalH`), `part` 1 selects the
  upper 64 bits (`Vpart[n, part]`): `element1 = Elem[operand1, e, 16];
  element2 = Elem[operand2, e, 16]; product = element1 * element2` (unsigned,
  32 bits) for each of the 4 elements, then `Elem[result, e, 32] = product`
  (UMULL) or `Elem[operand3, e, 32] + product` (UMLAL, modulo `2 ^ 32`);
* "MUL (vector)", "MLA (vector)", "MLS (vector)" (`.4s`): `product =
  (UInt(element1) * UInt(element2))<esize-1:0>`, and `Elem[result, e] =
  product`, `Elem[operand3, e] + product` or `Elem[operand3, e] - product`
  (`operand3 = V[d]`), modulo `2 ^ 32`;
* "SQDMULH (vector)" (`.4s`): `sqdmulhLane` in each lane, faulting if any
  would saturate;
* "UMIN" (`.4s`): `Elem[result, e] = Min(UInt(element1), UInt(element2))`;
* "PMULL", "PMULL2" (`.1q`): `Elem[result, 0, 128] =
  PolynomialMult(Elem[operand1, part, 64], Elem[operand2, part, 64])`;
* "PMULL", "PMULL2" (`.8h`, `size = 00`: `esize = 8 << UInt(size)`,
  `datasize = 64`, `part = UInt(Q)`, `elements = 8`): `operand1 = Vpart[n,
  part, 64]; operand2 = Vpart[m, part, 64]; for e = 0 to 7: Elem[result, e,
  16] = PolynomialMult(Elem[operand1, e, 8], Elem[operand2, e, 8])`
  (`polyMul8`), `V[d, 128] = result`: byte `e` of the lower (`pmull`) or
  upper (`pmull2`) half of each source;
* "AESE": `AESSubBytes(AESShiftRows(operand1 EOR operand2))`; "AESD":
  `AESInvSubBytes(AESInvShiftRows(operand1 EOR operand2))`, with `operand1
  = V[d]`, `operand2 = V[n]`; "AESMC": `AESMixColumns(V[n])`; "AESIMC":
  `AESInvMixColumns(V[n])`;
* "SHA1C", "SHA1P", "SHA1M": `sha1Hash`; "SHA1H": `V[d] = ROL(V[n]<31:0>,
  30)` (the other bits zero); "SHA1SU0", "SHA1SU1": `sha1Su0`, `sha1Su1`;
* "SHA256H": `SHA256hash(V[d], V[n], V[m], TRUE)`; "SHA256H2":
  `SHA256hash(V[n], V[d], V[m], FALSE)`; "SHA256SU0", "SHA256SU1":
  `sha256Su0`, `sha256Su1`;
* "SHA512H", "SHA512H2", "SHA512SU0", "SHA512SU1": `sha512H`, `sha512H2`,
  `sha512Su0`, `sha512Su1`;
* "SM4E", "SM4EKEY" (A64 ISA XML 2025-12): `sm4E`, `sm4EKey`, four rounds of
  SM4's encryption of `V[d]` under the round keys `V[n]`, and of its key
  expansion from `V[n]` with the constants `V[m]`;
* "SM3SS1", "SM3TT1A", "SM3TT1B", "SM3TT2A", "SM3TT2B", "SM3PARTW1",
  "SM3PARTW2" (A64 ISA XML 2025-12): `sm3Ss1`, `sm3Tt1`, `sm3Tt2`,
  `sm3PartW1`, `sm3PartW2`, with `WjPrime`/`Wj = Vm[i*:32]` the word `i =
  UInt(imm2)` of `V[m]`;
* "EOR3": `Vn EOR Vm EOR Va`; "BCAX": `Vn EOR (Vm AND NOT(Va))`; "RAX1":
  `Elem[Vd, e, 64] = Elem[Vn, e, 64] EOR ROL(Elem[Vm, e, 64], 1)`; "XAR":
  `Elem[Vd, e, 64] = ROR(Elem[Vn, e, 64] EOR Elem[Vm, e, 64], imm6)`;
* SVE2's "XAR" (DDI 0602, "SVE Instructions"; 32-bit elements, `tszh:tszl =
  01:xx`): `rot = 2 *
  esize - UInt(tsize:imm3)`, from 1 to `esize`; `element1 = operand1[e*:esize];
  element2 = operand2[e*:esize]; result[e*:esize] = ROR(element1 XOR element2,
  rot)`, with `operand1 = Z[dn]`, `operand2 = Z[m]`, `Z[dn] = result`, on the
  four elements of the low 128 bits.

Immediates that are not encodable (an out-of-range shift, lane index or
EXT position) make the instruction fault. -/
def VOp.eval (s : State) : VOp → Option (VReg × BitVec 128)
  | .mov d n => some (d, s.v n)
  | .movi0 d => some (d, 0)
  | .dup .s4 d n => let w := (s.gpr n).setWidth 32; some (d, ofVWords w w w w)
  | .dup .d2 d n => some (d, ofVDwords (s.gpr n) (s.gpr n))
  | .ins .s4 d i n => if i < 4 then some (d, setLane (s.v d) 32 i ((s.gpr n).setWidth 32)) else none
  | .ins .d2 d i n => if i < 2 then some (d, setLane (s.v d) 64 i (s.gpr n)) else none
  | .dup .b16 d n => let b := (s.gpr n).setWidth 8; some (d, ofVBytes fun _ => b)
  | .ins .b16 d i n => if i < 16 then some (d, setLane (s.v d) 8 i ((s.gpr n).setWidth 8)) else none
  | .dup .h8 d n => let h := (s.gpr n).setWidth 16; some (d, ofVHalves fun _ => h)
  | .ins .h8 d i n => if i < 8 then some (d, setLane (s.v d) 16 i ((s.gpr n).setWidth 16)) else none
  | .dupS d n i => if i < 4 then some (d, (vword (s.v n) i).setWidth 128) else none
  | .dupE a d n i =>
    if i < 128 / a.esize then
      some (d, a.map2 (fun w _ _ => (s.v n).extractLsb' (w * i) w) 0 0)
    else none
  | .insE a d i n j =>
    if i < 128 / a.esize ∧ j < 128 / a.esize then
      some (d, setLane (s.v d) a.esize i ((s.v n).extractLsb' (a.esize * j) a.esize))
    else none
  | .cmeq a d n m =>
    some (d, a.map2 (fun w x y => if x = y then BitVec.allOnes w else 0) (s.v n) (s.v m))
  | .cmp op a d n m =>
    some (d, a.map2 (fun w x y =>
      if op.test x y then BitVec.allOnes w else 0) (s.v n) (s.v m))
  | .bsel op d n m => some (d, op.eval (s.v d) (s.v n) (s.v m))
  | .logic op d n m =>
    let a := s.v n
    let b := s.v m
    some (d, match op with
      | .and => a &&& b | .orr => a ||| b | .eor => a ^^^ b | .bic => a &&& ~~~b
      | .orn => a ||| ~~~b)
  | .not d n => some (d, ~~~(s.v n))
  | .add a d n m => some (d, a.map2 (fun _ x y => x + y) (s.v n) (s.v m))
  | .sub a d n m => some (d, a.map2 (fun _ x y => x - y) (s.v n) (s.v m))
  | .addv a d n =>
    if a ≠ .d2 then some (d, BitVec.ofNat 128 (a.laneSum (s.v n) % 2 ^ a.esize)) else none
  | .uaddlv a d n =>
    if a ≠ .d2 then some (d, BitVec.ofNat 128 (a.laneSum (s.v n) % 2 ^ (2 * a.esize))) else none
  | .shift op a d n sh =>
    if op.ok a.esize sh then some (d, a.map2 (fun w x y => op.eval sh w x y) (s.v d) (s.v n))
    else none
  | .ext d n m imm =>
    if imm < 16 then some (d, ((s.v m ++ s.v n) >>> (imm * 8)).extractLsb' 0 128) else none
  | .rev op d n => some (d, op.eval (s.v n))
  | .perm op a d n m => some (d, op.eval a (s.v n) (s.v m))
  | .tbl d n m => some (d, ofVBytes fun i =>
      let idx := (vbyte (s.v m) i).toNat
      if idx < 16 then vbyte (s.v n) idx else 0)
  | .tblN x len d n m =>
    if 1 ≤ len ∧ len ≤ 4 then some (d, ofVBytes fun i =>
      let idx := (vbyte (s.v m) i).toNat
      if idx < 16 * len then tableByte s.v n idx else if x then vbyte (s.v d) i else 0)
    else none
  | .umull hi d n m =>
    let p := if hi then 2 else 0
    let prod (e : Nat) : BitVec 64 :=
      (vword (s.v n) (p + e)).setWidth 64 * (vword (s.v m) (p + e)).setWidth 64
    some (d, ofVDwords (prod 0) (prod 1))
  | .umlal hi d n m =>
    let p := if hi then 2 else 0
    let prod (e : Nat) : BitVec 64 :=
      (vword (s.v n) (p + e)).setWidth 64 * (vword (s.v m) (p + e)).setWidth 64
    some (d, ofVDwords (vdword (s.v d) 0 + prod 0) (vdword (s.v d) 1 + prod 1))
  | .umullH hi d n m =>
    let p := if hi then 4 else 0
    let prod (e : Nat) : BitVec 32 :=
      (vhalf (s.v n) (p + e)).setWidth 32 * (vhalf (s.v m) (p + e)).setWidth 32
    some (d, ofVWords (prod 0) (prod 1) (prod 2) (prod 3))
  | .umlalH hi d n m =>
    let p := if hi then 4 else 0
    let prod (e : Nat) : BitVec 32 :=
      (vhalf (s.v n) (p + e)).setWidth 32 * (vhalf (s.v m) (p + e)).setWidth 32
    some (d, ofVWords (vword (s.v d) 0 + prod 0) (vword (s.v d) 1 + prod 1)
      (vword (s.v d) 2 + prod 2) (vword (s.v d) 3 + prod 3))
  | .mul d n m => some (d, VArr.s4.map2 (fun _ x y => x * y) (s.v n) (s.v m))
  | .mla d n m => some (d, mapWords3 (fun a x y => a + x * y) (s.v d) (s.v n) (s.v m))
  | .mls d n m => some (d, mapWords3 (fun a x y => a - x * y) (s.v d) (s.v n) (s.v m))
  | .sqdmulh d n m =>
    let r (e : Nat) := sqdmulhLane (vword (s.v n) e) (vword (s.v m) e)
    match r 0, r 1, r 2, r 3 with
    | some w0, some w1, some w2, some w3 => some (d, ofVWords w0 w1 w2 w3)
    | _, _, _, _ => none
  | .umin d n m =>
    some (d, VArr.s4.map2 (fun _ x y => if x.toNat ≤ y.toNat then x else y) (s.v n) (s.v m))
  | .mulH op d n m =>
    let r (e : Nat) := op.lane (vhalf (s.v d) e) (vhalf (s.v n) e) (vhalf (s.v m) e)
    if (List.range 8).all fun e => (r e).isSome then some (d, ofVHalves fun e => (r e).getD 0)
    else none
  | .mulHE op d n m i =>
    let r (e : Nat) := op.lane (vhalf (s.v d) e) (vhalf (s.v n) e) (vhalf (s.v m) i)
    if i < 8 ∧ m.index < 16 ∧ (List.range 8).all fun e => (r e).isSome then
      some (d, ofVHalves fun e => (r e).getD 0)
    else none
  | .pmull hi d n m =>
    let p := if hi then 1 else 0
    some (d, polyMul (vdword (s.v n) p) (vdword (s.v m) p))
  | .pmull8 hi d n m =>
    let p := if hi then 8 else 0
    some (d, ofVHalves fun e => polyMul8 (vbyte (s.v n) (p + e)) (vbyte (s.v m) (p + e)))
  | .aese d n => some (d, aesMapBytes aesSbox (aesShiftRows (s.v d ^^^ s.v n)))
  | .aesd d n => some (d, aesMapBytes aesInvSbox (aesInvShiftRows (s.v d ^^^ s.v n)))
  | .aesmc d n => some (d, aesMixColumns (s.v n))
  | .aesimc d n => some (d, aesInvMixColumns (s.v n))
  | .sha1 op d n m => some (d, sha1Hash op.f (s.v d) (vword (s.v n) 0) (s.v m))
  | .sha1h d n => some (d, ((vword (s.v n) 0).rotateLeft 30).setWidth 128)
  | .sha1su0 d n m => some (d, sha1Su0 (s.v d) (s.v n) (s.v m))
  | .sha1su1 d n => some (d, sha1Su1 (s.v d) (s.v n))
  | .sha256h d n m => some (d, sha256Hash (s.v d) (s.v n) (s.v m) true)
  | .sha256h2 d n m => some (d, sha256Hash (s.v n) (s.v d) (s.v m) false)
  | .sha256su0 d n => some (d, sha256Su0 (s.v d) (s.v n))
  | .sha256su1 d n m => some (d, sha256Su1 (s.v d) (s.v n) (s.v m))
  | .sha512h d n m => some (d, sha512H (s.v d) (s.v n) (s.v m))
  | .sha512h2 d n m => some (d, sha512H2 (s.v d) (s.v n) (s.v m))
  | .sha512su0 d n => some (d, sha512Su0 (s.v d) (s.v n))
  | .sha512su1 d n m => some (d, sha512Su1 (s.v d) (s.v n) (s.v m))
  | .sm4e d n => some (d, sm4E (s.v d) (s.v n))
  | .sm4ekey d n m => some (d, sm4EKey (s.v n) (s.v m))
  | .sm3ss1 d n m a => some (d, sm3Ss1 (s.v n) (s.v m) (s.v a))
  | .sm3tt op d n m i =>
    if i < 4 then
      some (d, match op with
        | .tt1a => sm3Tt1 false (s.v d) (s.v n) (vword (s.v m) i)
        | .tt1b => sm3Tt1 true (s.v d) (s.v n) (vword (s.v m) i)
        | .tt2a => sm3Tt2 false (s.v d) (s.v n) (vword (s.v m) i)
        | .tt2b => sm3Tt2 true (s.v d) (s.v n) (vword (s.v m) i))
    else none
  | .sm3partw1 d n m => some (d, sm3PartW1 (s.v d) (s.v n) (s.v m))
  | .sm3partw2 d n m => some (d, sm3PartW2 (s.v d) (s.v n) (s.v m))
  | .eor3 d n m a => some (d, s.v n ^^^ s.v m ^^^ s.v a)
  | .bcax d n m a => some (d, s.v n ^^^ (s.v m &&& ~~~(s.v a)))
  | .rax1 d n m => some (d, VArr.d2.map2 (fun _ x y => x ^^^ y.rotateLeft 1) (s.v n) (s.v m))
  | .xar d n m imm =>
    if imm < 64 then some (d, VArr.d2.map2 (fun _ x y => (x ^^^ y).rotateRight imm) (s.v n) (s.v m))
    else none
  | .xarS d m rot =>
    if 1 ≤ rot ∧ rot ≤ 32 then
      some (d, VArr.s4.map2 (fun _ x y => (x ^^^ y).rotateRight rot) (s.v d) (s.v m))
    else none

/-- Semantics, transcribing DDI 0487 C6.2:
* "ADD (shifted register)", "ADD (immediate)", "SUB (immediate)": the
  result of `AddWithCarry` (the flags are not set by these forms);
* "SUB (shifted register)": `AddWithCarry(operand1, NOT(operand2), '1')`,
  i.e. `n - m` modulo `2 ^ size` (the flags are not set by this form);
* "ADC": `(result, -) = AddWithCarry(operand1, operand2, PSTATE.C)`, and
  "SBC" the same with `operand2 = NOT(operand2)`: the result of
  `addWithCarry` (the low `size` bits of the sum), but the flags are not set
  (`setflags` is false for these forms); baseline A64. See Arm DDI 0487 C6.2
  and DDI 0596:
  https://developer.arm.com/documentation/ddi0596/2020-12/Base-Instructions/ADC--Add-with-Carry-
  https://developer.arm.com/documentation/ddi0596/2020-12/Base-Instructions/SBC--Subtract-with-Carry-;
* "CSEL": `if ConditionHolds(cond) then result = X[n, datasize] else
  result = X[m, datasize]; X[d, datasize] = result`, where for HS
  (`cond = '0010'`) `ConditionHolds` is `PSTATE.C == '1'` (DDI 0487 C6.2 and
  J1.3, `ConditionHolds`); the flags are not set. See
  https://developer.arm.com/documentation/ddi0596/2020-12/Base-Instructions/CSEL--Conditional-Select-;
  with another condition code (`cselc`), the same with `CondCode.holds`;
* "CSNEG": `if ConditionHolds(cond) then result = X[n] else result =
  NOT(X[m]) + 1` (that is, `-X[m]`), the flags not set. See
  https://developer.arm.com/documentation/ddi0596/2020-12/Base-Instructions/CSNEG--Conditional-Select-Negation-;
* "TST (shifted register)", the alias of "ANDS (shifted register)" with
  `Rd = '11111'` (the result is not written), no shift: `result = operand1
  AND operand2; PSTATE.<N,Z,C,V> = result<datasize-1>:IsZeroBit(result):'00'`. See
  https://developer.arm.com/documentation/ddi0596/2020-12/Base-Instructions/TST--shifted-register---Test--shifted-register---an-alias-of-ANDS--shifted-register--;
* "CCMP (immediate)": `if ConditionHolds(cond) then operand2 = NOT(imm5);
  (-, flags) = AddWithCarry(operand1, operand2, '1')` (the flags of
  `operand1 - imm5`), `else flags = nzcv`; `PSTATE.<N,Z,C,V> = flags`, with
  `imm5 < 32` and `nzcv` four bits (`nzcv<3>` is N). See
  https://developer.arm.com/documentation/ddi0596/2020-12/Base-Instructions/CCMP--immediate---Conditional-Compare--immediate--;
  All four are baseline A64 instructions.
* "ADRP" then "ADD (immediate)" into the same register (`adrSym`): ADRP's
  `base = PC[]; base<11:0> = Zeros(12); X[d, 64] = base + imm`, with `imm`
  the page offset the linker writes for the static's address `S`
  (`Page(S) - Page(P)`, `Page(x) = x` with bits 11:0 cleared: ELF for the
  Arm 64-bit Architecture, `R_AARCH64_ADR_PREL_PG_HI21`; Mach-O's
  `ARM64_RELOC_PAGE21`), so `X[d] = Page(S)`; then ADD's `X[d, 64] = X[d] +
  imm12`, with `imm12 = S<11:0>` (`R_AARCH64_ADD_ABS_LO12_NC`;
  `ARM64_RELOC_PAGEOFF12`): `X[d] = S`, the flags not set. A static beyond
  ADRP's range (±4 GB) does not link. See Arm DDI 0487 C6.2 and
  https://developer.arm.com/documentation/ddi0602/2025-09/Base-Instructions/ADRP--Form-PC-relative-address-to-4KB-page-
  https://github.com/ARM-software/abi-aa/blob/main/aaelf64/aaelf64.rst;
* "AND/ORR/EOR (shifted register)" and "BIC (shifted register)": the
  ROR forms use `operand2 = ShiftReg(m, SRType_ROR, shift_amount, datasize)`;
  BIC complements this rotated operand before AND. `imm6<5> = 1` is
  undefined for the 32-bit form, hence `sh < datasize`. These baseline
  instructions do not set flags. See Arm DDI 0487 C6.2 and DDI 0596:
  https://developer.arm.com/documentation/ddi0596/2020-12/Base-Instructions/EOR--shifted-register---Bitwise-Exclusive-OR--shifted-register--
  https://developer.arm.com/documentation/ddi0596/2020-12/Base-Instructions/BIC--shifted-register---Bitwise-Bit-Clear--shifted-register--;
* "ROR (immediate)" = "EXTR" with both sources `n`: `(n:n)<sh+size-1:sh>`,
  a rotation right by `sh`;
* "EXTR": `result = concat<lsb+datasize-1:lsb>` for `concat = X[n]:X[m]`,
  with `lsb = UInt(imms)`; `imms<5> = 1` is reserved for the 32-bit form,
  hence `lsb < datasize`. The flags are not set. See Arm DDI 0487 C6.2 and
  https://developer.arm.com/documentation/ddi0596/2020-12/Base-Instructions/EXTR--Extract-register-;
* "LSR (immediate)" = "UBFM": a logical shift right by `sh`;
* "LSL (immediate)" = "UBFM" with `immr = -sh MOD size`, `imms = size - 1 -
  sh`: a logical shift left by `sh` (the bits shifted out are lost, zeros
  shifted in);
* "MADD": `result = UInt(operand3) + (UInt(operand1) * UInt(operand2));
  X[d, destsize] = result<destsize-1:0>`, with `operand1 = X[n]`, `operand2
  = X[m]`, `operand3 = X[a]` at the operand size; "MUL" = "MADD" with `a` the
  zero register, so `operand3 = 0` (the flags are not set by either);
* "REV" (32- and 64-bit); "MOVZ": `imm` at bit `16 * hw` of zeros; "MOVK":
  `imm` into bits `16 * hw + 15 : 16 * hw` of the destination, the others
  unchanged (`hw < 2` for 32-bit, `hw < 4` for 64-bit);
* "LDR (immediate)": the loaded value is zero-extended; "STR (immediate)":
  the low `size` bits are stored;
* "LDR (immediate)" with `n == 31` (`ldrSp`): `address = SP[]`, then as
  above, `address + offset` with `offset = LSL(imm12, 3)`; `data = Mem[address,
  8]`; `X[t, 64] = data`;
* "STR (immediate)" with `n == 31` (`strSp`): the same address; `data =
  X[t, 64]`; `Mem[address, 8] = data`;
* "LDRB (immediate)": `data = Mem[address, 1]; X[t, 32] = ZeroExtend(data,
  32)` (hence zero-extended to 64 bits); "STRB (immediate)": `data = X[t,
  8]; Mem[address, 1] = data`, the low byte of `t`;
* "LDP" and "STP", 64-bit (`opc = '10'`, `scale = 3`), signed offset
  (`wback = FALSE`, `postindex = FALSE`): `offset = LSL(SignExtend(imm7,
  64), scale)`, only the non-negative ones (`imm7 < 64`, so `off = 8 *
  imm7 ≤ 504`); `address = X[n, 64] + offset`; `dbytes = 8`. STP:
  `Mem[address, dbytes] = X[t, 64]; Mem[address + dbytes, dbytes] = X[t2,
  64]`. LDP: `data1 = Mem[address, dbytes]; data2 = Mem[address + dbytes,
  dbytes]; X[t, 64] = data1; X[t2, 64] = data2`. An LDP with `t == t2` is
  CONSTRAINED UNPREDICTABLE (`Unpredictable_LDPOVERLAP`: UNKNOWN values,
  UNDEFINED or a NOP), so it faults. Without writeback, `t` or `t2` may be
  `n`: the address is computed before either is written. Both are baseline
  A64 instructions. See Arm DDI 0487 C6.2 "LDP", "STP" and
  https://developer.arm.com/documentation/ddi0602/2025-09/Base-Instructions/LDP--Load-pair-of-registers-
  https://developer.arm.com/documentation/ddi0602/2025-09/Base-Instructions/STP--Store-pair-of-registers-;
* an AdvSIMD or cryptographic instruction: `VOp.eval`;
* "LDR (immediate, SIMD&FP)", "STR (immediate, SIMD&FP)" (128-bit, unsigned
  offset: `offset = LSL(imm12, 4)`): `V[t] = Mem[address, 16]` and
  `Mem[address, 16] = V[t]`;
* "UMOV": `X[d, datasize] = ZeroExtend(Elem[V[n], index, esize], datasize)`,
  with `esize = datasize` (32 or 64). -/
def exec : Instr → State → Option State
  | .add sz d n m, s => some (s.write sz d (s.read sz n + s.read sz m))
  | .sub sz d n m, s => some (s.write sz d (s.read sz n - s.read sz m))
  | .adds sz d n m, s => some (s.addWithCarry sz d (s.read sz n) (s.read sz m) false)
  | .adcs sz d n m, s => some (s.addWithCarry sz d (s.read sz n) (s.read sz m) s.c)
  | .subs sz d n m, s => some (s.addWithCarry sz d (s.read sz n) (~~~s.read sz m) true)
  | .sbcs sz d n m, s => some (s.addWithCarry sz d (s.read sz n) (~~~s.read sz m) s.c)
  | .adc sz d n m, s =>
    some (s.write sz d (s.read sz n + s.read sz m + BitVec.ofNat sz.bits s.c.toNat))
  | .sbc sz d n m, s =>
    some (s.write sz d (s.read sz n + ~~~s.read sz m + BitVec.ofNat sz.bits s.c.toNat))
  | .csel sz d n m, s => some (s.write sz d (if s.c then s.read sz n else s.read sz m))
  | .tst sz n m, s =>
    some { s with
      nf := (s.read sz n &&& s.read sz m).msb
      zf := decide ((s.read sz n &&& s.read sz m) = 0)
      c := false
      vf := false }
  | .ccmp sz n imm nzcv cond, s =>
    if imm < 32 ∧ nzcv < 16 then
      some (if cond.holds s then s.flagsAdd (s.read sz n) (~~~(BitVec.ofNat sz.bits imm)) true
        else { s with
          nf := nzcv.testBit 3
          zf := nzcv.testBit 2
          c := nzcv.testBit 1
          vf := nzcv.testBit 0 })
    else none
  | .cselc sz d n m cond, s => some (s.write sz d (if cond.holds s then s.read sz n else s.read sz m))
  | .csneg sz d n m cond, s => some (s.write sz d (if cond.holds s then s.read sz n else -s.read sz m))
  | .adrSym d name, s => some (s.write .x d (s.syms name))
  | .addImm sz d n imm, s =>
    if imm < 4096 then some (s.write sz d (s.read sz n + BitVec.ofNat _ imm)) else none
  | .subImm sz d n imm, s =>
    if imm < 4096 then some (s.write sz d (s.read sz n - BitVec.ofNat _ imm)) else none
  | .logic op sz d n m, s =>
    let a := s.read sz n
    let b := s.read sz m
    some (s.write sz d (match op with | .and => a &&& b | .orr => a ||| b | .eor => a ^^^ b))
  | .logicRor op sz d n m sh, s =>
    if sh < sz.bits then
      let a := s.read sz n
      let b := (s.read sz m).rotateRight sh
      some (s.write sz d (match op with | .and => a &&& b | .orr => a ||| b | .eor => a ^^^ b))
    else none
  | .bicRor sz d n m sh, s =>
    if sh < sz.bits then
      some (s.write sz d (s.read sz n &&& ~~~((s.read sz m).rotateRight sh)))
    else none
  | .ror sz d n sh, s =>
    if sh < sz.bits then some (s.write sz d ((s.read sz n).rotateRight sh)) else none
  | .extr sz d n m lsb, s =>
    if lsb < sz.bits then
      some (s.write sz d ((s.read sz n ++ s.read sz m).extractLsb' lsb sz.bits))
    else none
  | .lsr sz d n sh, s =>
    if sh < sz.bits then some (s.write sz d (s.read sz n >>> sh)) else none
  | .lsl sz d n sh, s =>
    if sh < sz.bits then some (s.write sz d (s.read sz n <<< sh)) else none
  | .madd sz d n m a, s => some (s.write sz d (s.read sz a + s.read sz n * s.read sz m))
  | .mul sz d n m, s => some (s.write sz d (s.read sz n * s.read sz m))
  -- DDI 0487 C6.2, UMULH: UInt(X[n]) * UInt(X[m]), bits 127:64.
  | .umulh d n m, s =>
    some (s.write .x d (BitVec.ofNat 64 ((s.gpr n).toNat * (s.gpr m).toNat / 2 ^ 64)))
  -- DDI 0602 (A64 ISA XML 2025-12), UMADDL: operand1 = X(n)<31:0>,
  -- operand2 = X(m)<31:0>, operand3 = X(a); result = UInt(operand3) +
  -- UInt(operand1) * UInt(operand2); X(d) = result<63:0>. UMULL is UMADDL
  -- with Ra = XZR (operand3 = 0).
  | .umaddl d n m a, s =>
    some (s.write .x d (s.gpr a + (s.read .w n).setWidth 64 * (s.read .w m).setWidth 64))
  | .umull d n m, s =>
    some (s.write .x d ((s.read .w n).setWidth 64 * (s.read .w m).setWidth 64))
  -- DDI 0487 C6.2, CLZ: result = CountLeadingZeroBits(X[n, datasize]);
  -- X[d, datasize] = result<datasize-1:0>. CountLeadingZeroBits(x) is
  -- N - (HighestSetBit(x) + 1) (J1, shared pseudocode), `BitVec.clz`.
  | .clz sz d n, s => some (s.write sz d (s.read sz n).clz)
  -- DDI 0487 C6.2, RBIT: for i = 0 to datasize-1,
  -- result<datasize-1-i> = operand<i>; `BitVec.reverse`.
  | .rbit sz d n, s => some (s.write sz d (s.read sz n).reverse)
  | .rev32 d n, s => some (s.write .w d (rev32 (s.read .w n)))
  | .rev d n, s => some (s.write .x d (rev64 (s.read .x n)))
  | .movz sz d imm hw, s =>
    if 16 * hw < sz.bits then some (s.write sz d (imm.setWidth sz.bits <<< (16 * hw))) else none
  | .movk sz d imm hw, s =>
    if 16 * hw < sz.bits then
      let mask : BitVec sz.bits := (0xFFFF : BitVec sz.bits) <<< (16 * hw)
      some (s.write sz d ((s.read sz d &&& ~~~mask) ||| (imm.setWidth sz.bits <<< (16 * hw))))
    else none
  | .ldr sz t n off, s =>
    (addr s sz.bytes n off).bind fun a =>
      (s.load a sz.bytes).map fun v => s.write sz t (v.setWidth sz.bits)
  | .str sz t n off, s =>
    (addr s sz.bytes n off).bind fun a => s.store a sz.bytes ((s.read sz t).setWidth (8 * sz.bytes))
  | .ldrb t n off, s =>
    (addr s 1 n off).bind fun a => (s.load a 1).map fun v => s.write .w t (v.setWidth 32)
  | .strb t n off, s =>
    (addr s 1 n off).bind fun a => s.store a 1 ((s.read .w t).setWidth 8)
  | .ldp t1 t2 n off, s =>
    if t1 ≠ t2 ∧ off % 8 = 0 ∧ off ≤ 504 then
      let a := s.gpr n + BitVec.ofNat 64 off
      (s.load a 8).bind fun v₁ => (s.load (a + 8) 8).map fun v₂ =>
        (s.write .x t1 (v₁.setWidth 64)).write .x t2 (v₂.setWidth 64)
    else none
  | .stp t1 t2 n off, s =>
    if off % 8 = 0 ∧ off ≤ 504 then
      let a := s.gpr n + BitVec.ofNat 64 off
      (s.store a 8 ((s.read .x t1).setWidth 64)).bind fun s' =>
        s'.store (a + 8) 8 ((s.read .x t2).setWidth 64)
    else none
  | .ldrSp t off, s =>
    if off % 8 = 0 ∧ off < 32768 then
      (s.load (s.sp + BitVec.ofNat 64 off) 8).map fun v => s.write .x t (v.setWidth 64)
    else none
  | .strSp t off, s =>
    if off % 8 = 0 ∧ off < 32768 then
      s.store (s.sp + BitVec.ofNat 64 off) 8 ((s.read .x t).setWidth 64)
    else none
  | .addSp d imm, s =>
    if imm < 4096 then some (s.write .x d (s.sp + BitVec.ofNat 64 imm)) else none
  | .vop op, s => (op.eval s).map fun (d, x) => s.setV d x
  | .ldrq t n off, s => (addr s 16 n off).bind fun a => (s.load a 16).map fun x => s.setV t x
  | .strq t n off, s => (addr s 16 n off).bind fun a => s.store a 16 (s.v t)
  -- `ldrqTbl`: as `ldrq t n off`, its source the 16 bytes at `n + off`,
  -- little-endian: when `n` holds the static's address and `off` is an
  -- offset `ldrq` encodes (a multiple of 16, less than 65536: the scaled
  -- 12-bit immediate of LDR (immediate, SIMD&FP), DDI 0487 C7.2) with two
  -- words of the table from there, words `off / 8` and `off / 8 + 1` of the
  -- static `name` (bits 63:0 the first); otherwise it faults. The static is
  -- the immutable object of these words the emitter writes (see the module
  -- docs), so the bytes there are always these.
  | .ldrqTbl t n off name ws, s =>
    if s.gpr n = s.syms name ∧ off % 16 = 0 ∧ off < 65536 ∧ off / 8 + 2 ≤ ws.length then
      some (s.setV t (ws.getD (off / 8 + 1) 0 ++ ws.getD (off / 8) 0))
    else none
  -- `ldrTbl`: as `ldr sz t n off`, its source the 8 (`.x`) or 4 (`.w`) bytes
  -- at `n + off`, little-endian: when `n` holds the static's address and
  -- `off` is an offset `ldr` encodes (a multiple of the access size, less
  -- than 4096 times it: the scaled 12-bit immediate of LDR (immediate),
  -- unsigned offset, DDI 0487 C6.2, as `addr` has it) in a word of the
  -- table, the bytes `off % 8` and on of word `off / 8` of the static
  -- `name`: all of it (`.x`), or its low (`off % 8 = 0`) or high
  -- (`off % 8 = 4`) half, zero-extended into the 64-bit register, as LDR's
  -- 32-bit form does (`X[t, regsize] = ZeroExtend(data, regsize)`, which
  -- `write` is). Otherwise it faults. The static is the immutable object of
  -- these words the emitter writes (see the module docs), so the bytes
  -- there are always these.
  | .ldrTbl sz t n off name ws, s =>
    if s.gpr n = s.syms name ∧ off % sz.bytes = 0 ∧ off < 4096 * sz.bytes ∧ off / 8 < ws.length then
      some (s.write sz t ((ws.getD (off / 8) 0).extractLsb' (8 * (off % 8)) sz.bits))
    else none
  | .umov sz d n i, s =>
    if i * sz.bits < 128 then some (s.write sz d ((s.v n).extractLsb' (sz.bits * i) sz.bits))
    else none
  -- DDI 0487 C6.2, "NOP": no effect but on the PC, which the model does not
  -- have.
  | .align _, s => some s
  -- The system register DIT (DDI 0601 2026-03, "DIT, Data Independent
  -- Timing"): bit 24 is PSTATE.DIT, bits 63:25 and 23:0 are RES0. Its
  -- reader is the same at every exception level, EL0 included: `MRS <Xt>,
  -- DIT` is `X{64}(t) = Zeros{39} :: PSTATE.DIT :: Zeros{24}`.
  | .mrsDit t, s => some (s.write .x t (if s.dit then 0x1000000#64 else 0#64))
  -- DDI 0602 2026-03, "MSR (immediate)" (A64 ISA XML, `msr_imm.xml`): for
  -- `op1 = '011'`, `min_EL = EL0`, so EL0 may execute it; `operand = CRm`,
  -- and for `op1::op2 = '011 010'`, `field = PSTATEField_DIT`, whose
  -- execution is `PSTATE.DIT = operand[0]`. `imm` (`CRm`) is 0 or 1 here.
  | .msrDitImm on, s => some { s with dit := on }
  -- DDI 0602 2026-03, "DSB" (`DataSynchronizationBarrier`), "ISB"
  -- (`InstructionSynchronizationBarrier`), "SB" (`SpeculationBarrier`): they
  -- order and complete memory accesses, synchronize context and limit
  -- speculation, none of which the model has, and write no register,
  -- memory or PSTATE field.
  | .barrier _, s => some s
  -- Frame delimiters execute only through `push` and `pop`, and the
  -- instruction of an indirect call only through `icall`.
  | .push _, _ | .pop _, _ | .alloc _, _ | .free _, _ | .blr _, _ => none

def addrs : Instr → State → List Addr
  | .ldr _ _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .str _ _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .ldrb _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .strb _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .ldp _ _ n off, s | .stp _ _ n off, s =>
    [s.gpr n + BitVec.ofNat 64 off, s.gpr n + BitVec.ofNat 64 off + 8]
  | .ldrq _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .strq _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  -- The offset in the table: the static's address does not depend on the
  -- data (see the module docs).
  | .ldrqTbl _ _ off .., _ => [BitVec.ofNat 64 off]
  | .ldrTbl _ _ _ off .., _ => [BitVec.ofNat 64 off]
  | .ldrSp _ off, s | .strSp _ off, s => [s.sp + BitVec.ofNat 64 off]
  | .push _, s => [s.sp - 16]
  | .pop _, s => [s.sp]
  | _, _ => []

/-- DDI 0487 C6.2, "CBZ"/"CBNZ": the branch is taken iff the operand is (not) zero. -/
def eval : Cond → State → Option Bool
  | .zero sz r, s => some (s.read sz r == 0)
  | .nonzero sz r, s => some (s.read sz r != 0)

/-- DDI 0487, C6.2 "BL": `X[30, 64] = PC64 + 4` (the address of the next
instruction), then the branch, possibly through a linker veneer, which may
change `x16` and `x17` (AAPCS64 §6.1.1). The return address and the values
left in `x16` and `x17` are the next three of the state's unknowns. The
fourth supplies independent N, Z, C and V bits: AAPCS64 §6.1.1 makes NZCV undefined
at public interfaces, and AAELF64 §5.7.7 (Call and Jump relocations) permits
veneers to corrupt it.
https://github.com/ARM-software/abi-aa/blob/main/aaelf64/aaelf64.rst -/
def call (s : State) : Option State :=
  some { s with
    gpr := fun r =>
      if r = .x30 then s.unknowns 0 else if r = .x16 then s.unknowns 1
      else if r = .x17 then s.unknowns 2 else s.gpr r
    c := (s.unknowns 3).getLsbD 0
    nf := (s.unknowns 3).getLsbD 1
    zf := (s.unknowns 3).getLsbD 2
    vf := (s.unknowns 3).getLsbD 3
    unknowns := fun n => s.unknowns (n + 4) }

/-- DDI 0487, C6.2 "RET" (with the default register `x30`): `target =
X[30, 64]; BranchTo(target)`. It returns after the call instruction if `x30`
is the return address the call left (`s₁`); otherwise the model faults. -/
def ret (s₁ s₂ : State) : Option State :=
  if s₂.gpr .x30 = s₁.gpr .x30 then some s₂ else none

/-- The push of a frame, DDI 0487 C6.2 "STR (immediate)", 64-bit, pre-index
(`str xr, [sp, #-16]!`): `address = SP[] + offset` with `offset = -16`;
`Mem[address, 8] = X[t]`; `SP[] = address`. The 16 bytes (the register,
then 8 bytes it does not write) become a writable region, at the head of
`wr`. Faults if the frame would wrap around the address space
(`sp < 16`).

The model grants 16 bytes but writes only the first 8, so `[sp, #8]` then
holds what memory held there before the push. That memory was below the
stack pointer, where on hardware a signal handler may change it at any
time, while the model keeps it until a store. This is harmless: the
contract says nothing of those bytes (they are in the stack below the
caller's stack pointer, `Abi.reserved`, which no buffer overlaps), so a
proof holds whatever they contain and learns nothing from reading them;
it could only rely on two reads agreeing. `ldrSp` and `strSp` can read
and write the frame directly, and `addSp` can form a pointer to it. None
grants permission below the currently allocated stack: `strSp` stores
through `State.store`, which faults outside the writable regions, so it
reaches only a frame's bytes (or a writable buffer that happens to lie at
or above the stack pointer).

DDI 0602, ADD/SUB (immediate), `sf=1`, `sh=0`, `Rn=Rd=31`:
`operand1 = SP[64]`, and the non-flag-setting result is written to `SP[64]`.
`addSp` uses `Rn=31`, `Rd != 31` and writes the result to `X[d,64]`.
These are baseline A64 instructions, requiring no optional feature.
https://developer.arm.com/documentation/ddi0602/2025-09/Base-Instructions/ADD--immediate---Add--immediate--
https://developer.arm.com/documentation/ddi0602/2025-09/Base-Instructions/SUB--immediate---Subtract--immediate--

`alloc`/`free` are accepted only as frame delimiters, never by `exec`.
Allocation grants one contiguous region without initializing it, exactly
as the unwritten half of the existing `push` frame. The size is a positive,
16-byte-aligned unshifted immediate; allocation cannot underflow. Release
requires the matching region and unchanged SP and permissions.
-/
def push : Instr → State → Option State
  | .alloc bytes, s =>
    if 0 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ bytes ≤ s.sp.toNat then
      let sp := s.sp - BitVec.ofNat 64 bytes
      some { s with sp := sp, wr := ⟨sp, bytes⟩ :: s.wr }
    else none
  | .push r, s =>
    if 16 ≤ s.sp.toNat then
      let sp := s.sp - 16
      some { s with sp := sp, mem := s.mem.write sp 8 (s.gpr r), wr := ⟨sp, 16⟩ :: s.wr }
    else none
  | _, _ => none

/-- The memory once the `n` bytes at `a`, a released frame, are below the
stack pointer. AAPCS64 (release 2026Q3), 6.4.5 "The Stack": "The inactive
region of T's stack is the area of memory denoted by the half-open interval
[T.limit, T.SP)", and 6.4.5.1 "Universal stack constraints": "No thread is
permitted to access (for reading or for writing) the inactive region of S."
Anything that runs on the stack between two instructions (a signal handler)
may have written them, and the code can assume nothing of them. Apple's
platforms keep more: "The ARM64 red zone consists of the 128 bytes
immediately below the stack pointer. Apple platforms don't modify these
bytes during exceptions" ("Writing ARM64 code for Apple platforms",
"Respect the stack's red zone"); a byte that keeps its value is one of the
outcomes here, so the model holds on those targets too, and it lets no
proof use the red zone (the code may access only its regions, none of which
is below the stack pointer). Each byte either keeps its value or takes one
the model does not know, as the unknowns say: for the doubleword `j` of the
frame, the bytes of `u (2 * j)` say which of its bytes are replaced (those
not zero), and the bytes of `u (2 * j + 1)` are what replaces them. A byte
may keep its value, so what a function leaves in a frame it releases may be
left there (`NoResidue`, whose two runs share their unknowns, still tells
apart a frame that holds a secret). -/
def lose (m : Mem) (a : Addr) (n : Nat) (u : Nat → BitVec 64) : Mem :=
  fun x =>
    let d := (x - a).toNat
    if d < n then
      if (u (2 * (d / 8))).extractLsb' (8 * (d % 8)) 8 = 0 then m x
      else (u (2 * (d / 8) + 1)).extractLsb' (8 * (d % 8)) 8
    else m x

/-- The pop of a frame, DDI 0487 C6.2 "LDR (immediate)", 64-bit, post-index
(`ldr xr, [sp], #16`): `address = SP[]`; `data = Mem[address, 8]`; `SP[] =
address + 16`; `X[t] = data`. Faults unless the stack pointer and the
writable regions are those the push left (`s₁`), whose head is the frame;
it removes the frame. `free bytes` is `add sp, sp, #bytes` alone, likewise
for the frame of `alloc bytes`. The released frame's bytes are then below
the stack pointer, and are `lose`'s: the next of the state's `unknowns`,
two for each doubleword of the frame, say what each holds. -/
def pop : Instr → State → State → Option State
  | .free bytes, s₁, s₂ =>
    if 0 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧
        s₂.sp = s₁.sp ∧ s₂.wr = s₁.wr ∧ s₁.wr.head? = some ⟨s₁.sp, bytes⟩ then
      some { s₂ with
        sp := s₂.sp + BitVec.ofNat 64 bytes, wr := s₂.wr.tail,
        mem := lose s₂.mem s₂.sp bytes s₂.unknowns,
        unknowns := fun n => s₂.unknowns (n + bytes / 4) }
    else none
  | .pop r, s₁, s₂ =>
    if s₂.sp = s₁.sp ∧ s₂.wr = s₁.wr ∧ s₁.wr.head? = some ⟨s₁.sp, 16⟩ then
      some { s₂.write .x r (s₂.mem.read s₂.sp 8) with
        sp := s₂.sp + 16, wr := s₂.wr.tail, mem := lose s₂.mem s₂.sp 16 s₂.unknowns,
        unknowns := fun n => s₂.unknowns (n + 4) }
    else none
  | _, _, _ => none

/-- The CPU features an instruction needs beyond the AArch64 baseline
(ARMv8.0-A with AdvSIMD, which every Rust AArch64 target but
`aarch64-unknown-none-softfloat` assumes, and the target's `rustCfg`
requires), named as
Rust's target features. DDI 0487 A2 ("Armv8-A architecture extensions") and
the "Is FEAT_…" condition in each instruction's decode (C7.2): FEAT_AES for
AESE, AESD, AESMC, AESIMC and FEAT_PMULL for PMULL/PMULL2 with 64-bit
sources, which Rust's `aes` feature covers together (PMULL/PMULL2 with 8-bit
sources, `pmull8`, need AdvSIMD alone, the baseline: A64 ISA XML 2026-03,
"PMULL, PMULL2", decodes `if size == '01' || size == '10' then
EndOfDecode(Decode_UNDEF); end; if size == '11' &&
!IsFeatureImplemented(FEAT_PMULL) then EndOfDecode(Decode_UNDEF); end;`, and
says "The PMULL and PMULL2 variants that operate on 64-bit source elements
are defined only when FEAT_PMULL is implemented"); FEAT_SHA1 for SHA1C,
SHA1P, SHA1M, SHA1H, SHA1SU0, SHA1SU1 and FEAT_SHA256 for SHA256H,
SHA256H2, SHA256SU0, SHA256SU1 (Rust's `sha2`); FEAT_SHA512 for SHA512H,
SHA512H2, SHA512SU0, SHA512SU1 and FEAT_SHA3 for EOR3, BCAX, RAX1, XAR
(Rust's `sha3`); FEAT_SM4 for SM4E and SM4EKEY (A64 ISA XML 2025-12, "SM4E",
"SM4EKEY": `if !IsFeatureImplemented(FEAT_SM4) then
EndOfDecode(Decode_UNDEF); end;`), Rust's `sm4`, which stands for FEAT_SM4
and FEAT_SM3 together, so that it is also what SM3SS1, SM3TT1A, SM3TT1B,
SM3TT2A, SM3TT2B, SM3PARTW1 and SM3PARTW2 need (`if
!IsFeatureImplemented(FEAT_SM3) then EndOfDecode(Decode_UNDEF); end;`); FEAT_SVE2 for SVE2's XAR (DDI 0602, "XAR": `if
!IsFeatureImplemented(FEAT_SVE2) && !IsFeatureImplemented(FEAT_SME) then
UNDEFINED`; Rust's `sve2`, which implies `sve`, since FEAT_SVE2 requires
FEAT_SVE); FEAT_DIT for MRS of the system register DIT (DDI 0601 2026-03,
"DIT, Data Independent Timing": "This register is present only when FEAT_DIT
is implemented and FEAT_AA64 is implemented. Otherwise, direct accesses to
DIT are UNDEFINED", and its accessor begins `if
!(IsFeatureImplemented(FEAT_DIT) && IsFeatureImplemented(FEAT_AA64)) then
Undefined();`) and for MSR (immediate) of PSTATE.DIT (DDI 0602 2026-03,
"MSR (immediate)": `when '011 010' => if !IsFeatureImplemented(FEAT_DIT) then
EndOfDecode(Decode_UNDEF);`), Rust's `dit`; FEAT_SB for SB (DDI 0602
2026-03, "SB": `if !IsFeatureImplemented(FEAT_SB) then
EndOfDecode(Decode_UNDEF); end;`), Rust's `sb`. DSB and ISB are in the
baseline. -/
def Instr.requires : Instr → List String
  | .vop (.aese ..) | .vop (.aesd ..) | .vop (.aesmc ..) | .vop (.aesimc ..)
  | .vop (.pmull ..) => ["aes"]
  | .vop (.sha1 ..) | .vop (.sha1h ..) | .vop (.sha1su0 ..) | .vop (.sha1su1 ..)
  | .vop (.sha256h ..) | .vop (.sha256h2 ..) | .vop (.sha256su0 ..) | .vop (.sha256su1 ..) =>
    ["sha2"]
  | .vop (.sha512h ..) | .vop (.sha512h2 ..) | .vop (.sha512su0 ..) | .vop (.sha512su1 ..)
  | .vop (.eor3 ..) | .vop (.bcax ..) | .vop (.rax1 ..) | .vop (.xar ..) => ["sha3"]
  | .vop (.sm4e ..) | .vop (.sm4ekey ..)
  | .vop (.sm3ss1 ..) | .vop (.sm3tt ..) | .vop (.sm3partw1 ..) | .vop (.sm3partw2 ..) => ["sm4"]
  | .vop (.xarS ..) => ["sve2"]
  | .mrsDit _ | .msrDitImm _ => ["dit"]
  | .barrier .sb => ["sb"]
  | _ => []

/-- The address an indirect call instruction calls: DDI 0487, C6.2 "BLR":
"Branch with Link to Register calls a subroutine at an address in a
register, setting register X30 to PC+4": `target = X[n, 64]; X[30, 64] =
PC64 + 4; BranchTo(target, BranchType_INDCALL)`. Setting `x30` and the
rest of the call are the direct call's (`call`), the return `ret`. The
flags are not affected. -/
def icall : Instr → State → Option Addr
  | .blr n, s => some (s.gpr n)
  | _, _ => none

abbrev isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := eval
  call := call
  callAddrs _ := []
  ret := ret
  retAddrs _ := []
  -- No modelled instruction writes the stack pointer, other than the push
  -- and pop of a frame (`ldrSp` and `strSp` only read it).
  writesSp _ := false
  push := push
  pop := pop
  requires := Instr.requires
  icall := icall
  -- A function's symbol, as a static's (`adrSym`).
  fnAddr s name := s.syms name

end VG.AArch64
