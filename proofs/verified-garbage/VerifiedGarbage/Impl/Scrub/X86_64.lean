module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Returning without secret residue (x86-64)

`scrub v retBits cs c` runs `c`, then clears everything `c` may have left
where its Rust caller cannot clear it (`X86_64.NoResidue`):

* the SSE registers, with `pxor x, x` (`v = .sse`, for code without VEX or
  EVEX instructions, which leaves their upper halves as the caller left
  them) or `vpxor x, x, x` (`v = .avx`, which also zeroes bits 511:128 of
  `zmm0`–`zmm15`); with `v = .evex`, for code that may write `zmm16`–`zmm31`
  or MXCSR, those registers too (`vpxorq z, z, z`), and MXCSR's status
  flags and reserved bits (`mxFix`), which leaves in it its control bits,
  those the code keeps (`abiPreserved`), with every status flag set, so
  that the flags code before it set stay set for the code after it (with
  the default control bits, that is `0x1FBF`, Intel's mitigation of MCDT:
  see "MCDT" in `TCB/X86_64/Isa.lean`);
* the stack below the stack pointer, within its `cs.sum` bytes (the stack
  `c`'s frames and calls use), in nested frames of the sizes `cs` (each
  less than a page, as `alloc` requires): the granules (16 bytes of `xmm0`,
  or the 8 bytes of `r11` at the bottom of a frame whose size is not a
  multiple of 16) at the offsets `ks` from the bottom, each frame from its
  top down. The granules are those an analysis of `c` finds may hold
  secrets (all of them, if `ks` lists them all): stack `c` itself wrote, so
  the stores touch no page `c` did not;
* the caller-saved general-purpose registers, with `xor r32, r32`, but the
  `retBits` low bits of `rax`, the result, whose upper bits it zeroes; the
  last `xor` leaves known flags.
-/

@[expose] public section

namespace VG.Impl.Scrub.X86_64

open VG.X86_64

/-- How the vector registers are cleared. -/
inductive VecLevel
  /-- `pxor`: for code that leaves bits 511:128 of the vector registers. -/
  | sse
  /-- `vpxor` (VEX.128): zeroes bits 511:128 of `zmm0`–`zmm15` too. -/
  | avx
  /-- As `avx`, with `vpxorq` (EVEX.512) of `zmm16`–`zmm31` and MXCSR's
  status flags cleared: for code that may write those. -/
  | evex
  deriving DecidableEq, Repr

def xregs : List XReg :=
  [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7,
   .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14, .xmm15]

def hregs : List HReg :=
  [.xmm16, .xmm17, .xmm18, .xmm19, .xmm20, .xmm21, .xmm22, .xmm23,
   .xmm24, .xmm25, .xmm26, .xmm27, .xmm28, .xmm29, .xmm30, .xmm31]

def zeroX : VecLevel → XReg → Instr
  | .sse, x => .xop (.bin .pxor x x)
  | .avx, x => .vop (.vbin .vpxor .l128 x x x)
  | .evex, x => .vop (.vbin .vpxor .l128 x x x)

/-- `vpxorq zmm, zmm, zmm`, of one of `zmm16`–`zmm31`. -/
def zeroH (h : HReg) : Instr := .e5op (.bin .vpxorq (.hi h) (.hi h) (.hi h))

/-- `zmm16`–`zmm31` zeroed, at the level `evex` alone. -/
def clearHigh : VecLevel → List Instr
  | .evex => hregs.map zeroH
  | _ => []

/-- At the level `evex`: MXCSR with its status flags (bits 5:0) set, which
nothing else clears, and its reserved bits (31:16,
as the code that restores it clears them: see "MXCSR" in
`TCB/X86_64/Isa.lean`) cleared, through 8 bytes of a frame of 16 below
the stack pointer; `r11` is left zero, as the wipe expects it. The only way
the generated code writes MXCSR is Intel's sequence around the instructions
MCDT affects (`ci/check_mcdt.py`), so this is that sequence, around none:
`stmxcsr` saves MXCSR, whose saved value is masked and has its flags set
(`and`, `or`); the prologue loads
`0x1FBF`; and the epilogue loads the saved value. -/
def mxFix : VecLevel → Prog isa
  | .evex => .frame (.alloc 16) (.block [.stmxcsr { base := .rsp }, .mov32 .r11 (.mem { base := .rsp }),
      .alu32 .and .r11 (.imm 0xFFC0), .alu32 .or .r11 (.imm 0x3F), .store32 { base := .rsp } .r11,
      .mov32 .r11 (.imm 0x1FBF), .store32 { base := .rsp, disp := 4 } .r11,
      .ldmxcsr { base := .rsp, disp := 4 }, .lfence, .lfence, .ldmxcsr { base := .rsp },
      .alu32 .xor .r11 (.reg .r11)]) (.free 16)
  | _ => .block []

def clearVec (v : VecLevel) : List Instr := xregs.map (zeroX v)

/-- `xor r32, r32`. -/
def zeroR (r : Reg) : Instr := .alu32 .xor r (.reg r)

/-- The caller-saved general-purpose registers but `rax`. -/
def scratchRegs : List Reg := [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

/-- Clear the bits of `rax` above a result of `retBits` bits. -/
def retFix (retBits : Nat) : List Instr :=
  if retBits = 0 then [zeroR .rax]
  else if retBits < 32 then [.alu32 .and .rax (.imm (BitVec.ofNat 32 (2 ^ retBits - 1)))]
  else if retBits = 32 then [.mov32 .rax (.reg .rax)]
  else []

/-- Clear the general-purpose registers (the last instruction an `xor`, for
the flags). -/
def clearGpr (retBits : Nat) : List Instr := retFix retBits ++ scratchRegs.map zeroR

/-- `movdqu [rsp + off], xmm0`. -/
def zero16 (off : Nat) : Instr := .movdquStore { base := .rsp, disp := (off : Int) } .xmm0

/-- `vmovdqu [rsp + off], ymm0`. -/
def zero32 (off : Nat) : Instr := .vmovdquStore .l256 { base := .rsp, disp := (off : Int) } .xmm0

/-- Whether the wipe may store 32 bytes at a time, from `ymm0`: at every
level but `sse`, whose zeroing of `xmm0` (`zeroX`) zeroes `ymm0`. -/
def VecLevel.wide : VecLevel → Bool
  | .sse => false
  | _ => true

/-- `zero16` at `base + 16 * k`, unless its offset from the bottom of the
wiped stack (`off` plus its offset in the frame) is not in `ks`. -/
def store1 (ks : List Nat) (off base k : Nat) : List Instr :=
  if ks.contains (off + base + 16 * k) then [zero16 (base + 16 * k)] else []

/-- The 16-byte granules at `base + 16 * (k - 1)`, …, `base + 16`, `base`
zeroed, from the top down, but those whose offset from the bottom of the
wiped stack is not in `ks`: each with `zero16`, or, if `w`, a granule and the
one below it, both in `ks`, with one `zero32`. -/
def stores16 (w : Bool) (ks : List Nat) (off base : Nat) : Nat → List Instr
  | 0 => []
  | 1 => store1 ks off base 0
  | k + 2 =>
    if w && ks.contains (off + base + 16 * (k + 1)) && ks.contains (off + base + 16 * k) then
      zero32 (base + 16 * k) :: stores16 w ks off base k
    else store1 ks off base (k + 1) ++ stores16 w ks off base (k + 1)

/-- The 8-byte store at `rsp` of a chunk whose size is not a multiple of 16,
if its offset `off` from the bottom of the wiped stack is in `ks`. -/
def store8s (ks : List Nat) (off b : Nat) : List Instr :=
  if b % 16 = 8 && ks.contains off then [.store { base := .rsp } .r11] else []

/-- Zero the `b` bytes at `rsp` (offset `off` from the bottom of the wiped
stack) from the top down, in 16-byte granules (and one 8-byte one at the
bottom, if `b` is not a multiple of 16), those whose offset is in `ks`. -/
def chunkStores (w : Bool) (ks : List Nat) (off b : Nat) : List Instr :=
  stores16 w ks off (b % 16) (b / 16) ++ store8s ks off b

/-- Zero the granules `ks` of the stack below `rsp`, in nested frames of the
sizes `cs`. -/
def wipe (w : Bool) (ks : List Nat) : List Nat → Prog isa
  | [] => .block []
  | b :: bs => .frame (.alloc b) (.seq (.block (chunkStores w ks bs.sum b)) (wipe w ks bs)) (.free b)

/-- Chunks of at most 4080 bytes (`fuel` of them at most) summing to `n`. -/
def chunksAux : Nat → Nat → List Nat
  | 0, _ => []
  | _ + 1, 0 => []
  | f + 1, n + 1 => if n + 1 ≤ 4080 then [n + 1] else 4080 :: chunksAux f (n + 1 - 4080)

def chunks (n : Nat) : List Nat := chunksAux (n / 4080 + 1) n

/-- The clearing: the SSE registers `xs`, at the level `evex` `zmm16`–`zmm31`
too, and the general-purpose registers
`ps` (`xmm0` and `r11`, which the wipe stores, if it stores any), at the
level `f` `evex` (by default `v`) MXCSR's status flags, the stack,
then the result's upper bits and the general-purpose registers `gs`. Code
that leaves the same MXCSR in two runs along the same path needs no `mxFix`
(`f` below `evex`), even if it writes `zmm16`–`zmm31`. -/
def scrubTail (v : VecLevel) (retBits : Nat) (xs : List XReg) (ps gs : List Reg) (ks cs : List Nat)
    (f : VecLevel := v) : Prog isa :=
  .seq (.block (xs.map (zeroX v) ++ clearHigh v ++ ps.map zeroR))
    (.seq (mxFix f) (.seq (wipe v.wide ks cs) (.block (retFix retBits ++ gs.map zeroR))))

/-- `c`, then the clearing. -/
def scrub (v : VecLevel) (retBits : Nat) (xs : List XReg) (ps gs : List Reg) (ks cs : List Nat) (c : Prog isa)
    (f : VecLevel := v) : Prog isa :=
  .seq c (scrubTail v retBits xs ps gs ks cs f)

/-! ## What to clear

Only what `c` may have written: a register it never writes holds what it
held on entry (`Proof/Framework/X86_64/Scrub.lean`). -/

/-- Whether an instruction may write a vector register (as `KeepReg.writesVec`). -/
def writesVec : Instr → Bool
  | .movdquLoad .. | .movdquTbl .. | .xop _ | .vop _ | .vmovdquLoad .. | .vmovdquTbl .. | .vbroadcasti128 .. | .vbinLoad ..
  | .zop _
  | .vmovdqu32Load .. | .vbroadcasti32x4 .. | .vbroadcasti32x4H .. | .zbcst .. | .vpbroadcastdZ .. | .zbcstd .. | .vpmadd52Load ..
  | .eop _ | .evLoad .. | .evMadd52Load .. | .kLoad .. | .kLoad8 ..
  | .e5op _ | .evBroadcastLoad .. | .e5InsertLoad .. => true
  | _ => false

/-- The SSE registers to clear: all of them, if `c` may write one; otherwise
`xmm0` if the wipe stores it (`ks` not empty). -/
def xsOf (c : Prog isa) (ks : List Nat) : List XReg :=
  if c.all (fun i => !writesVec i) then (if ks = [] then [] else [.xmm0]) else xregs

/-- `r11`, if the wipe stores it. -/
def psOf (ks : List Nat) : List Reg := if ks = [] then [] else [.r11]

/-- The scratch registers `c` may write (`Taint.clobbers`, as `dstOf` and
the frames' and `mul`'s registers), or `r11` alone if none, so that the last
`xor` leaves known flags. -/
def gsOf (clobbers : Instr → Reg → Bool) (c : Prog isa) : List Reg :=
  let w := scratchRegs.filter fun r => !c.all (fun i => !clobbers i r)
  if w = [] then [.r11] else w

end VG.Impl.Scrub.X86_64
