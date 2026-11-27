module

public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Impl.Scrub.X86_64
public import VerifiedGarbage.Proof.Framework.CodeOnce

/-!
# The checks of the scrub, compiled (x86-64)

The emitter evaluates the side conditions of the scrub of every x86-64
function (`Scrub.withScrubAll`, `RScrub.withScrub` and the others) on all of
its code: the level of its instructions (`Instr.vecLevel`), the stack it
uses (`Code.x86_64Depth`), the registers it writes (`Taint.clobbers`) and
what it leaves in MXCSR (`mxClass`). This module, which imports only the
trusted base and `CodeOnce`, holds their definitions, so that it can be
compiled (the library `NativeScrubX86_64`, `lakefile.toml`) and the emitter
run them as compiled code, an order of magnitude faster than in the
interpreter. What they mean is proven of them where it was, in the modules
that import this one: most of the x86-64 proofs, which a change here
rebuilds. The two checks that only the scrub's own modules use are in
`ScrubPaths.lean`.
-/

@[expose] public section

namespace VG

/-- The bytes of stack a frame's push takes. -/
def X86_64.Instr.frameBytes : X86_64.Instr → Nat
  | .push rs => 8 * rs.length
  | .alloc bytes => bytes
  | _ => 0

/-- The most stack below `rsp` that `c` uses at once, in bytes. -/
def Code.x86_64Depth : Prog X86_64.isa → Nat
  | .block _ => 0
  | .seq a b => max a.x86_64Depth b.x86_64Depth
  | .ite _ t e => max t.x86_64Depth e.x86_64Depth
  | .loop b _ => b.x86_64Depth
  | .call _ b => b.x86_64Depth + 8
  | .frame i b _ => b.x86_64Depth + i.frameBytes
  | .icall _ _ b n => max (b.x86_64Depth + 8) n.x86_64Depth

end VG

namespace VG.X86_64

/-- Whether an instruction loads MXCSR. -/
def loadsMxcsr : Instr → Bool
  | .ldmxcsr _ => true
  | _ => false

namespace Taint

/-- The general-purpose register an instruction writes, if it writes exactly
one (none for stores and SSE instructions, and for `mul` and `mulx`, which
write two). -/
def dstOf : Instr → Option Reg
  | .mov d _ | .mov32 d _ | .alu _ d _ | .alu32 _ d _ | .shift32 _ d _ | .bswap32 d
  | .rorx32 d .. | .andn32 d .. | .rorx d .. | .andn d .. | .movzx8 d _ | .movzx16 d _ | .bswap d | .shift _ d _
  | .shiftCl _ d | .shiftx _ d .. | .movImm64 d _ | .leaSym d _ | .adcx d _ | .adox d _ | .cmov _ d _
  | .vpmovmskb _ d _ | .vpcmpltuw d .. | .movqR d _ | .imul d _ | .imul3 d .. | .shld d .. | .btr d _ | .aluTbl _ d .. => some d
  | .store .. | .store32 .. | .store8 .. | .store16 .. | .movdquLoad .. | .movdquStore .. | .movdquTbl .. | .xop _
  | .vop _
  | .vmovdquLoad .. | .vmovdquStore .. | .vmovdquTbl .. | .vbroadcasti128 .. | .vbinLoad .. | .zop _
  | .vmovdqu32Load .. | .vmovdqu32Store .. | .vbroadcasti32x4 .. | .vbroadcasti32x4H .. | .zbcst .. | .vpbroadcastdZ .. | .zbcstd .. | .vpmadd52Load ..
  | .stmxcsr _ | .ldmxcsr _
  | .eop _ | .evLoad .. | .evStore .. | .evMadd52Load .. | .kLoad .. | .kStore .. | .kLoad8 .. | .kStore8 .. | .lfence
  | .e5op _ | .evBroadcastLoad .. | .e5InsertLoad .. | .e5ExtractStore ..
  | .mul _ | .mulx .. | .push _ | .pop .. | .alloc _ | .free _ | .callr _ => none

/-- Whether an instruction may write the general-purpose register `r`. -/
def clobbers (i : Instr) (r : Reg) : Bool :=
  match i with
  | .mul _ => r == .rax || r == .rdx
  | .mulx hi lo _ => r == hi || r == lo
  -- The push and pop of a frame move `rsp`, and the pop loads `d`.
  | .push _ | .alloc _ | .free _ => r == .rsp
  | .pop d _ => r == .rsp || r == d
  | _ => dstOf i == some r

end Taint

/-- An instruction's level: see the module docs of `ResidueKeep.lean`. -/
def Instr.vecLevel : Instr → Nat
  | .vop _ | .vmovdquLoad .. | .vmovdquTbl .. | .vbroadcasti128 .. | .vbinLoad ..
  | .vpmadd52Load .. | .zop _ | .vmovdqu32Load .. | .vbroadcasti32x4 .. | .zbcst ..
  | .vpbroadcastdZ .. | .zbcstd .. | .kLoad .. | .kLoad8 .. => 1
  | .vbroadcasti32x4H .. | .eop _ | .evLoad .. | .evMadd52Load .. | .ldmxcsr _
  | .e5op _ | .evBroadcastLoad .. | .e5InsertLoad .. => 2
  | _ => 0

/-- The level of the vector registers alone: `vecLevel`, but `ldmxcsr`,
which writes only MXCSR, at level 0. -/
def Instr.vecLevelR (i : Instr) : Nat := if loadsMxcsr i then 0 else i.vecLevel

/-- Whether `i` is at a level of at most `k`. -/
def Instr.levelLe (k : Nat) (i : Instr) : Bool := decide (i.vecLevel ≤ k)

/-- Whether `i` is at a level of the vector registers of at most `k`. -/
def Instr.levelLeR (k : Nat) (i : Instr) : Bool := decide (i.vecLevelR ≤ k)

/-- Whether every instruction of `c` is at a level of at most `k`
(`Code.allOnce`). -/
def levelLeOnce (k : Nat) (c : Prog isa) : Bool := c.allOnce (Instr.levelLe k)

/-- Whether every instruction of `c` is at a level of the vector registers of
at most `k` (`Code.allOnce`). -/
def levelLeROnce (k : Nat) (c : Prog isa) : Bool := c.allOnce (Instr.levelLeR k)

/-- Whether no instruction of `c` may write a vector register. -/
def noVec (c : Prog isa) : Bool := c.all fun i => !Impl.Scrub.X86_64.writesVec i

namespace RTaint

/-- The memory an instruction may write: its operand and width. -/
def storeW : Instr → Option (MemOp × Nat)
  | .store m _ => some (m, 8)
  | .store32 m _ => some (m, 4)
  | .store8 m _ => some (m, 1)
  | .store16 m _ => some (m, 2)
  | .movdquStore m _ => some (m, 16)
  | .vmovdquStore .l128 m _ => some (m, 16)
  | .vmovdquStore .l256 m _ => some (m, 32)
  | .vmovdqu32Store m _ => some (m, 64)
  | .evStore m _ | .e5ExtractStore m _ _ => some (m, 32)
  | .stmxcsr m => some (m, 4)
  | _ => none

/-- Whether an instruction may write memory: those of `storeW`, and the
masked stores. -/
def writesMem (i : Instr) : Bool :=
  (storeW i).isSome || match i with
    | .kStore .. | .kStore8 .. => true
    | _ => false

end RTaint

/-- `stmxcsr [m]; mov r32, [m]; and r32, 0xFFFF`: MXCSR, but for its
reserved bits, in `r`. -/
def mxcsrSave (m : MemOp) (r : Reg := .r11) : List Instr :=
  [.stmxcsr m, .mov32 r (.mem m), .alu32 .and r (.imm 0xFFFF)]

/-- `mov [m], r32; ldmxcsr [m]`: MXCSR from `r`. -/
def mxcsrRestore (m : MemOp) (r : Reg := .r11) : List Instr := [.store32 m r, .ldmxcsr m]

/-- The operand and register of a block that may be `mxcsrSave`. -/
def saveOp : List Instr → Option (MemOp × Reg)
  | .stmxcsr m :: .mov32 r _ :: _ => some (m, r)
  | _ => none

/-- The operand of a block that may be `mxcsrRestore`. -/
def restoreOp : List Instr → Option MemOp
  | .store32 m _ :: _ => some m
  | _ => none

/-- What code leaves in MXCSR: what it held on entry (`keep`), or that but
for its reserved bits (`mask`, what `mxcsrSave` then `mxcsrRestore` leave). -/
inductive MxC where
  | keep
  | mask
  deriving DecidableEq

/-- MXCSR after code of class `k`, from `x` on entry. -/
def MxC.app : MxC → BitVec 32 → BitVec 32
  | .keep, x => x
  | .mask, x => x &&& 0xFFFF

/-- The class of code of class `a`, then of class `b`. -/
def MxC.comp : MxC → MxC → MxC
  | .keep, .keep => .keep
  | _, _ => .mask

/-- `restores`, computed (with `Code.all`), for the emitter. -/
def restoresC (a b : Prog isa) : Bool :=
  match a, b with
  | .block is, .seq mid (.block js) =>
    match saveOp is, restoreOp js with
    | some (m, r), some m' =>
      is == mxcsrSave m r && js == mxcsrRestore m' r && mid.all fun i => !Taint.clobbers i r
    | _, _ => false
  | _, _ => false

/-- The class of what `c` leaves in MXCSR, if every path through it leaves
the same function of MXCSR on entry (see the module docs). -/
def mxClass : Prog isa → Option MxC
  | .block is => if is.all (fun i => !loadsMxcsr i) then some .keep else none
  | .seq a b =>
    if restoresC a b then some .mask else
    match mxClass a, mxClass b with
    | some x, some y => some (x.comp y)
    | _, _ => none
  | .ite _ t e =>
    match mxClass t, mxClass e with
    | some x, some y => if x = y then some x else none
    | _, _ => none
  | .loop b _ => mxClass b
  | .call _ b => mxClass b
  | .frame i b j => if !loadsMxcsr i && !loadsMxcsr j then mxClass b else none
  | .icall i _ b n =>
    if loadsMxcsr i then none else
    match mxClass b, mxClass n with
    | some x, some y => if x = y then some x else none
    | _, _ => none

namespace RScrub

/-- `mxClass c`, given calls with their class (`k`: a call's function, code
and class), with those calls and the calls of `c`: `mxClass` follows the
code of a function once per call of it, through every function that calls
it, and this once (`Code.memoCall`). -/
def mxClassFrom : Prog isa → List (String × Prog isa × Unit × Option MxC) →
    Option MxC × List (String × Prog isa × Unit × Option MxC)
  | .block is, k => (if is.all (fun i => !loadsMxcsr i) then some .keep else none, k)
  | .seq a b, k =>
    if restoresC a b then (some .mask, k) else
    let r := mxClassFrom a k
    match r.1 with
    | some x =>
      let q := mxClassFrom b r.2
      (match q.1 with
      | some y => (some (x.comp y), q.2)
      | none => (none, q.2))
    | none => (none, r.2)
  | .ite _ t e, k =>
    let r := mxClassFrom t k
    match r.1 with
    | some x =>
      let q := mxClassFrom e r.2
      (match q.1 with
      | some y => (if x = y then some x else none, q.2)
      | none => (none, q.2))
    | none => (none, r.2)
  | .loop b _, k => mxClassFrom b k
  | .call n b, k => Code.memoCall n b () k fun _ => mxClassFrom b k
  | .frame i b j, k => if !loadsMxcsr i && !loadsMxcsr j then mxClassFrom b k else (none, k)
  | .icall i n b nx, k =>
    if loadsMxcsr i then (none, k) else
    let r := Code.memoCall n b () k fun _ => mxClassFrom b k
    match r.1 with
    | some x =>
      let q := mxClassFrom nx r.2
      (match q.1 with
      | some y => (if x = y then some x else none, q.2)
      | none => (none, q.2))
    | none => (none, r.2)

/-- `mxClass c`, following the code of each function `c` calls once. -/
def mxClassOnce (c : Prog isa) : Option MxC := (mxClassFrom c []).1

end RScrub

end VG.X86_64
