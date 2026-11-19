import Cosim.Common
import VerifiedGarbage.TCB.AArch64.Print

/-!
# Cosimulating VG's AArch64 model

As for x86-64 (`Cosim/X86_64.lean`): each line of VG's code, as its assembly
file prints it, is parsed back into every `Instr` whose text (`Instr.asm`)
is exactly that line, so which instruction of the model the text means is
VG's printer's, not this parser's, which is loose. Each is then run in the
model from random states, and the runner runs its machine code from the same
states.
-/

namespace Cosim.AArch64

open VG VG.AArch64

def regs : List Reg :=
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
    .x16, .x17, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30]
def vregs : List VReg :=
  [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15,
    .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29,
    .v30, .v31]
def sizes : List Size := [.w, .x]
def arrs : List VArr := [.s4, .d2, .b16, .h8]
def bools : List Bool := [false, true]
def logicOps : List LogicOp := [.and, .orr, .eor]
def vLogicOps : List VLogicOp := [.and, .orr, .eor, .bic, .orn]
def vShiftOps : List VShiftOp := [.shl, .ushr, .sri, .sli, .sshr]
def vPermOps : List VPermOp := [.zip1, .zip2, .trn1, .trn2, .uzp1, .uzp2]
def vRevOps : List VRevOp := [.rev32b, .rev32h, .rev64b, .rev64s]
def vMulHOps : List VMulHOp := [.mul, .mla, .mls, .sqdmulh, .sqrdmulh]
def vCmpOps : List VCmpOp := [.hi, .hs]
def vSelOps : List VSelOp := [.bsl, .bit, .bif]
def sha1Ops : List Sha1Op := [.c, .p, .m]
def sm3TtOps : List Sm3TtOp := [.tt1a, .tt1b, .tt2a, .tt2b]
def condCodes : List CondCode :=
  [.eq, .ne, .hs, .lo, .mi, .pl, .vs, .vc, .hi, .ls, .ge, .lt, .gt, .le]

/-! ## Parsing -/

/-- A general-purpose register operand, `w<n>` or `x<n>`, with its size. -/
def gp (s : String) : List (Size × Reg) := do
  let sz ← sizes
  let r ← regs
  if r.name sz == s then [(sz, r)] else []

/-- The digits at the start of `s`, as a number. -/
def leadingNat (s : List Char) : Option Nat :=
  match s.takeWhile Char.isDigit with
  | [] => none
  | ds => (String.ofList ds).toNat?

/-- The vector register an operand names, whatever its form: `v<n>.<t>`,
`v<n>.<t>[i]`, `q<n>`, `s<n>`, `z<n>.s`, or the first of a table list
`{v<n>.16b, …}`. -/
def vr (s : String) : List VReg :=
  let cs := (if s.startsWith "{" then (s.drop 1).toString else s).toList
  match cs with
  | c :: rest =>
    if c ∈ ['v', 'q', 's', 'b', 'h', 'd', 'z'] then
      match leadingNat rest with
      | some n => (vregs[n]?).toList
      | none => []
    else []
  | [] => []

/-- The element index of `v<n>.<t>[i]`. -/
def ei (s : String) : List Nat :=
  match s.splitOn "[" with
  | [_, i] => (leadingNat i.toList).toList
  | _ => []

/-- `#<n>`. -/
def imm (s : String) : List Nat :=
  if s.startsWith "#" then ((s.drop 1).toString.toNat?).toList else []

/-- `<shift> #<n>`, as in `lsl #16` or `ror #7`. -/
def shifted (kw : String) (s : String) : List Nat :=
  if s.startsWith (kw ++ " ") then imm (s.drop (kw.length + 1)).toString else []

/-- `[x<n>, #<off>]`. -/
def mem (s : String) : List (Reg × Nat) :=
  if s.startsWith "[" && s.endsWith "]" then
    match fields ((s.drop 1).dropEnd 1).toString "," with
    | [b, o] => do
      let (sz, r) ← gp b
      if sz != .x then [] else (imm o).map (r, ·)
    | _ => []
  else []

/-- `[sp, #<off>]`. -/
def spMem (s : String) : List Nat :=
  if s.startsWith "[sp, " && s.endsWith "]" then imm ((s.drop 5).dropEnd 1).toString else []

/-- The number of registers of a table list `{…}`. -/
def tableLen (s : String) : Nat := (s.splitOn ",").length

/-- The operands of a line, split at the commas outside brackets and braces. -/
def operands (s : String) : List String := Id.run do
  let mut parts : List String := []
  let mut cur := ""
  let mut depth := 0
  for c in s.toList do
    if c == '[' || c == '{' then depth := depth + 1
    if c == ']' || c == '}' then depth := depth - 1
    if c == ',' && depth == 0 then
      parts := parts ++ [cur.trimAscii.toString]
      cur := ""
    else
      cur := cur.push c
  return parts ++ [cur.trimAscii.toString]

/-- The placeholder static of a table instruction: the case gives its
address and words. -/
def tbl : String := "T"

/-- Every vector instruction of `ops`' operands, generously: the printer's
text decides which is meant. -/
def vops (ops : List String) : List VOp :=
  match ops with
  | [a0, a1] =>
    (do let d ← vr a0; let n ← vr a1
        [VOp.mov d n, .not d n, .aese d n, .aesd d n, .aesmc d n, .aesimc d n, .sha1h d n,
          .sha1su1 d n, .sha256su0 d n, .sha512su0 d n, .sm4e d n] ++
        vRevOps.map (.rev · d n) ++
        arrs.flatMap (fun a => [.addv a d n, .uaddlv a d n]) ++
        (do let i ← ei a1; [.dupS d n i] ++ arrs.map (.dupE · d n i)) ++
        (do let i ← ei a0; let j ← ei a1; arrs.map (fun a => .insE a d i n j))) ++
    (do let d ← vr a0; let (_, r) ← gp a1
        arrs.map (.dup · d r) ++ (do let i ← ei a0; arrs.map (.ins · d i r))) ++
    (do let d ← vr a0; if a1 == "#0" then [.movi0 d] else [])
  | [a0, a1, a2] =>
    (do let d ← vr a0; let n ← vr a1; let m ← vr a2
        if a1.startsWith "{" then
          [.tbl d n m, .tblN false (tableLen a1) d n m, .tblN true (tableLen a1) d n m]
        else
          arrs.flatMap (fun a =>
            [.cmeq a d n m, .add a d n m, .sub a d n m] ++ vCmpOps.map (.cmp · a d n m) ++
            vPermOps.map (.perm · a d n m)) ++
          vSelOps.map (.bsel · d n m) ++ vLogicOps.map (.logic · d n m) ++
          bools.flatMap (fun hi =>
            [.umull hi d n m, .umlal hi d n m, .umullH hi d n m, .umlalH hi d n m,
              .pmull hi d n m, .pmull8 hi d n m]) ++
          [.mul d n m, .mla d n m, .mls d n m, .sqdmulh d n m, .umin d n m] ++
          vMulHOps.map (.mulH · d n m) ++
          (do let i ← ei a2; vMulHOps.map (.mulHE · d n m i) ++ sm3TtOps.map (.sm3tt · d n m i)) ++
          sha1Ops.map (.sha1 · d n m) ++
          [.sha1su0 d n m, .sha256h d n m, .sha256h2 d n m, .sha256su1 d n m, .sha512h d n m,
            .sha512h2 d n m, .sha512su1 d n m, .sm4ekey d n m, .sm3partw1 d n m,
            .sm3partw2 d n m, .rax1 d n m]) ++
    (do let d ← vr a0; let n ← vr a1; let sh ← imm a2
        arrs.flatMap fun a => vShiftOps.map (.shift · a d n sh))
  | [a0, a1, a2, a3] =>
    (do let d ← vr a0; let n ← vr a1; let m ← vr a2
        (do let k ← imm a3; [.ext d n m k, .xar d n m k, .xarS d m k]) ++
        (do let a ← vr a3; [.sm3ss1 d n m a, .eor3 d n m a, .bcax d n m a]))
  | _ => []

/-- Every instruction one line of text can be, that `Instr.asm` prints as
it. -/
def single (line : String) : List Instr := Id.run do
  let rest := " ".intercalate ((line.splitOn " ").drop 1)
  let a := if rest == "" then [] else operands rest
  let mut c : List Instr := (vops a).map .vop
  match a with
  | [] =>
    c := c ++ [.barrier .isb, .barrier .sb]
  | [o] =>
    c := c ++ (do let (_, r) ← gp o; [.blr r])
    c := c ++ (if o == "sy" then [.barrier .dsbSy] else [])
    c := c ++ ((o.toNat?).toList.map .align)
  | [a0, a1] =>
    c := c ++ (do let (sz, d) ← gp a0; let (_, n) ← gp a1
                  [.tst sz d n, .clz sz d n, .rbit sz d n, .rev32 d n, .rev d n])
    c := c ++ (do let (sz, t) ← gp a0; let (n, off) ← mem a1
                  [.ldr sz t n off, .str sz t n off, .ldrb t n off, .strb t n off,
                    .ldrTbl sz t n off tbl []])
    c := c ++ (do let t ← vr a0; let (n, off) ← mem a1; [.ldrq t n off, .strq t n off, .ldrqTbl t n off tbl []])
    c := c ++ (do let (_, t) ← gp a0; let off ← spMem a1; [.ldrSp t off, .strSp t off])
    c := c ++ (do let (_, t) ← gp a0; if a1 == "[sp, #-16]!" then [.push t] else [])
    c := c ++ (do let (sz, d) ← gp a0; let n ← vr a1; let i ← ei a1; [.umov sz d n i])
    c := c ++ (do let (_, t) ← gp a0; if a1 == "DIT" then [.mrsDit t] else [])
    c := c ++ (if a0 == "DIT" then (imm a1).filterMap fun n =>
                  if n == 0 then some (.msrDitImm false) else if n == 1 then some (.msrDitImm true) else none
                else [])
  | [a0, a1, a2] =>
    c := c ++ (do let (sz, d) ← gp a0; let (_, n) ← gp a1; let (_, k) ← gp a2
                  [.add sz d n k, .sub sz d n k, .adds sz d n k, .adcs sz d n k, .subs sz d n k,
                    .sbcs sz d n k, .adc sz d n k, .sbc sz d n k, .mul sz d n k, .umulh d n k,
                    .umull d n k] ++ logicOps.map (.logic · sz d n k))
    c := c ++ (do let (sz, d) ← gp a0; let (_, n) ← gp a1; let i ← imm a2
                  [.addImm sz d n i, .subImm sz d n i, .ror sz d n i, .lsr sz d n i, .lsl sz d n i])
    c := c ++ (do let (sz, d) ← gp a0; let i ← imm a1; let sh ← shifted "lsl" a2
                  if sh % 16 != 0 || i ≥ 65536 then [] else
                  [.movz sz d (BitVec.ofNat 16 i) (sh / 16), .movk sz d (BitVec.ofNat 16 i) (sh / 16)])
    c := c ++ (do let (_, d) ← gp a0; let i ← imm a2; if a1 == "sp" then [.addSp d i] else [])
    c := c ++ (do let i ← imm a2; if a0 == "sp" && a1 == "sp" then [.alloc i, .free i] else [])
    c := c ++ (do let (_, t1) ← gp a0; let (_, t2) ← gp a1; let (n, off) ← mem a2
                  [.ldp t1 t2 n off, .stp t1 t2 n off])
    c := c ++ (do let (_, t) ← gp a0; if a1 == "[sp]" && a2 == "#16" then [.pop t] else [])
  | [a0, a1, a2, a3] =>
    c := c ++ (do let (sz, d) ← gp a0; let (_, n) ← gp a1; let (_, k) ← gp a2
                  (do let cc ← condCodes.filter (·.name == a3)
                      [.csel sz d n k, .cselc sz d n k cc, .csneg sz d n k cc]) ++
                  (do let sh ← shifted "ror" a3
                      logicOps.map (.logicRor · sz d n k sh) ++ [.bicRor sz d n k sh]) ++
                  (do let i ← imm a3; [.extr sz d n k i]) ++
                  (do let (_, r) ← gp a3; [.madd sz d n k r, .umaddl d n k r]))
    c := c ++ (do let (sz, n) ← gp a0; let i ← imm a1; let f ← imm a2
                  let cc ← condCodes.filter (·.name == a3); [.ccmp sz n i f cc])
  | _ => pure ()
  return c

/-- The instructions a group of lines can be. Every instruction of the
model prints as one line, but for `adrSym`, whose lines name a static the
linker places and are not cosimulated. -/
def candidates (lines : List String) : List Instr :=
  match lines with
  | [l] => (single l).filter (·.asm == lines)
  | _ => []

/-! ## States -/

/-- What the runner loads and stores: `x0`–`x30` by number (`x18` and `x29`,
which the model does not have, are left as they were), `sp`, NZCV (bit 3 N,
2 Z, 1 C, 0 V: the register's bits 31–28), PSTATE.DIT, `v0`–`v31`, and the
data. -/
structure Img where
  gpr : Array (BitVec 64)
  sp : BitVec 64
  nzcv : Nat
  dit : Bool
  v : Array (BitVec 128)
  data : ByteArray

def stateLen : Nat := 31 * 8 + 8 + 4 + 4 + 32 * 16 + dataLen

def Img.encode (i : Img) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity stateLen
  for r in i.gpr do
    b := pushBV b r
  b := pushBV b i.sp
  b := pushLE b i.nzcv 4
  b := pushLE b (if i.dit then 1 else 0) 4
  for r in i.v do
    b := pushBV b r
  return b ++ i.data

def window : Region := ⟨BitVec.ofNat 64 windowBase, windowLen⟩

/-- The model's state of `i`, which may access only the window. A call's
(`ret`) unknowns are what the CPU leaves: the return address `ret`, after
the call instruction, and in `x16`, `x17` and NZCV their values before the
call, which no veneer changes here (`call`'s order: C, N, Z, V from bit 0).
Any other case's are zero, so a frame's release (`lose`) keeps every byte
of the frame, as the CPU does with no signal handler between. -/
def Img.state (i : Img) (ret : Option Nat := none) : State :=
  let data := i.data
  let flags := ((i.nzcv >>> 1) &&& 1) + 2 * ((i.nzcv >>> 3) &&& 1) + 4 * ((i.nzcv >>> 2) &&& 1) +
    8 * (i.nzcv &&& 1)
  { gpr := fun r => i.gpr[r.index]!
    sp := i.sp
    nf := i.nzcv.testBit 3, zf := i.nzcv.testBit 2, c := i.nzcv.testBit 1, vf := i.nzcv.testBit 0
    dit := i.dit
    v := fun r => i.v[r.index]!
    mem := fun a =>
      let o := (a - BitVec.ofNat 64 dataBase).toNat
      if o < dataLen then BitVec.ofNat 8 (data.get! o).toNat else 0
    rd := []
    wr := [window]
    unknowns := fun n => match ret, n with
      | some ret, 0 => BitVec.ofNat 64 ret
      | some _, 1 => i.gpr[16]!
      | some _, 2 => i.gpr[17]!
      | some _, 3 => BitVec.ofNat 64 flags
      | _, _ => 0
    syms := fun _ => 0 }

/-- The image of the model's state `s`, which ran from `start`. -/
def ofState (start : Img) (s : State) : Img :=
  let data := Id.run do
    let mut d := start.data
    for o in [0:dataLen] do
      d := d.set! o (s.mem (BitVec.ofNat 64 (dataBase + o))).toNat.toUInt8
    return d
  { gpr := Id.run do
      let mut g := start.gpr
      for r in regs do
        g := g.set! r.index (s.gpr r)
      return g
    sp := s.sp
    nzcv := (if s.nf then 8 else 0) + (if s.zf then 4 else 0) + (if s.c then 2 else 0) +
      (if s.vf then 1 else 0)
    dit := s.dit
    v := vregs.toArray.map s.v
    data }

/-- A stack pointer: 16-byte aligned, as AAPCS64 keeps it and Linux checks
at every access through it (SCTLR_EL1.SA0). -/
def spIn (lo hi : Nat) : Gen Nat := do
  let lo := (lo + 15) / 16 * 16
  return lo + 16 * (← below ((hi - lo) / 16 + 1))

def randomImg : Gen Img := do
  let mut gpr := #[]
  for _ in [0:31] do
    gpr := gpr.push (← val64)
  let mut v := #[]
  for _ in [0:32] do
    v := v.push (← bits 128)
  return { gpr, sp := BitVec.ofNat 64 (← spIn (windowBase + 256) (windowBase + windowLen - 256))
           nzcv := ← below 16, dit := ← bool, v, data := ← bytes dataLen }

def Img.setReg (i : Img) (r : Reg) (v : Nat) : Img :=
  { i with gpr := i.gpr.set! r.index (BitVec.ofNat 64 v) }

def Img.poke (i : Img) (a : Nat) (v : Nat) (n : Nat) : Img := Id.run do
  let mut d := i.data
  let mut v := v
  for j in [0:n] do
    d := d.set! (a - dataBase + j) (v % 256).toUInt8
    v := v / 256
  return { i with data := d }

/-- The base register and offset of an instruction's access through a
register, and its size. -/
def memOp : Instr → Option (Reg × Nat × Nat)
  | .ldr sz _ n off | .str sz _ n off => some (n, off, sz.bytes)
  | .ldrb _ n off | .strb _ n off => some (n, off, 1)
  | .ldp _ _ n off | .stp _ _ n off => some (n, off, 16)
  | .ldrq _ n off | .strq _ n off => some (n, off, 16)
  | _ => none

/-- The table of a table instruction: its base register, offset, and how
many words from the one at the offset it reads. -/
def tblOf : Instr → Option (Reg × Nat × Nat)
  | .ldrqTbl _ n off .. => some (n, off, 2)
  | .ldrTbl _ _ n off .. => some (n, off, 1)
  | _ => none

/-- Whether a table instruction's offset is one its load encodes, which the
model requires of a table load: for `ldrqTbl` a multiple of 16 below 65536,
for `ldrTbl` a multiple of the access size below 4096 times it (DDI 0487
C7.2 and C6.2, the scaled 12-bit immediate). The text of a load at any other
offset is not a table load VG's code can hold, so that reading of the text
has no case. -/
def tblEncodes : Instr → Bool
  | .ldrqTbl _ _ off .. => off % 16 == 0 && off < 65536
  | .ldrTbl sz _ _ off .. => off % sz.bytes == 0 && off < 4096 * sz.bytes
  | _ => true

def withWords (i : Instr) (ws : List (BitVec 64)) : Instr :=
  match i with
  | .ldrqTbl t n off name _ => .ldrqTbl t n off name ws
  | .ldrTbl sz t n off name _ => .ldrTbl sz t n off name ws
  | i => i

/-- The words of a table instruction's static, from `n`: random, and in
memory where the CPU reads them, so it reads what the model does. -/
def placeTbl (img : Img) (n : Reg) (off need : Nat) : Gen (Img × List (BitVec 64)) := do
  let a := windowBase + 8 * (← below ((windowLen - 64) / 8))
  let words := off / 8 + need + (← below 4)
  let mut ws := #[]
  for _ in [0:words] do
    ws := ws.push (← val64)
  let mut img := img
  for j in [0:need] do
    img := img.poke (a + 8 * j) ws[off / 8 + j]!.toNat 8
  -- `n` wraps, as an address does, if the offset is past the window's start.
  return (img.setReg n (((a : Int) - 8 * (off / 8 : Nat)) % 2 ^ 64).toNat, ws.toList)

/-- What the model says `i` leaves, run from `s` (the frame instructions by
the push and pop of a frame, which also check the frame's bookkeeping). A
frame's release takes its unknowns all zero, the outcome where every
released byte keeps its value (`lose`), as each does on the CPU, where nothing
else writes memory between two instructions; a `free` may release bytes
outside the window. -/
def run (i : Instr) (s : State) : Option State :=
  match i with
  | .push _ | .alloc _ => push i s
  | .pop _ => let s₁ := { s with unknowns := fun _ => 0, wr := ⟨s.sp, 16⟩ :: s.wr }; pop i s₁ s₁
  | .free n => let s₁ := { s with unknowns := fun _ => 0, wr := ⟨s.sp, n⟩ :: s.wr }; pop i s₁ s₁
  | _ => exec i s

/-- A case of the straight-line instruction `i`: a start image and the
model's end image. Retries a state the model faults in. -/
def insnCase (i : Instr) : Gen (Option (Instr × Img × Img)) := do
  for _ in [0:32] do
    let mut img ← randomImg
    let mut i := i
    match tblOf i with
    | some (n, off, need) =>
      let (img', ws) ← placeTbl img n off need
      img := img'
      i := withWords i ws
    | none => pure ()
    if let some (n, off, len) := memOp i then
      let a := windowBase + (← below (windowLen - len + 1))
      img := img.setReg n (((a : Int) - off) % 2 ^ 64).toNat
    -- A frame's push from the top of the window, its pop from the bottom,
    -- the release of a frame to the window's bottom, and an access through
    -- `sp` within it. So `sp` ends at most 4096 bytes below the window, as
    -- the runner needs (`SCRATCH`).
    match i with
    | .free k => img := { img with sp := BitVec.ofNat 64 (← spIn (windowBase - k) (windowBase + 256 - k)) }
    | .push _ => img := { img with sp := BitVec.ofNat 64 (← spIn (windowBase + windowLen - 64) (windowBase + windowLen)) }
    | .pop _ => img := { img with sp := BitVec.ofNat 64 (← spIn windowBase (windowBase + 64)) }
    | .ldrSp _ off | .strSp _ off =>
      img := { img with sp := BitVec.ofNat 64 (← spIn (windowBase - off) (windowBase + windowLen - 8 - off)) }
    | _ => pure ()
    let s := match tblOf i with
      | some (n, _, _) => { img.state with syms := fun _ => img.state.gpr n }
      | none => img.state
    if let some s' := run i s then
      return some (i, img, ofState img s')
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
  let s := img.state (some (insnAddr + code.size))
  if let some r := r then
    if icall (.blr r) s != some (BitVec.ofNat 64 targetAddr) then return none
  let some s₁ := call s | return none
  let some s' := ret s₁ s₁ | return none
  return some (img, ofState img s')

def word (w : Nat) : ByteArray := pushU32 .empty w

/-- `cbz`/`cbnz <Rt>, targetAddr` from `insnAddr` (DDI 0487 C6.2, "CBZ",
"CBNZ": `sf 011010 op imm19 Rt`, the offset `imm19 * 4`). -/
def cb (c : Cond) : ByteArray :=
  let (sz, op, r) := match c with
    | .zero sz r => (sz, 0, r)
    | .nonzero sz r => (sz, 1, r)
  let sf := if sz == .x then 1 else 0
  let imm19 := (targetAddr - insnAddr) / 4
  word (sf <<< 31 ||| 0b011010 <<< 25 ||| op <<< 24 ||| imm19 <<< 5 ||| r.index)

/-- `bl targetAddr` from `insnAddr` (DDI 0487 C6.2, "BL": `1 00101 imm26`). -/
def bl : ByteArray := word (0x94000000 ||| (targetAddr - insnAddr) / 4)

def caseBytes (start out : Img) (marker : Bool) : ByteArray :=
  (start.encode ++ out.encode).push (if marker then 1 else 0) |>.push 15

/-- The branch condition of `cbz`/`cbnz <r>, <label>`. -/
def cond (l : String) : List Cond :=
  match l.splitOn " " with
  | [m, r, _] => do
    let (sz, r) ← gp (r.dropEnd 1).toString
    if m == "cbz" then [.zero sz r] else if m == "cbnz" then [.nonzero sz r] else []
  | _ => []

/-- The blocks of one group of lines of VG's code, with the CPU features
each needs, `n` cases each; or why there are none. -/
def blocks (kind : String) (lines : List String) (code : ByteArray) (n : Nat) :
    Gen (Except String (List (Block × List String))) := do
  let text := "; ".intercalate lines
  match kind, lines with
  | "branch", [l] =>
    match cond l with
    | [c] =>
      let mut cases := #[]
      for _ in [0:n] do
        let some (img, taken) ← branchCase c | return .error s!"{text}: the model's condition is undefined"
        cases := cases.push (caseBytes img img taken)
      let shown := " ".intercalate ((l.splitOn " ").take 2)
      return .ok [({ text := shown, kind := .branch, code := cb c, cases }, [])]
    | _ => return .error s!"{text}: not a branch the model has"
  | "call", [_] =>
    let mut cases := #[]
    for _ in [0:n] do
      let some (img, out) ← callCase bl none | return .error s!"{text}: the model's call faults"
      cases := cases.push (caseBytes img out false)
    return .ok [({ text := "bl (direct); ret", kind := .call, code := bl, cases }, [])]
  | "insn", _ =>
    let cs := candidates lines
    if cs.isEmpty then return .error s!"{text}: no instruction of the model prints as this"
    let mut out := []
    for i in cs do
      if let .blr r := i then
        let mut cases := #[]
        for _ in [0:n] do
          let some (img, o) ← callCase code r | return .error s!"{text}: the model's call faults"
          cases := cases.push (caseBytes img o false)
        out := out ++ [({ text := text ++ "; ret", kind := .call, code, cases }, [])]
        continue
      if !tblEncodes i then continue
      let mut cases := #[]
      for _ in [0:n] do
        let some (_, img, o) ← insnCase i
          | return .error s!"{text}: the model faults in every state tried ({repr i})"
        cases := cases.push (caseBytes img o false)
      out := out ++ [({ text, kind := .insn, code, cases }, i.requires)]
    if out.isEmpty then return .error s!"{text}: the model faults in every state tried"
    return .ok out
  | _, _ => return .error s!"{text}: unknown kind {kind}"

end Cosim.AArch64
