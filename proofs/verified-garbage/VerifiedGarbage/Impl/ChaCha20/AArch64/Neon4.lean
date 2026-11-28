module

public import VerifiedGarbage.Impl.ChaCha20.AArch64.Xor

/-!
# Four-block ChaCha20 with ARM64 NEON

Each vector holds one word from four independent blocks. The four column
quarter rounds are scheduled together, as are the four diagonal quarter
rounds. Only caller-saved vector registers are used. The bulk stream keeps
the keystream in registers through the input XOR, from the source at `x1` to
the destination at `x6` (`x4` is the kernel's scratch register).
-/

@[expose] public section

namespace VG.Impl.ChaCha20.AArch64.Neon4

open VG.AArch64

def vreg (k : Fin 16) : VReg :=
  #[.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7,
    .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23][k]

/-- Byte indices for rotating each 32-bit word left by eight bits. -/
def rol8Table : BitVec 128 := 0x0e0d0c0f0a09080b0605040702010003

def setupTable : List Instr :=
  [.movz .x .x4 0x0003 0, .movk .x .x4 0x0201 1,
   .movk .x .x4 0x0407 2, .movk .x .x4 0x0605 3,
   .vop (.dup .d2 .v30 .x4),
   .movz .x .x4 0x080b 0, .movk .x .x4 0x0a09 1,
   .movk .x .x4 0x0c0f 2, .movk .x .x4 0x0e0d 3,
   .vop (.ins .d2 .v30 1 .x4)]

/-- The operations of the round scheduler, each acting on all four blocks. -/
inductive Op
  | add (d a b : Fin 16)
  | xorRol (d a b : Fin 16) (n : Fin 32)

def Op.code : Op → List Instr
  | .add d a b => [.vop (.add .s4 (vreg d) (vreg a) (vreg b))]
  | .xorRol d a b n =>
    ([.vop (.logic .eor .v31 (vreg a) (vreg b))] : List Instr) ++
    if n.val = 16 then [.vop (.rev .rev32h (vreg d) .v31)]
    else if n.val = 8 then [.vop (.tbl (vreg d) .v31 .v30)]
    else [.vop (.shift .ushr .s4 (vreg d) .v31 (32 - n)),
      .vop (.shift .sli .s4 (vreg d) .v31 n)]

/-- The code of `op`, using SVE2 if `sve`: an `xorRol` whose destination is
its first source, by a nonzero rotation, is then one XAR, `ROR(d XOR b, 32 -
n)`, which is `ROL(d XOR b, n)` (as `Rows6.Op.codeFor`). -/
def Op.codeFor (sve : Bool) (op : Op) : List Instr :=
  match sve, op with
  | true, .xorRol d a b n =>
    if d = a ∧ 0 < n.val then [.vop (.xarS (vreg d) (vreg b) (32 - n.val))] else op.code
  | _, _ => op.code

def cols : List (Fin 16 × Fin 16 × Fin 16 × Fin 16) :=
  [(0,4,8,12), (1,5,9,13), (2,6,10,14), (3,7,11,15)]
def diags : List (Fin 16 × Fin 16 × Fin 16 × Fin 16) :=
  [(0,5,10,15), (1,6,11,12), (2,7,8,13), (3,4,9,14)]

def half (qs : List (Fin 16 × Fin 16 × Fin 16 × Fin 16)) (r₁ r₂ : Fin 32) : List Op :=
  qs.map (fun (a,b,_,_) => .add a a b) ++
  qs.map (fun (a,_,_,d) => .xorRol d d a r₁) ++
  qs.map (fun (_,_,c,d) => .add c c d) ++
  qs.map (fun (_,b,c,_) => .xorRol b b c r₂)

def quarters (qs : List (Fin 16 × Fin 16 × Fin 16 × Fin 16)) : List Op :=
  half qs 16 12 ++ half qs 8 7

/-- A double round, with SVE2's XAR for the rotations if `sve` (`Op.codeFor`). -/
def doubleRound (sve : Bool := false) : List Instr :=
  (quarters cols ++ quarters diags).flatMap (Op.codeFor sve)

/-- Keep the double-round instruction body compact and repeat it ten times. -/
def roundLoop (sve : Bool := false) : Prog isa :=
  .seq (.block [.movz .x .x4 10 0])
    (.loop (.seq (.block (doubleRound sve)) (.block [.subImm .x .x4 .x4 1])) (.nonzero .x .x4))

/-- Broadcast an input word; word 12 instead has consecutive counters. -/
def inputWordInto (k : Fin 16) (d : VReg) : List Instr :=
  ([.ldr .w .x4 .x0 (4 * k), .vop (.dup .s4 d .x4)] : List Instr) ++
  if k = 12 then
    [.addImm .w .x4 .x4 1, .vop (.ins .s4 d 1 .x4),
     .addImm .w .x4 .x4 1, .vop (.ins .s4 d 2 .x4),
     .addImm .w .x4 .x4 1, .vop (.ins .s4 d 3 .x4)]
  else []

def inputWord (k : Fin 16) : List Instr := inputWordInto k .v31

def setupWord (k : Fin 16) : List Instr := inputWordInto k (vreg k)
def setup : List Instr := (List.finRange 16).flatMap setupWord ++ setupTable

def addWord (k : Fin 16) : List Instr :=
  inputWord k ++ ([.vop (.add .s4 (vreg k) (vreg k) .v31)] : List Instr)

/-- Transpose four words from four blocks into four contiguous output rows. -/
def transposePrep (a b c d : VReg) : List Instr :=
  [.vop (.perm .zip1 .s4 .v24 a b), .vop (.perm .zip2 .s4 .v25 a b),
   .vop (.perm .zip1 .s4 .v26 c d), .vop (.perm .zip2 .s4 .v27 c d)]

def transposeEnd (a b c d : VReg) : List Instr :=
  [.vop (.perm .zip1 .d2 a .v24 .v26), .vop (.perm .zip2 .d2 b .v24 .v26),
   .vop (.perm .zip1 .d2 c .v25 .v27), .vop (.perm .zip2 .d2 d .v25 .v27)]

def transpose (a b c d : VReg) : List Instr :=
  transposePrep a b c d ++ transposeEnd a b c d

def rowWord (r i : Fin 4) : Fin 16 := ⟨4 * r + i, by omega⟩

/-- Row `r` of block `j` of the source (at `x1`) XORed with the keystream
into the destination (at `d`), the source's loaded before the destination's
is stored. -/
def xorRowTo (d : Reg) (r j : Fin 4) : List Instr :=
  [.ldrq .v31 .x1 (64 * j + 16 * r),
   .vop (.logic .eor .v31 .v31 (vreg (rowWord r j))),
   .strq .v31 d (64 * j + 16 * r)]

/-- In place, at `x1`. -/
def xorRow (r j : Fin 4) : List Instr := xorRowTo .x1 r j

def finishRowForTo (d : Reg) (js : List (Fin 4)) (r : Fin 4) : List Instr :=
  transpose (vreg (rowWord r 0)) (vreg (rowWord r 1))
    (vreg (rowWord r 2)) (vreg (rowWord r 3)) ++
  js.flatMap (xorRowTo d r)

def finishRowFor (js : List (Fin 4)) (r : Fin 4) : List Instr := finishRowForTo .x1 js r

def finishRowTo (d : Reg) (r : Fin 4) : List Instr := finishRowForTo d (List.finRange 4) r

def finishRow (r : Fin 4) : List Instr := finishRowTo .x1 r

/-- The keystream of the four blocks, XORed with the source (at `x1`) into the
destination (at `d`). -/
def finishTo (d : Reg) : List Instr :=
  (List.finRange 16).flatMap addWord ++ (List.finRange 4).flatMap (finishRowTo d)

def finish : List Instr := finishTo .x1

/-- A chunk, from the source at `x1` to the destination at `x6`. -/
def chunk (sve : Bool := false) : Prog isa :=
  .seq (.block setup) (.seq (roundLoop sve) (.block (finishTo .x6)))

/-- Advance four counters and one 256-byte chunk of the source and the
destination, which is also left in `x4`; x5 tests for another chunk. -/
def next : List Instr :=
  [.ldr .w .x4 .x0 48, .addImm .w .x4 .x4 4, .str .w .x4 .x0 48,
   .addImm .x .x1 .x1 256, .addImm .x .x6 .x6 256, .subImm .x .x2 .x2 256, .lsr .x .x5 .x2 8,
   VG.Impl.ChaCha20.AArch64.Xor.mov .x4 .x6]

def body (sve : Bool := false) : Prog isa := .seq (chunk sve) (.block next)

/-- Short inputs and the remaining bytes use the scalar stream implementation;
the destination is kept in `x6` meanwhile. -/
def xor : Prog isa :=
  .seq (.block [.lsr .x .x5 .x2 8, VG.Impl.ChaCha20.AArch64.Xor.mov .x6 .x4])
    (.seq (.ite (.zero .x .x5) (.block []) (.loop body (.nonzero .x .x5)))
      VG.Impl.ChaCha20.AArch64.Xor.xor)

end VG.Impl.ChaCha20.AArch64.Neon4
