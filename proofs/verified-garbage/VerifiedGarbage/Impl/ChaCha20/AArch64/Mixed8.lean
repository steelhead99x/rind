module

public import VerifiedGarbage.Impl.ChaCha20.AArch64.Rows6
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed5

/-! Six row-vector blocks share execution with two integer blocks.
Each phase performs one vector double round and two integer double rounds.
Five phases finish one integer block and half of the vector rounds. With
SVE2 (`sve`), each vector XOR and rotation is one XAR. A chunk XORs the
keystream with the source at `r` (`chunkFrom`) into the destination at `x1`:
`vg_chacha20_xor` (`xor`) keeps its source in `x27` and its destination in
`x1` meanwhile (`enterFrom`), and ChaCha20-Poly1305's stitched chunks
(`Stitch.lean`) run in place (`chunk`, `r = x1`). -/

@[expose] public section

namespace VG.Impl.ChaCha20.AArch64.Mixed8
open VG VG.AArch64

inductive Op
  | vector (op : Rows6.Op)
  | scalar (op : Neon4.Op)

/-- The code of an operation; the vector ones use SVE2 if `sve`. -/
def Op.code (sve : Bool) : Op → List Instr
  | .vector op => op.codeFor sve
  | .scalar op => Mixed5.scalarCode op

def interleave : List Rows6.Op → List Neon4.Op → List Op
  | [], ss => ss.map Op.scalar
  | v :: vs, [] => Op.vector v :: interleave vs []
  | v :: vs, s :: ss => Op.vector v :: Op.scalar s :: interleave vs ss

def scheduled (sve : Bool) : List Op → Prog isa
  | [] => .block []
  | op :: ops => .seq (.block (op.code sve)) (scheduled sve ops)

def roundOps : List Op := interleave Rows6.roundOps (Mixed5.roundOps ++ Mixed5.roundOps)
def parallelRound (sve : Bool) : Prog isa := scheduled sve roundOps

/-- Keep one phase in the instruction cache; x1 is free until the scalar spill. -/
def phase (sve : Bool) (restore : Reg) : Prog isa :=
  .seq (.block [.movz .x .x1 5 0])
    (.seq (.loop (.seq (parallelRound sve) (.block [.subImm .x .x1 .x1 1])) (.nonzero .x .x1))
      (.block [.addImm .x .x1 restore 0]))

def prepare : Prog isa := .seq (.block Mixed5.saveArgs)
  (.seq (.block Rows6.setup)
    (.seq (.block (Mixed5.counter 6)) (.block VG.Impl.ChaCha20.AArch64.load)))

def spill (offset : Nat) : Prog isa :=
  .seq (.block [.addImm .x .x1 .x20 offset]) (.block VG.Impl.ChaCha20.AArch64.finish)

def second : Prog isa := .seq (spill 0)
  (.seq (.block (Mixed5.counter 1)) (.block VG.Impl.ChaCha20.AArch64.load))

/-- Row `k` of the integer blocks' keystream (spilled at `x3`) XORed with the
source (at `r`) into the destination (at `x1`). -/
def xorScalarRowFrom (r : Reg) (k : Fin 8) : List Instr :=
  [.ldrq .v30 .x3 (16 * k.val),.ldrq .v31 r (384 + 16 * k.val),
   .vop (.logic .eor .v31 .v31 .v30),.strq .v31 .x1 (384 + 16 * k.val)]

def vectorFinishFrom (r : Reg) : Prog isa := .seq (.block Mixed5.restoreArgs)
  (.seq (.block (Mixed5.counter 7 true))
    (.block (Rows6.finishFrom r)))

/-- The keystream XORed with the source (at `r`: `x1` itself, in place, or
`x27`) into the destination (at `x1`). -/
def finishFrom (r : Reg) : Prog isa :=
  .seq (vectorFinishFrom r) (.block ((List.finRange 8).flatMap (xorScalarRowFrom r)))

def chunkFrom (sve : Bool) (r : Reg) : Prog isa := .seq prepare (.seq (phase sve .x26)
  (.seq second (.seq (phase sve .x20) (.seq (spill 64) (finishFrom r)))))

def check : List Instr :=
  [.lsr .x .x5 .x2 6,.subImm .x .x5 .x5 8,.lsr .x .x5 .x5 63]

def enter : List Instr := Mixed5.enter ++ ([.strq .v8 .x3 128,.strq .v9 .x3 144] : List Instr)
def leave : List Instr := ([.ldrq .v8 .x3 128,.ldrq .v9 .x3 144] : List Instr) ++ Mixed5.leave

/-- Our caller's registers the stream's chunks use, and where they are saved
in the working space (`x3`). -/
def savedFrom : List (Reg × Nat) := [(.x20, 256), (.x19, 264), (.x26, 272), (.x27, 280)]

/-- As `enter`, with our caller's `x27` saved too, the source (`x1`) moved to
`x27` and the destination (`x4`) to `x1`, where the chunks keep them. -/
def enterFrom : List Instr :=
  savedFrom.map (fun (r, d) => .str .x r .x3 d) ++
  ([.addImm .x .x20 .x3 0, .strq .v8 .x3 128, .strq .v9 .x3 144, .addImm .x .x27 .x1 0,
    .addImm .x .x1 .x4 0] : List Instr)

/-- The destination back in `x4` and the source in `x1`, and our caller's
registers restored. -/
def leaveFrom : List Instr :=
  ([.addImm .x .x4 .x1 0, .addImm .x .x1 .x27 0, .ldrq .v8 .x3 128, .ldrq .v9 .x3 144] : List Instr) ++
  savedFrom.map (fun (r, d) => .ldr .x r .x3 d)

def next : List Instr := Mixed5.counter 8 ++
  ([.addImm .x .x1 .x1 512,.subImm .x .x2 .x2 512] : List Instr) ++ check

/-- A chunk from the source at `x27` to the destination at `x1`, both advanced. -/
def bodyFrom (sve : Bool) : Prog isa :=
  .seq (chunkFrom sve .x27) (.block (next ++ ([.addImm .x .x27 .x27 512] : List Instr)))

/-- The stream, from the source at `x1` to the destination at `x4`; its
vector rounds use SVE2 if `sve`. -/
def xor (sve : Bool) : Prog isa := .seq (.block check)
  (.seq (.ite (.nonzero .x .x5) (.block [])
    (.seq (.block enterFrom) (.seq (.loop (bodyFrom sve) (.zero .x .x5)) (.block leaveFrom))))
    (VG.Impl.ChaCha20.AArch64.Small.xor sve))

end VG.Impl.ChaCha20.AArch64.Mixed8
