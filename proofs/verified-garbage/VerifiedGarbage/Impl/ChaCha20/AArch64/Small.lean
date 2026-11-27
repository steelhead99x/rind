module

public import VerifiedGarbage.Impl.ChaCha20.AArch64.Neon4

/-! Vector tails write only the two or three whole blocks available, from the
source at `x1` to the destination at `x6`. -/

@[expose] public section

namespace VG.Impl.ChaCha20.AArch64.Small
open VG VG.AArch64

def lanes (n : Nat) : List (Fin 4) := (List.finRange 4).filter (fun j => j.val < n)

/-- The first `n` blocks' keystream XORed with the source (at `x1`) into the
destination (at `x6`). -/
def finish (n : Nat) : List Instr :=
  (List.finRange 16).flatMap Neon4.addWord ++
    (List.finRange 4).flatMap (Neon4.finishRowForTo .x6 (lanes n))

def chunk (n : Nat) (sve : Bool := false) : Prog isa :=
  .seq (.block Neon4.setup) (.seq (Neon4.roundLoop sve) (.block (finish n)))

/-- The counter, the source and the destination advanced past `n` blocks; the
destination is also left in `x4`. -/
def next (n : Nat) : List Instr :=
  [.ldr .w .x4 .x0 48, .addImm .w .x4 .x4 n, .str .w .x4 .x0 48,
   .addImm .x .x1 .x1 (64*n), .addImm .x .x6 .x6 (64*n), .subImm .x .x2 .x2 (64*n), Xor.mov .x4 .x6]

def step (n : Nat) (sve : Bool := false) : Prog isa := .seq (chunk n sve) (.block (next n))

/-- Fewer than 256 bytes: two or three blocks with the vector kernel, the
destination (`x4`) kept in `x6`, and at most 127 bytes left to the scalar
stream. -/
def short (sve : Bool := false) : Prog isa :=
  .seq (.block [.lsr .x .x5 .x2 7, Xor.mov .x6 .x4])
  (.ite (.zero .x .x5) Xor.xor
    (.seq (.seq (.block [.lsr .x .x5 .x2 6, .subImm .x .x5 .x5 3, .lsr .x .x5 .x5 63])
      (.ite (.nonzero .x .x5) (step 2 sve) (step 3 sve))) Xor.xor))

/-- The whole 256-byte chunks with the four-block kernel (`Neon4.body`), then
the fewer than 256 bytes left with `short`, whose two- and three-block
steps leave at most 63 bytes to the scalar stream; the rounds use SVE2's XAR
if `sve`. The destination (`x4` on entry) is kept in `x6`, which the vector
code does not otherwise use, and in `x4` after each chunk. -/
def xor (sve : Bool := false) : Prog isa :=
  .seq (.block [.lsr .x .x5 .x2 8, Xor.mov .x6 .x4])
    (.seq (.ite (.zero .x .x5) (.block []) (.loop (Neon4.body sve) (.nonzero .x .x5))) (short sve))

end VG.Impl.ChaCha20.AArch64.Small
