module

public import VerifiedGarbage.Impl.ChaCha20.AArch64.Small

/-!
# Five-block ChaCha20 with NEON and integer rounds

Four independent blocks occupy NEON lanes and one uses the integer registers.
Integer and vector arithmetic operations alternate. x19, x20 and x26 are saved in the
existing 320-byte stream scratch space; x20 retains its address while the
scalar state occupies x2–x17. Public length/data stay in x19/x26. No new stack or CPU feature is required.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.AArch64.Mixed5
open VG VG.AArch64

def check : List Instr :=
  [.lsr .x .x5 .x2 6, .subImm .x .x5 .x5 5, .lsr .x .x5 .x5 63]

def enter : List Instr :=
  [.str .x .x20 .x3 256, .str .x .x19 .x3 264, .str .x .x26 .x3 272, .addImm .x .x20 .x3 0]

def leave : List Instr := [.ldr .x .x20 .x3 256, .ldr .x .x19 .x3 264, .ldr .x .x26 .x3 272]

def saveArgs : List Instr := [.addImm .x .x19 .x2 0, .addImm .x .x26 .x1 0]

def counter (n : Nat) (subtract : Bool := false) : List Instr :=
  ([.ldr .w .x4 .x0 48] : List Instr) ++
  (if subtract then [.subImm .w .x4 .x4 n] else [.addImm .w .x4 .x4 n]) ++
  ([.str .w .x4 .x0 48] : List Instr)

/-- The scalar block follows the same four-quarter schedule as the vector
blocks, exposing independent dependency chains in both register banks. -/
def scalarCode : Neon4.Op → List Instr
  | .add d a b => [.add .w (VG.Impl.ChaCha20.AArch64.wreg d)
      (VG.Impl.ChaCha20.AArch64.wreg a) (VG.Impl.ChaCha20.AArch64.wreg b)]
  | .xorRol d a b n =>
      [.logic .eor .w (VG.Impl.ChaCha20.AArch64.wreg d)
        (VG.Impl.ChaCha20.AArch64.wreg a) (VG.Impl.ChaCha20.AArch64.wreg b),
       .ror .w (VG.Impl.ChaCha20.AArch64.wreg d) (VG.Impl.ChaCha20.AArch64.wreg d) (32 - n)]

/-- The vector operations use SVE2 if `sve`. -/
def scheduled (sve : Bool := false) : List Neon4.Op → Prog isa
  | [] => .block []
  | op :: ops => .seq (.block (op.codeFor sve)) (.seq (.block (scalarCode op)) (scheduled sve ops))

def roundOps : List Neon4.Op := Neon4.quarters Neon4.cols ++ Neon4.quarters Neon4.diags

def parallelRound (sve : Bool := false) : Prog isa := scheduled sve roundOps

def rounds (sve : Bool := false) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds sve n) (parallelRound sve)

def restoreArgs : List Instr :=
  [.addImm .x .x1 .x26 0, .addImm .x .x2 .x19 0, .addImm .x .x3 .x20 0]

def xorLastRow (r : Fin 4) : List Instr :=
  ([.ldrq (VG.Impl.ChaCha20.AArch64.Neon4.vreg
    (VG.Impl.ChaCha20.AArch64.Neon4.rowWord r 0)) .x3 (16 * r)] : List Instr) ++
    VG.Impl.ChaCha20.AArch64.Neon4.xorRow r 0

def prepare : Prog isa :=
  .seq (.block saveArgs) (.seq (.block VG.Impl.ChaCha20.AArch64.Neon4.setup)
    (.seq (.block (counter 4)) (.block VG.Impl.ChaCha20.AArch64.load)))

def spill : Prog isa := .seq (.block [.addImm .x .x1 .x20 0])
  (.block VG.Impl.ChaCha20.AArch64.finish)

def finish : Prog isa := .seq (.block restoreArgs)
  (.seq (.block (counter 4 true)) (.block VG.Impl.ChaCha20.AArch64.Neon4.finish))

def last : Prog isa := .seq (.block [.addImm .x .x1 .x1 256])
  (.seq (.block ((List.finRange 4).flatMap xorLastRow)) (.block [.subImm .x .x1 .x1 256]))

/-- One chunk of five blocks; its vector rounds use SVE2 if `sve`. -/
def chunk (sve : Bool := false) : Prog isa :=
  .seq prepare (.seq (rounds sve 10) (.seq spill (.seq finish last)))

def next : List Instr := counter 5 ++
  ([.addImm .x .x1 .x1 320, .subImm .x .x2 .x2 320] : List Instr) ++ check

def body : Prog isa := .seq (chunk false) (.block next)

/-- The stream in place (`Small.xor`'s destination, `x4`, set to `x1`). -/
def xor : Prog isa :=
  .seq (.block check)
  (.seq (.ite (.nonzero .x .x5) (.block [])
    (.seq (.block enter) (.seq (.loop body (.zero .x .x5)) (.block leave))))
    (.seq (.block [.addImm .x .x4 .x1 0]) VG.Impl.ChaCha20.AArch64.Small.xor))

end VG.Impl.ChaCha20.AArch64.Mixed5
