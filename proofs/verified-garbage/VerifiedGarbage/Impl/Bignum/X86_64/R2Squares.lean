module

public import VerifiedGarbage.Impl.Bignum.X86_64

/-! # Counted squarings of R² setup's accumulator -/

@[expose] public section
namespace VG.Impl.Bignum.X86_64.Public.R2Squares
open VG VG.X86_64

def init (n : Nat) : List Instr :=
  [.mov32 .rax (.imm (BitVec.ofNat 32 (n + 1))), .store (hdr sCnt) .rax]

def next : List Instr :=
  [.mov .rax (.mem (hdr sCnt)), .alu .sub .rax (.imm 1), .store (hdr sCnt) .rax]

/-- Exactly `n + 1` squarings. The public counter reuses setup's existing header slot. -/
def run (mul : Nat → Nat → Nat → Prog isa) (n : Nat) : Prog isa :=
  .seq (.block (init n)) (.loop (.seq (mul aR2 aR2 aR2) (.block next)) .ne)

end VG.Impl.Bignum.X86_64.Public.R2Squares
