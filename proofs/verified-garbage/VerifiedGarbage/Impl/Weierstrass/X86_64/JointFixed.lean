module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Naf

/-! Direct generator-table lookup for public width-seven NAF digits. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.Joint
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

/-- `rax = (a - 1) 16 n` for the magnitude `a` in `r8`: a shift for four
words, else a product through `rcx` and `rdx`. -/
def fixedOffset (n : Nat) : List Instr :=
  if n = 4 then [.mov .rax (.reg .r8),.alu .sub .rax (.imm 1),.shift .shl .rax 6]
  else [.mov .rax (.reg .r8),.alu .sub .rax (.imm 1),
    .mov32 .rcx (.imm (BitVec.ofNat 32 (16*n))),.mul .rcx]

/-- The existing affine table has `16 n`-byte entries for consecutive multiples. -/
def fixedAddress (n : Nat) (tsym : String) : List Instr :=
  fixedOffset n ++ [.leaSym .rdx tsym,.alu .add .rdx (.reg .rax)]

def fixedLoad (K : WinCfg) (tsym : String) : List Instr :=
  fixedAddress K.M.n tsym ++
  Naf.copyPieces K.M.n (fun i => tblAt (16*i)) (fun i => sc (K.E.x+16*i)) ++
  setConst K.M.n K.E.z K.one

def fixedEntry (K : WinCfg) (tsym : String) : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 128)]) <|
    .ite .b (.block (fixedLoad K tsym)) (.block (
      [.mov32 .rax (.imm 256),.alu .sub .rax (.reg .r8),.mov .r8 (.reg .rax)] ++
      fixedLoad K tsym ++ VG.Impl.Mont.X86_64.sub K.M K.E.y K.zero K.E.y))

/-- `fixedEntry` for a digit of `±1 … ±255` in sixteen bits. -/
def fixedEntryW (K : WinCfg) (tsym : String) : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 256)]) <|
    .ite .b (.block (fixedLoad K tsym)) (.block (
      [.mov32 .rax (.imm 65536),.alu .sub .rax (.reg .r8),.mov .r8 (.reg .rax)] ++
      fixedLoad K tsym ++ VG.Impl.Mont.X86_64.sub K.M K.E.y K.zero K.E.y))

end VG.Impl.Weierstrass.X86_64.Joint
