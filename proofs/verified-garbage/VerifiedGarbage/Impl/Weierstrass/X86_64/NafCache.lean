module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Naf
import VerifiedGarbage.Impl.Weierstrass.X86_64.NafPrep

/-! Public lookup of the cached Z² and Z³ belonging to an odd multiple. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.Naf
open VG VG.X86_64 VG.Impl.Mont.X86_64

/-- `rax = (a - 1) 8 n` for the odd magnitude `a` in `r8`: a shift for four
words, else a product through `rcx` and `rdx`. -/
def cacheOffset (n : Nat) : List Instr :=
  if n = 4 then [.mov .rax (.reg .r8),.alu .sub .rax (.imm 1),.shift .shl .rax 5]
  else [.mov .rax (.reg .r8),.alu .sub .rax (.imm 1),
    .mov32 .rcx (.imm (BitVec.ofNat 32 (8*n))),.mul .rcx]

/-- For odd magnitude `a` in `r8`, select cache entry `(a-1)/2`, `16 n` bytes each. -/
def cacheAddress (n tbl : Nat) : List Instr :=
  cacheOffset n ++
  [.mov .rdx (.reg .rdi),.alu .add .rdx (.imm (BitVec.ofNat 32 tbl)),
   .alu .add .rdx (.reg .rax)]

def cacheRead (n tbl dst : Nat) : List Instr :=
  cacheAddress n tbl ++ copyPieces n (fun i => tblAt (16*i)) (fun i => sc (dst+16*i))

/-- The coordinates and powers use the same odd magnitude, retained in `r8`. -/
def cachedEntry (K : WinCfg) (tbl dst : Nat) : List Instr :=
  publicEntry K ++ cacheRead K.M.n tbl dst

def signedCachedEntry (K : WinCfg) (tbl dst : Nat) : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 128)]) <|
    .ite .b (.block (cachedEntry K tbl dst)) (.block (
      [.mov32 .rax (.imm 256),.alu .sub .rax (.reg .r8),.mov .r8 (.reg .rax)] ++
      cachedEntry K tbl dst ++ VG.Impl.Mont.X86_64.sub K.M K.E.y K.zero K.E.y))

end VG.Impl.Weierstrass.X86_64.Naf
