module
public import VerifiedGarbage.Impl.Weierstrass.X86_64

/-! Signed five-bit NAF recoding of a public scalar of `n` words into `64 n + 1` bytes. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.Naf
open VG VG.X86_64 VG.Impl.Mont.X86_64

/-- The scalar's `n` words and a top word: `r8` up, then `rbp` and `rsi` for
nine words (free while recoding: the prologue saves `rbp`, and `rsi`'s
argument is read by then). -/
def sregs (n : Nat) : List Reg := [.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi].take (n+1)

/-- The scalar's top word. -/
def stop (n : Nat) : Reg := (sregs n).getLastD .r8

def initN (n src : Nat) : List Instr :=
  loads ((sregs n).take n) src ++ [.mov32 (stop n) (.imm 0),.mov32 .rbx (.imm 0)]

def init (src : Nat) : List Instr :=
  loads [.r8,.r9,.r10,.r11] src ++ [.mov32 .r12 (.imm 0),.mov32 .rbx (.imm 0)]

def subtractDigit : List Instr :=
  [.mov .rax (.reg .rcx),.shift .shr .rax 63,.mov32 .rdx (.imm 0),.alu .sub .rdx (.reg .rax),
   .alu .sub .r8 (.reg .rcx),.alu .sbb .r9 (.reg .rdx),.alu .sbb .r10 (.reg .rdx),
   .alu .sbb .r11 (.reg .rdx),.alu .sbb .r12 (.reg .rdx)]

/-- `r8 … = r8 … - rcx` for the sign-extended digit `rcx`, through `rax` and `rdx`. -/
def subtractDigitN (n : Nat) : List Instr :=
  [.mov .rax (.reg .rcx),.shift .shr .rax 63,.mov32 .rdx (.imm 0),.alu .sub .rdx (.reg .rax),
   .alu .sub .r8 (.reg .rcx)] ++ (sregs n).tail.map fun r => .alu .sbb r (.reg .rdx)

end VG.Impl.Weierstrass.X86_64.Naf
