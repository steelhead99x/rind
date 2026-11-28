module

public import VerifiedGarbage.Impl.Mont.X86_64

/-! Four-limb modular doubling with a single input load. -/

@[expose] public section

namespace VG.Impl.Mont.X86_64
open VG.X86_64

namespace Double4

def sum : List Instr :=
  [.mov32 .r12 (.imm 0), .alu .add .r8 (.reg .r8), .alu .adc .r9 (.reg .r9),
   .alu .adc .r10 (.reg .r10), .alu .adc .r11 (.reg .r11), .alu .adc .r12 (.imm 0)]

end Double4

/-- For `M.n = 4`, double a canonical field value without loading it twice. -/
def double4 (M : Mod) (o a : Nat) : List Instr :=
  loads [.r8,.r9,.r10,.r11] a ++ Double4.sum ++
    csubC M [.r8,.r9,.r10,.r11] .r12 ++ stores [.r8,.r9,.r10,.r11] o

end VG.Impl.Mont.X86_64
