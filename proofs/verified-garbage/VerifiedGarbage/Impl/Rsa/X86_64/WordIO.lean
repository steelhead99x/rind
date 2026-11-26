module

public import VerifiedGarbage.Impl.Bignum.X86_64

/-! Word-sized conversion for public RSA operands whose byte length is a
multiple of eight. Other lengths retain the byte conversion. -/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.WordIO
open VG VG.X86_64 VG.Impl.Bignum.X86_64

def atByte (r idx : Reg) : MemOp := { base := r, index := some idx }

def loadWords : Prog isa :=
  .seq (.block [.mov .r14 (.reg .rsi), .alu .add .r14 (.reg .rcx), .mov32 .rdx (.imm 0)])
    (.loop (.block [.alu .sub .r14 (.imm 8), .mov .rax (.mem (at0 .r14)), .bswap .rax,
      .store (atByte .rbx .rdx) .rax, .alu .add .rdx (.imm 8), .alu .cmp .rdx (.reg .rcx)]) .ne)

def storeWords : Prog isa :=
  .seq (.block [.mov .r14 (.reg .rsi), .alu .add .r14 (.reg .rcx), .mov32 .rdx (.imm 0)])
    (.loop (.block [.mov .rax (.mem (atByte .rbx .rdx)), .alu .and .rax (.reg .r15), .bswap .rax,
      .alu .sub .r14 (.imm 8), .store (at0 .r14) .rax,
      .alu .add .rdx (.imm 8), .alu .cmp .rdx (.reg .rcx)]) .ne)

def lengthTest : List Instr :=
  [.mov .rax (.reg .rcx), .alu .and .rax (.imm 7), .alu .cmp .rax (.imm 0)]

def load : Prog isa := .seq (.block lengthTest) (.ite .e loadWords loadBE)
def store : Prog isa := .seq (.block lengthTest) (.ite .e storeWords storeBE)
end VG.Impl.Rsa.X86_64.WordIO
