module

public import VerifiedGarbage.Impl.Mont.X86_64

/-! Branchless modular halving for canonical P-256 field elements. -/

@[expose] public section

namespace VG.Impl.P256.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64

namespace Half

/-- Mask the prime by the low bit of the input; clear the fifth limb. -/
def mask : List Instr :=
  [.mov .rax (.reg .r8), .alu .and .rax (.imm 1), .mov32 .rcx (.imm 0),
   .alu .sub .rcx (.reg .rax), .mov .rdx (.reg .rcx), .shift .shr .rdx 32,
   .movImm64 .rbp 0xffffffff00000001, .alu .and .rbp (.reg .rcx), .mov32 .r12 (.imm 0)]

/-- Add the masked prime, keeping the carry in a fifth limb. -/
def add : List Instr :=
  [.alu .add .r8 (.reg .rcx), .alu .adc .r9 (.reg .rdx), .alu .adc .r10 (.imm 0),
   .alu .adc .r11 (.reg .rbp), .alu .adc .r12 (.imm 0)]

/-- Shift the 257-bit sum right by one, returning four limbs. -/
def shift : List Instr :=
  (List.range 4).flatMap fun i =>
    let rs : List Reg := [.r8,.r9,.r10,.r11,.r12]
    [.shift .shr (rs.getD i .r8) 1, .mov .rax (.reg (rs.getD (i+1) .r8)),
     .shift .shl .rax 63, .alu .or (rs.getD i .r8) (.reg .rax)]

end Half

/-- `[o] = [a]/2 mod p`; the input and output may overlap. -/
def half (o a : Nat) : List Instr :=
  loads [.r8,.r9,.r10,.r11] a ++ Half.mask ++ Half.add ++ Half.shift ++
    stores [.r8,.r9,.r10,.r11] o

end VG.Impl.P256.X86_64
