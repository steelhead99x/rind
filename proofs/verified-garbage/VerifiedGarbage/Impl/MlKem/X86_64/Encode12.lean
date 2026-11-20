module

public import VerifiedGarbage.Impl.MlKem.X86_64.Common

/-!
# ML-KEM on x86-64: `vg_mlkem_encode12` and `vg_mlkem_decode12`

Both run over the 128 pairs of coefficients, each 3 bytes, with `rcx`
counting down.

* `encode12(f = rdi, out = rsi)`: the pair `f₀, f₁` (each less than
  `2¹²`) is the 24-bit number `f₀ + 2¹² f₁` (`f₁` shifted left by rotating
  it right by 20: its top bits are zero), whose three bytes are stored.
* `decode12(b = rdi, f = rsi)`: the three bytes are the 24-bit number `w`
  (the bytes shifted left by rotations), whose two 12-bit fields
  `w mod 2¹²` and `⌊w / 2¹²⌋` are reduced modulo `q` with `csubQ` and
  stored.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- The 24-bit number of the pair at `rdi`, in `rax`. -/
def enc12Pair : List Instr :=
  [.mov32 .rax (.mem (at_ .rdi 0)), .mov32 .rdx (.mem (at_ .rdi 4)), .shift32 .ror .rdx 20,
    .alu32 .add .rax (.reg .rdx)]

/-- Its three bytes to `rsi`. -/
def enc12Store : List Instr :=
  [.store8 (at_ .rsi 0) .rax, .shift32 .shr .rax 8, .store8 (at_ .rsi 1) .rax, .shift32 .shr .rax 8,
    .store8 (at_ .rsi 2) .rax]

def enc12Step : List Instr := [.alu .add .rdi (.imm 8), .alu .add .rsi (.imm 3), .alu .sub .rcx (.imm 1)]

def encode12Body : List Instr := enc12Pair ++ enc12Store ++ enc12Step

def encode12 : Prog isa := .seq (.block [.mov32 .rcx (.imm 128)]) (.loop (.block encode12Body) .ne)

/-- The 24-bit number of the three bytes at `rdi`, in `rax`. -/
def dec12Load : List Instr :=
  [.movzx8 .rax (at_ .rdi 0), .movzx8 .rdx (at_ .rdi 1), .shift32 .ror .rdx 24,
    .alu32 .add .rax (.reg .rdx), .movzx8 .rdx (at_ .rdi 2), .shift32 .ror .rdx 16,
    .alu32 .add .rax (.reg .rdx)]

/-- Its two fields, reduced, to `rsi`. -/
def dec12Fields : List Instr :=
  [.mov32 .rdx (.reg .rax), .alu32 .and .rax (.imm 0xfff), .shift32 .shr .rdx 12] ++
    csubQ .rax .r8 ++ csubQ .rdx .r8 ++ [.store32 (at_ .rsi 0) .rax, .store32 (at_ .rsi 4) .rdx]

def dec12Step : List Instr := [.alu .add .rdi (.imm 3), .alu .add .rsi (.imm 8), .alu .sub .rcx (.imm 1)]

def decode12Body : List Instr := dec12Load ++ dec12Fields ++ dec12Step

def decode12 : Prog isa := .seq (.block [.mov32 .rcx (.imm 128)]) (.loop (.block decode12Body) .ne)

end VG.Impl.MlKem.X86_64
