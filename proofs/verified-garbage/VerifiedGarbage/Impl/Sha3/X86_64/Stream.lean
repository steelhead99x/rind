module

public import VerifiedGarbage.Impl.Sha3.X86_64

/-!
# The SHA-3 sponge: x86-64 implementation

The streaming state is the Keccak state (`[u64; 25]` at `state`), with the
bytes of a partial block XORed into it as they arrive (see
`VG.Spec.Sha3.Repr`); the position in the block is kept by the caller.

* `absorb(state = rdi, rate = rsi, pos = rdx, data = rcx, len = r8,
  scratch = r9)` XORs the bytes of `data` into the state from byte `pos`, a
  lane at a time where it can (at a multiple of 8, with 8 bytes left) and a
  byte at a time otherwise, permuting the state whenever a block is
  complete, and returns the position after them.
* `pad(state = rdi, rate = rsi, pos = rdx, suffix = rcx, scratch = r8)` XORs
  the suffix into byte `pos` and `0x80` into byte `rate - 1`, and permutes
  the state.
* `squeeze(state = rdi, rate = rsi, pos = rdx, out = rcx, outlen = r8,
  scratch = r9)` copies the state to `out` from byte `pos`, a lane or a
  byte at a time likewise, permuting it whenever a block has been used up
  and more output is needed, and returns the position after them.

The permutation is called (`vg_keccak_f1600`, `Impl.Sha3.X86_64.permute`)
with the first 512 bytes of `scratch` as its scratch space. It preserves
`rbx, rbp, r12–r15`, so `absorb` and `squeeze` keep their variables there
across it (`rbx` = `state`, `r15` = `scratch`), and save their caller's
values of those registers in `scratch[512..560)`. The call stores its return
address in the 8 bytes below `rsp`. Every address and branch depends only on
the pointers, `rate`, `pos` and the lengths.
-/

@[expose] public section

namespace VG.Impl.Sha3.X86_64.Stream

open VG.X86_64
open VG.Impl.Sha3.X86_64 (at_ permute)

/-- The callee-saved registers, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 512), (.rbp, 520), (.r12, 528), (.r13, 536), (.r14, 544), (.r15, 552)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .store (at_ b d) r

/-- Restore them (`r15`, the base, last). -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r15 d))

/-- `[rbx + r12]`: byte `r12` of the state. -/
def stByte : MemOp := { base := .rbx, index := some .r12, scale := 1 }

/-- Permute the state at `rbx`, with scratch space `r15`. (`rbx` and `r15`
are copied back from `rdi` and `rsi`, which the permutation returns
unchanged, only for the constant-time analysis, which tracks which registers
hold the base address of a region through registers but not through
memory.) -/
def permuteAt : Prog isa :=
  .seq (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .r15)])
    (.seq (.call "vg_keccak_f1600" permute) (.block [.mov .rbx (.reg .rdi), .mov .r15 (.reg .rsi)]))

/-! ## `absorb`

Registers: `rbp` = `rate`, `r12` = the position in the block, `r13` =
`data`, `r14` = bytes of `data` left. -/

/-- ZF is set exactly when the position is at a lane (`r12 mod 8 = 0`) and at
least 8 bytes are left (of data or of output) (`r14 ≥ 8`, as `r14 - 8` is
then less than 2⁶³): `r10 = (r12 ∧ 7) ∨ ((r14 - 8) >> 63)` is then 0. -/
def wordTest : List Instr :=
  [.mov .r10 (.reg .r12), .mov32 .r11 (.imm 7), .alu .and .r10 (.reg .r11), .mov .r11 (.reg .r14),
    .alu .sub .r11 (.imm 8), .shift .shr .r11 63, .alu .or .r10 (.reg .r11), .alu .test .r10 (.reg .r10)]

/-- A lane of data XORed into the state; ZF is set if that completes the block. -/
def absorbWord : List Instr :=
  [.mov .rax (.mem { base := .r13 }), .alu .xor .rax (.mem stByte), .store stByte .rax,
    .alu .add .r13 (.imm 8), .alu .add .r12 (.imm 8), .alu .sub .r14 (.imm 8), .alu .cmp .r12 (.reg .rbp)]

/-- A byte of data XORed into the state; ZF is set if that completes the block. -/
def absorbByte : List Instr :=
  [.movzx8 .rax { base := .r13 }, .movzx8 .rcx stByte, .alu .xor .rax (.reg .rcx),
    .store8 stByte .rax, .alu .add .r13 (.imm 1), .alu .add .r12 (.imm 1),
    .alu .sub .r14 (.imm 1), .alu .cmp .r12 (.reg .rbp)]

def absorbBody : Prog isa :=
  .seq (.block wordTest)
  (.seq (.ite .e (.block absorbWord) (.block absorbByte))
    (.seq (.ite .e (.seq (.block [.mov32 .r12 (.imm 0)]) permuteAt) (.block []))
      (.block [.alu .test .r14 (.reg .r14)])))

def absorb : Prog isa :=
  .seq (.block (save .r9 ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .r13 (.reg .rcx), .mov .r14 (.reg .r8), .mov .r15 (.reg .r9), .alu .test .r14 (.reg .r14)] : List Instr)))
  (.seq (.ite .e (.block []) (.loop absorbBody .ne))
    (.block (.mov .rax (.reg .r12) :: restore)))

/-! ## `pad` -/

def pad : Prog isa :=
  .seq (.block [.movzx8 .rax { base := .rdi, index := some .rdx, scale := 1 },
      .alu .xor .rax (.reg .rcx), .store8 { base := .rdi, index := some .rdx, scale := 1 } .rax,
      .movzx8 .rax { base := .rdi, index := some .rsi, scale := 1, disp := -1 },
      .alu .xor .rax (.imm 0x80), .store8 { base := .rdi, index := some .rsi, scale := 1, disp := -1 } .rax,
      .mov .rsi (.reg .r8)])
    (.call "vg_keccak_f1600" permute)

/-! ## `squeeze`

Registers: `rbp` = `rate`, `r12` = the position in the block, `r13` =
`out`, `r14` = bytes of `out` left. -/

/-- A lane of the state to `out`. -/
def squeezeWord : List Instr :=
  [.mov .rax (.mem stByte), .store { base := .r13 } .rax, .alu .add .r13 (.imm 8),
    .alu .add .r12 (.imm 8), .alu .sub .r14 (.imm 8)]

/-- A byte of the state to `out`. -/
def squeezeByte : List Instr :=
  [.movzx8 .rax stByte, .store8 { base := .r13 } .rax, .alu .add .r13 (.imm 1),
    .alu .add .r12 (.imm 1), .alu .sub .r14 (.imm 1)]

def squeezeBody : Prog isa :=
  .seq (.block [.alu .cmp .r12 (.reg .rbp)])
  (.seq (.ite .e (.seq (.block [.mov32 .r12 (.imm 0)]) permuteAt) (.block []))
    (.seq (.block wordTest) (.ite .e (.block squeezeWord) (.block squeezeByte))))

def squeeze : Prog isa :=
  .seq (.block (save .r9 ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .r13 (.reg .rcx), .mov .r14 (.reg .r8), .mov .r15 (.reg .r9), .alu .test .r14 (.reg .r14)] : List Instr)))
  (.seq (.ite .e (.block []) (.loop squeezeBody .ne))
    (.block (.mov .rax (.reg .r12) :: restore)))

end VG.Impl.Sha3.X86_64.Stream
