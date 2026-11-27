module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# ML-KEM on x86-64: common code

Pieces of code that the ML-KEM functions share: `csubQ r m`, `r ← r mod q`
for a 32-bit `r < 2q`, without a branch: `sub r, q` sets CF exactly when
`r < q`, `sbb m, m` turns it into a mask (all ones or zero), and `q` masked
with it is added back.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `q = 3329`, as an immediate. -/
def qImm : BitVec 32 := 3329

/-- `r ← r mod q` for `r < 2q` (32 bits), with `m` as a mask. -/
def csubQ (r m : Reg) : List Instr :=
  [.alu32 .sub r (.imm qImm), .alu32 .sbb m (.reg m), .alu32 .and m (.imm qImm),
    .alu32 .add r (.reg m)]

end VG.Impl.MlKem.X86_64
