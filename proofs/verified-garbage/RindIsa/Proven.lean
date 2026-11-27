import RindIsa.AArch64.Sha256Hw
import RindIsa.X86_64.Mul4x

/-! The functions rind proves in its models of AArch64 and x86_64, which
`rind-asm` prints and `vg-cosim --rind` cosimulates. -/

namespace Rind.AArch64

/-- A function rind proves, its body's program, and the statics it reads:
each its symbol in the program, its Rust path, and the words it begins
with. -/
structure Proven where
  path : String
  prog : VG.Prog isa
  statics : List (String × String × List (BitVec 32))

def proven : List Proven :=
  [{ path := "rind::low::aarch64::sha256::sha256_block_data_order_hw", prog := Sha256Hw.prog,
     statics := [(Sha256Hw.kName, "rind::low::aarch64::sha256::K256", Sha256Hw.table)] }]

end Rind.AArch64

namespace Rind.X86_64

/-- A function rind proves in its model of x86_64, and its body's program,
which reads no static. -/
structure Proven where
  path : String
  prog : VG.Prog isa

def proven : List Proven :=
  [{ path := "rind::low::x86_64::mont::bn_mul4x_mont", prog := Mul4x.prog }]

end Rind.X86_64
