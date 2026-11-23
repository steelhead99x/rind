import RindIsa.AArch64.Sha256Hw

/-! The functions rind proves in its model of AArch64, which `rind-asm`
prints and `vg-cosim --rind` cosimulates. -/

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
