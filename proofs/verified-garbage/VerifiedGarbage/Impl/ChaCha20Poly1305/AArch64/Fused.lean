module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64

/-!
# ChaCha20-Poly1305 on AArch64: the MAC's input absorbed in one pass

`macAll` absorbs the additional data and the data, each padded to a whole
number of blocks, and the lengths block into the Poly1305 state at
`ctx + 448`, as `macPad` twice and `absorbLengths` do, but with
`vg_poly1305_blocks`'s parts in line: the key and the accumulator are
loaded into registers once (`setup`), every block is absorbed from there,
and the accumulator is reduced and stored once (`reduce`, `storeH`). Four
calls of `vg_poly1305_blocks` each loaded, reduced and stored the
accumulator, and absorbed no block when the additional data had no whole
block.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.AArch64.Fused

open VG.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Impl.Poly1305.AArch64.Radix64 (setup absorb reduce storeH)

/-- The `x10` (1 to 15) bytes at `x1`, padded with zeros at `ctx + 16`, absorbed. -/
def tail : Prog isa :=
  .seq (.block [.movz .x .x11 0 0, .str .x .x11 .x21 16, .str .x .x11 .x21 24,
    .addImm .x .x9 .x21 16])
  (.seq copyLoop
    (.block (([.addImm .x .x1 .x21 16] : List Instr) ++ absorb true)))

/-- The whole blocks at `x1` (`x2` of them, nonzero) absorbed. -/
def loop : Prog isa :=
  .loop (.block (absorb true ++ VG.Impl.Poly1305.AArch64.advance)) (.nonzero .x .x2)

/-- The `n` bytes at `p`, padded with zeros to a multiple of 16, absorbed:
the whole blocks, which leave `x1` at the rest, and then the rest. -/
def seg (p n : Reg) : Prog isa :=
  .seq (.block [mov .x1 p, .lsr .x .x2 n 4])
  (.seq (.ite (.zero .x .x2) (.block []) loop)
  (.seq (.block [.lsl .x .x10 n 60, .lsr .x .x10 .x10 60])
    (.ite (.zero .x .x10) (.block []) tail)))

/-- The additional data and the data, each padded, and the lengths block
(at `ctx`), absorbed into the state at `ctx + 448`. -/
def macAll : Prog isa :=
  .seq (.block (([.addImm .x .x0 .x21 448] : List Instr) ++ setup))
  (.seq (seg .x24 .x25)
  (.seq (seg .x22 .x23)
    (.block (([.addImm .x .x1 .x21 0] : List Instr) ++ absorb true ++ reduce ++ storeH))))

end VG.Impl.ChaCha20Poly1305.AArch64.Fused
