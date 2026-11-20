module

public import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed8
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Poly

/-!
# ChaCha20 and Poly1305 together (AArch64)

The eight-block ChaCha20 kernel (`Impl/ChaCha20/AArch64/Mixed8.lean`) keeps
the AdvSIMD units busy with six blocks and the integer units with two, one
at a time, but leaves the multiplier idle and nine general-purpose registers
free. ChaCha20-Poly1305 fills them with Poly1305 (`Poly.lean`), as
BoringSSL's `chacha20_poly1305_armv8.pl` does with its own kernel: each
chunk of 512 bytes absorbs 32 blocks of Poly1305 while its rounds run. The
two computations are independent, so out-of-order cores overlap them.

A chunk is the kernel's (`Mixed8.chunkFrom`, from the source at `x27` to the
destination at `x1`) with each of its two counted phases of five double
rounds replaced by `phase`: `x20` (the kernel's working space, which the
phase does not use) points at the 256 bytes the phase absorbs, a block is
absorbed, and each of the five iterations absorbs three more after its double
round; then `x27`, which the blocks use, is set back to the source (`back`),
and `x20` is restored to the working space, which is 64 bytes after the
ChaCha20 state in the ChaCha20-Poly1305 context. The chunks run as the
stream's do (`Mixed8.enterFrom`, `Mixed8.leaveFrom`).
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.AArch64.Stitch

open VG.AArch64
open VG.Impl.ChaCha20.AArch64

/-- Three blocks. -/
def absorb3 : List Instr := Poly.block ++ Poly.block ++ Poly.block

/-- `n` blocks. -/
def absorbN (n : Nat) : List Instr := (List.replicate n Poly.block).flatten

/-- A counted phase with Poly1305: `start` sets `x20` to the first block,
`lead` blocks are absorbed, and `k` more after each double round; then `back`
sets `x27`, which the blocks use, back to the chunk's source (from where `x20`
stopped), and `x20` and `x1` are restored. -/
def phaseWith (sve : Bool) (start : Instr) (restore : Reg) (lead k : Nat) (back : Instr) : Prog isa :=
  .seq (.block ([start] ++ absorbN lead ++ ([.movz .x .x1 5 0] : List Instr)))
    (.seq (.loop (.seq (Mixed8.parallelRound sve) (.block (absorbN k ++ ([.subImm .x .x1 .x1 1] : List Instr))))
        (.nonzero .x .x1))
      (.block [back, .addImm .x .x20 .x0 64, .addImm .x .x1 restore 0]))

/-- Where the 256 bytes a phase absorbs start: when decrypting, the chunk's
source (`x27`) and its second half; when encrypting, the previous chunk's
output, which is before the chunk's (`x26`, its data during the chunk). -/
def start (enc : Bool) (half : Nat) : Instr :=
  if enc then .subImm .x .x20 .x26 (512 - 256 * half) else .addImm .x .x20 .x27 (256 * half)

/-- The chunk's source back in `x27`, after the phase: when decrypting, the
256 bytes before where `x20` stopped, after `half + 1` halves; when
encrypting, in place, the chunk's data (`x26`). -/
def back (enc : Bool) (half : Nat) : Instr :=
  if enc then .addImm .x .x27 .x26 0 else .subImm .x .x27 .x20 (256 * (half + 1))

/-- The kernel's chunk, its two phases absorbing `l₀ + 5 k₀` blocks from where
`st₀` points `x20` and `l₁ + 5 k₁` from where `st₁` does, each ending with
`bk₀` or `bk₁`, and its data XORed from `r` (`Mixed8.finishFrom`). -/
def chunkWith (sve : Bool) (st₀ st₁ : Instr) (l₀ k₀ l₁ k₁ : Nat) (bk₀ bk₁ : Instr) (r : Reg) : Prog isa :=
  .seq Mixed8.prepare (.seq (phaseWith sve st₀ .x26 l₀ k₀ bk₀)
    (.seq Mixed8.second (.seq (phaseWith sve st₁ .x20 l₁ k₁ bk₁) (.seq (Mixed8.spill 64) (Mixed8.finishFrom r)))))

/-- One chunk of 512 bytes from the source at `x27` to the destination at `x1`,
with 32 blocks of Poly1305. -/
def chunk (sve enc : Bool) : Prog isa :=
  chunkWith sve (start enc 0) (start enc 1) 1 3 1 3 (back enc 0) (back enc 1) .x27

/-- A chunk, then the counter and the pointers advanced (as `Mixed8.bodyFrom`). -/
def body (sve enc : Bool) : Prog isa :=
  .seq (chunk sve enc) (.block (Mixed8.next ++ ([.addImm .x .x27 .x27 512] : List Instr)))

/-- Chunks while 512 bytes remain. -/
def chunks (sve enc : Bool) : Prog isa := .loop (body sve enc) (.zero .x .x5)

/-- The whole chunks of at least 512 bytes of data, with the stream's
registers (`x0`–`x4`, as `vg_chacha20_xor`'s arguments: the source at `x1`,
the destination at `x4`) and the accumulator in `x21`–`x23`: `x19`, `x20`,
`x26`, `x27`, `v8` and `v9` saved in the working space and the source moved to
`x27`, the destination to `x1` (`Mixed8.enterFrom`), and the chunks. When
encrypting, a chunk absorbs the one before it, so the first is the kernel's
own (`Mixed8.bodyFrom`). -/
def bulk (sve enc : Bool) : Prog isa :=
  .seq (.block Mixed8.enterFrom)
    (.seq (if enc then .seq (Mixed8.bodyFrom sve) (.ite (.nonzero .x .x5) (.block []) (chunks sve true))
      else chunks sve false)
      (.block Mixed8.leaveFrom))

/-! ## The keystream of eight blocks while absorbing other data

From 449 to 511 bytes, `open` (`Stitched.lean`'s `OpenPad`) has the kernel
encrypt 512 bytes of zeros, the keystream of the data, while Poly1305
absorbs the data's first 448 bytes: the data is at `x27`, from where each
phase points `x20` at its part, sixteen blocks in the first and twelve in the
second (two, and then two after each double round), and to where it sets `x27`
back. -/

/-- A chunk of the kernel absorbing 448 bytes from `x27`. -/
def chunkPad (sve : Bool) : Prog isa :=
  chunkWith sve (.addImm .x .x20 .x27 0) (.addImm .x .x20 .x27 256) 1 3 2 2
    (.subImm .x .x27 .x20 256) (.subImm .x .x27 .x20 448) .x1

/-- `chunkPad`, with the registers it uses saved and restored. -/
def bulkPad (sve : Bool) : Prog isa :=
  .seq (.block Mixed8.enter) (.seq (chunkPad sve) (.block Mixed8.leave))

/-- The chunks that encrypt and those that decrypt, with and without SVE2, as
constants (whose literals the proofs evaluate). -/
def bulkSeal : Prog isa := bulk false true
def bulkOpen : Prog isa := bulk false false
def bulkSealSve : Prog isa := bulk true true
def bulkOpenSve : Prog isa := bulk true false
def bulkPadNeon : Prog isa := bulkPad false
def bulkPadSve : Prog isa := bulkPad true

end VG.Impl.ChaCha20Poly1305.AArch64.Stitch
