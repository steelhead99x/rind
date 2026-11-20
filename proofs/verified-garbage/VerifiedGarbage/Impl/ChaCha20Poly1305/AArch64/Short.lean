module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Fused

/-!
# ChaCha20-Poly1305: AArch64, up to 256 bytes

With 64 to 256 bytes of data (1 to 256 with SVE2: `lo`), `seal` and `open` compute the one-time key and
the data's keystream together, in one pass of the five-block ChaCha20 kernel
(`Mixed5.chunk`: four blocks in NEON lanes and one in the integer
registers; with SVE2, each vector XOR and rotation is one XAR), rather than
the one-time key with `vg_chacha20_block` and the keystream with
`vg_chacha20_xor`. The kernel XORs the keystream of its five
blocks into 320 bytes; given zeros, it leaves the keystream itself. The
context (`../AArch64.lean`) is laid out differently while it runs:

* `[0, 64)`: the ChaCha20 state for counter 0 (the lengths block and the
  padded block are written there only after the pass);
* `[64, 384)`: the keystream of the blocks with counters 0 to 4: the
  one-time key, then the data's;
* `[384, 448)`: the kernel's integer block, before it is XORed in (`x3`,
  the kernel's buffer, whose other 256 bytes it does not write);
* `[632, 656)`: our caller's `x19`, `x20` and `x26`, which the kernel uses.

Then the one-time key initializes Poly1305 at `[448, 576)`, as in
`prologue`, and the data is XORed with its keystream (`xorKs`) 16 bytes at a
time and then a byte at a time, before Poly1305 absorbs it when encrypting
and after when decrypting.

The branch on the length is the only one added, and the kernel's addresses
are the context plus constants: only the pointers and the lengths can affect
timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.AArch64.Short

open VG.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)

/-- The shortest length this code takes: 1 with SVE2 (`sve`), whose kernel is
faster than the two scalar blocks of the existing path even for one block of
keystream, and 64 without, where it is not. -/
def lo (sve : Bool) : Nat := if sve then 1 else 64

/-- `x9 = 0` iff `lo sve ≤ len ≤ 511`, the lengths that start with this code's
prologue (`ShortRest.lean` takes those above 256): `(len - 1) | (len - lo) | len`
is below 512 iff each of them is, and each subtraction wraps around below.
`len - 1` adds nothing to `len - lo` but keeps the check five instructions
long, as it was when it took up to 256 bytes, so the stitched code after it is
at the same addresses: four instructions put the seal's loops four bytes
earlier, 1.0-2.8% slower at 4 to 16 KiB, as five of different lengths in the two
instances put the SVE2 instance's loop 1.2-1.6% slower. -/
def check (sve : Bool) : List Instr :=
  [.subImm .x .x9 .x5 1, .subImm .x .x10 .x5 (lo sve), .logic .orr .x .x9 .x9 .x10,
    .logic .orr .x .x9 .x9 .x5, .lsr .x .x9 .x9 9]

/-- The ChaCha20 state for counter 0, at `x21`. -/
def initState0 : List Instr := (List.range 16).flatMap (stWAt 0)

/-- The kernel's output zeroed: `ctx[64, 384)`. -/
def zero : List Instr :=
  [.vop (.logic .eor .v0 .v0 .v0)] ++ (List.range 20).map fun i => .strq .v0 .x21 (64 + 16 * i)

/-- `x19`, `x20` and `x26` saved, and the kernel's arguments: the state
(`x0`), the output (`x1`) and the buffer (`x3`, also in `x20`). -/
def enter : List Instr :=
  [.str .x .x19 .x21 632, .str .x .x20 .x21 640, .str .x .x26 .x21 648,
   .addImm .x .x0 .x21 0, .addImm .x .x1 .x21 64, .addImm .x .x3 .x21 384, mov .x20 .x3]

/-- `x19`, `x20` and `x26` restored, and `vg_poly1305_init`'s arguments. -/
def leave : List Instr :=
  [.ldr .x .x19 .x21 632, .ldr .x .x20 .x21 640, .ldr .x .x26 .x21 648,
   .addImm .x .x0 .x21 448, .addImm .x .x1 .x21 64]

/-- Saves the registers, moves the arguments, and computes the keystream of
counters 0 to 4 and the Poly1305 state for the one-time key; the kernel's
vector rounds use SVE2's XAR if `sve`. -/
def prologue (sve : Bool) : Prog isa :=
  .seq (.block (save ++ moves ++ initState0 ++ zero ++ enter))
  (.seq (.seq (VG.Impl.ChaCha20.AArch64.Mixed5.chunk sve) (.block leave))
    (.call "vg_poly1305_init" Impl.Poly1305.AArch64.init))

/-- XORs `x11` (nonzero) blocks of 16 bytes at `x9` with those at `x10` into
`x15`, advancing all three. -/
def xor16 : Prog isa :=
  .loop (.block [.ldrq .v0 .x9 0, .ldrq .v1 .x10 0, .vop (.logic .eor .v0 .v0 .v1), .strq .v0 .x15 0,
    .addImm .x .x9 .x9 16, .addImm .x .x10 .x10 16, .addImm .x .x15 .x15 16, .subImm .x .x11 .x11 1])
    (.nonzero .x .x11)

/-- XORs the `x11` (nonzero) bytes at `x9` with those at `x10` into `x15`,
advancing all three. -/
def xor1 : Prog isa :=
  .loop (.block [.ldrb .x12 .x9 0, .ldrb .x13 .x10 0, .logic .eor .w .x12 .x12 .x13, .strb .x12 .x15 0,
    .addImm .x .x9 .x9 1, .addImm .x .x10 .x10 1, .addImm .x .x15 .x15 1, .subImm .x .x11 .x11 1])
    (.nonzero .x .x11)

/-- The data (`x22`, `x23` bytes) XORed with its keystream into its
destination, at the addresses `setup` puts in `x10` and `x15` (with the
data's in `x9` and `x23 >> 4` in `x11`). -/
def xorKsWith (setup : List Instr) : Prog isa :=
  .seq (.block setup)
  (.seq (.ite (.zero .x .x11) (.block []) xor16)
  (.seq (.block [.lsl .x .x11 .x23 60, .lsr .x .x11 .x11 60])
    (.ite (.zero .x .x11) (.block []) xor1)))

/-- The destination of the data at `x9`, into `x15`: `x9 + x28` if `to` (`open`,
which keeps in `x28` the destination's distance from the data), else the data
itself (`seal`, in place). -/
def dstOf (to : Bool) : Instr := if to then .add .x .x15 .x9 .x28 else mov .x15 .x9

/-- The data (`x22`, `x23` bytes) XORed with its keystream, at `ctx + k`, into
its destination (`dstOf to`). -/
def xorKsFrom (to : Bool) (k : Nat) : Prog isa :=
  xorKsWith [mov .x9 .x22, dstOf to, .addImm .x .x10 .x21 k, .lsr .x .x11 .x23 4]

/-- The data XORed with its keystream, at `ctx + 128`. -/
def xorKs (to : Bool) : Prog isa := xorKsFrom to 128

/-- `seal` but for the tag, after the prologue: the data encrypted, then
the MAC's input absorbed in one pass (`Fused.macAll`). -/
def sealAfter : Prog isa :=
  .seq (.block lengths)
  (.seq (xorKs false)
    Fused.macAll)

/-- `open` up to the tag computed, after the prologue. -/
def openAfter : Prog isa :=
  .seq (.block lengths)
  (.seq Fused.macAll
  (.seq (xorKs true)
    (finalizeTo 48)))

end VG.Impl.ChaCha20Poly1305.AArch64.Short
