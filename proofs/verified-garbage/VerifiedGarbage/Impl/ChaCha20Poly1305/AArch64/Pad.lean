module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.ShortRest

/-!
# ChaCha20-Poly1305: AArch64, the data's keystream from eight blocks

For data of up to 511 bytes, `vg_chacha20_xor` (`Small.lean`) computes the
keystream four blocks and then one to three at a time, while from 512 bytes
its eight-block kernel (`Mixed8.lean`) computes eight blocks in about the time
the smaller kernels take for four. `cryptPad` gives the data the eight
blocks' keystream instead, in place of `cryptWith`'s call of the stream on
the data:

* `ctx[768, 1280)` is zeroed, and the stream encrypts it, 512 bytes from
  counter 1, with the state at `ctx + 64` and its working space at
  `ctx + 128` (as `cryptWith` does the data): it then holds the keystream of
  counters 1 to 8;
* the data, up to 512 bytes, is XORed with it (`Short.xorKsFrom 768`);
* `ctx[768, 1280)` is zeroed again, as the frame's wipe leaves it.

`sealMain` and `openMain` are `sealMainWith` and `openMainWith` (the
one-time key from the scalar block function) with `cryptPad`. They take the
lengths above `threshold` (`sealRoute`; `Stitched.lean`'s `openRoute`, which
from 449 bytes decrypts with `OpenPad.openMain` instead) up to 511:
`ShortRest.lean`'s code, whose pass of five blocks computes the key and 256
bytes of keystream together, is faster below it. The branch is on the length only, and the addresses are the
context and the data plus constants: only the pointers and the lengths can
affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.AArch64.Pad

open VG.AArch64
open VG.Impl.ChaCha20.AArch64 (XorCallee)

/-- The longest data `ShortRest.lean`'s code takes: 320 bytes with SVE2
(`sve`), 448 without. This file's code takes the same time from 320 to 511
bytes, while `ShortRest.lean`'s stream gets slower with each block after the
first 256 bytes, and a partial last block costs it a step more. With SVE2 this
file's is the faster from 384 bytes; without, `ShortRest.lean`'s is faster at
384 and at 448 bytes, whole blocks after 256 (by 0.5-1.6%), and slower at 449
and 480 (by 12-14%). -/
def threshold (sve : Bool) : Nat := if sve then 320 else 448

/-- `x9 = 0` iff `len ≤ threshold sve`: `(len + 511 - threshold sve) >> 9`.
Both instances are two instructions. -/
def split (sve : Bool) : List Instr := [.addImm .x .x9 .x5 (511 - threshold sve), .lsr .x .x9 .x9 9]

/-- `ctx[768, 1280)` zeroed, through `v0`. -/
def zero : List Instr :=
  .vop (.logic .eor .v0 .v0 .v0) :: (List.range 32).map fun i => .strq .v0 .x21 (768 + 16 * i)

/-- The stream's arguments: the counter set to 1, the state, `ctx[768, 1280)`,
512 bytes, and the working space. -/
def args : List Instr :=
  [.movz .w .x9 1 0, .str .w .x9 .x21 112, .addImm .x .x0 .x21 64, .addImm .x .x1 .x21 768,
   .movz .x .x2 512 0, .addImm .x .x3 .x21 128]

/-- The keystream of counters 1 to 8 at `ctx[768, 1280)`, and the data XORed
with it into its destination (`Short.dstOf to`). -/
def cryptPad (c : XorCallee) (to : Bool) : Prog isa :=
  .seq (.block (zero ++ args))
    (.seq c.inPlace
      (.seq (Short.xorKsFrom to 768) (.block zero)))

def sealMain (c : XorCallee) : Prog isa := sealMainWith (cryptPad c false)

def openMain (c : XorCallee) : Prog isa := openMainWith (cryptPad c true)

/-- From `lo` to 511 bytes when encrypting: `ShortRest.lean`'s code up to
`threshold`, then this file's. -/
def sealRoute (c : XorCallee) : Prog isa :=
  .seq (.block (split c.sve)) (.ite (.zero .x .x9) (ShortRest.sealMain c) (sealMain c))

end VG.Impl.ChaCha20Poly1305.AArch64.Pad
