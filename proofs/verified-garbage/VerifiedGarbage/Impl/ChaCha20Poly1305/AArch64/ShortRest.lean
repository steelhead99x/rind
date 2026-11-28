module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Short

/-!
# ChaCha20-Poly1305: AArch64, 257 to 511 bytes

`Short.lean`'s five-block pass computes the one-time key and the keystream
of the first 256 bytes; the rest, 1 to 255 bytes, is encrypted by the
stream (`vg_chacha20_xor`) from counter 5, rather than all of the data from
counter 1 after a scalar block for the key (`../AArch64.lean`):

* after `Short.prologue`, the ChaCha20 state for counter 0 at `ctx[0, 64)`
  is copied to `ctx[64, 128)` (whose one-time key Poly1305 has read), with
  counter 5 (`stash`), since the padded blocks and the lengths block
  overwrite `ctx[0, 32)` before `open` decrypts;
* the first 256 bytes are XORed with their keystream at `ctx[128, 384)`
  (`Short.xorKs`, with `x23` set to 256 and restored from `x14`, which
  `xorKs` does not use);
* the stream encrypts the rest, with the state at `ctx + 64` and its working
  space at `ctx + 128` (`rest`), as `cryptWith` does all of the data.

Poly1305 absorbs the data as in `Short.lean`, after encrypting and before
decrypting. `Short.lean`'s code for up to 256 bytes shares the prologue: the
code branches on the length after it (`split`), so that the prologue is
emitted once. The branch on the length is the only one added, and the
addresses are the context and the data plus constants: only the pointers
and the lengths can affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.AArch64.ShortRest

open VG.AArch64
open VG.Impl.ChaCha20.AArch64 (XorCallee)
open VG.Impl.ChaCha20.AArch64.Xor (mov)

/-- `x9 = 0` iff `len ≤ 256`, after the prologue (with the length in `x23`,
and `1 ≤ len`): `(len - 1) >> 8` is zero iff `1 ≤ len ≤ 256`. -/
def split : List Instr := [.subImm .x .x9 .x23 1, .lsr .x .x9 .x9 8]

/-- Word `k` of the state at `ctx[0, 64)` copied to `ctx[64, 128)`, through
`w9`; the counter (word 12) set to 5. -/
def stashW (k : Nat) : List Instr :=
  if k = 12 then [.movz .w .x9 5 0, .str .w .x9 .x21 (64 + 4 * k)]
  else [.ldr .w .x9 .x21 (4 * k), .str .w .x9 .x21 (64 + 4 * k)]

/-- The state for counter 0 at `ctx[0, 64)` copied to `ctx[64, 128)`, with
counter 5. -/
def stash : List Instr := (List.range 16).flatMap stashW

/-- The first 256 bytes XORed with their keystream, at `ctx + 128`, into
their destination (`Short.dstOf to`). -/
def first (to : Bool) : Prog isa :=
  .seq (.block [mov .x14 .x23, .movz .x .x23 256 0])
    (.seq (Short.xorKs to) (.block [mov .x23 .x14]))

/-- The rest, after 256 bytes, encrypted or decrypted from the state at
`ctx + 64`, into its destination (`XorCallee.callWith to`). -/
def rest (c : XorCallee) (to : Bool) : Prog isa :=
  .seq (.block [.addImm .x .x0 .x21 64, .addImm .x .x1 .x22 256, .subImm .x .x2 .x23 256,
    .addImm .x .x3 .x21 128])
    (c.callWith to)

/-- `seal` but for the tag, after the prologue. -/
def sealAfter (c : XorCallee) : Prog isa :=
  .seq (.block stash)
  (.seq (first false)
  (.seq (rest c false)
  (.seq (macPad .x24 .x25)
  (.seq (.block lengths)
  (.seq (macPad .x22 .x23)
    absorbLengths)))))

/-- `open` up to the tag computed, after the prologue. -/
def openAfter (c : XorCallee) : Prog isa :=
  .seq (.block stash)
  (.seq (macPad .x24 .x25)
  (.seq (macPad .x22 .x23)
  (.seq (.block lengths)
  (.seq absorbLengths
  (.seq (first true)
  (.seq (rest c true)
    (finalizeTo 48)))))))

/-- `seal` but for the tag, for `lo ≤ len ≤ 511` (`Short.check`): the
prologue, then `Short.lean`'s code up to 256 bytes and this file's above. -/
def sealMain (c : XorCallee) : Prog isa :=
  .seq (Short.prologue c.sve)
  (.seq (.block split) (.ite (.zero .x .x9) Short.sealAfter (sealAfter c)))

/-- `open` up to the tag computed, for `lo ≤ len ≤ 511`. -/
def openMain (c : XorCallee) : Prog isa :=
  .seq (Short.prologue c.sve)
  (.seq (.block split) (.ite (.zero .x .x9) Short.openAfter (openAfter c)))

end VG.Impl.ChaCha20Poly1305.AArch64.ShortRest
