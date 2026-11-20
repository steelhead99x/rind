module

public import VerifiedGarbage.Impl.ChaCha20.AArch64.XorCallee
public import VerifiedGarbage.Impl.Poly1305.AArch64.Radix64

/-!
# ChaCha20-Poly1305: AArch64 implementation

`vg_chacha20_poly1305_seal(key = x0, nonce = x1, aad = x2, aad_len = x3, data = x4,
len = x5, tag = x6, work = x7)`, and `open`'s body (`Stitched.lean`'s
`openCode`), with the same arguments and the destination in `x8`, which
decrypts from the data to the destination, returns `w0`, and zeroes the
destination if the tag is wrong: `vg_chacha20_poly1305_open` runs it in place
(`openInPlace`), and `vg_chacha20_poly1305_open_to` from `src` to `dst`
(`openTo`). They are composed of calls of the verified ChaCha20 and Poly1305
functions. `work` is the working space, which the artifact's frame allocates
on the stack (`withStackScratchWiped`, `withStackArgScratchWiped`): `seal`'s
is the context, `open`'s the context and 32 bytes after it, `[1280, 1312)`,
where it saves the destination and `len` (`saveData`) for the zeroing
(`zeroData`), as no register keeps them through every path of its code, and
our caller's `x28`.

The working space (1280 bytes, called the context below):

* `[0, 16)`: the lengths block;
* `[16, 32)`: the padded last block of the additional data or the data;
* `[32, 48)`: `x27` and `x28`, with the eight-block stream (`Stitched.lean`);
* `[48, 64)`: the tag computed by `open`;
* `[64, 128)`: the ChaCha20 state, built from the key and the nonce;
* `[128, 448)`: the working space of `vg_chacha20_xor` (the first 32 bytes of
  the block with counter 0 are the one-time Poly1305 key);
* `[448, 576)`: the Poly1305 state;
* `[576, 624)`: our caller's `x21`–`x25` and our return address `x30`;
* `[624, 632)`: the address of `tag`;
* `[632, 760)`: the working space of `vg_poly1305_finalize_scratch` (`scratch`);
* `[768, 1280)`: the keystream of eight blocks, for 257 to 511 bytes
  (`Pad.lean`), zeroed after it is used; when decrypting 449 to 511 bytes,
  at `[256 + len, 768 + len)` instead, in `[704, 1280)`
  (`Stitched.lean`'s `OpenPad`).

`x21` holds the context, `x22` the data, `x23` its length, `x24` the
additional data and `x25` its length throughout: they are callee-saved, and
no callee writes them (`vg_chacha20_xor` saves and restores the ones it uses,
`x19`, `x20`, `x26` and `x27`, which we therefore keep nothing in across its
calls), so they stay public for the constant-time analysis. `seal` calls
the stream in place (`XorCallee.inPlace`: its destination, `x4`, set to its
source), `open` with its destination at `x28` after the source
(`XorCallee.callWith true`): `saveData` sets `x28` to the destination's
distance from the data, which no callee writes, and which the code that
restores it from memory (the eight-block stream's, after `polyIn` saved it)
sets again from registers, so that it stays public too; `openTail` restores
our caller's. No register is left for the address of `tag` throughout (the
eight-block stream's code uses every other one), so it is saved in the
context with the registers, and loaded from there when it is needed: after
the rest (`sealMain`, `openMain`), whose analysis does not need it, by its
own block, which loads the same value in two runs. A call (`bl`) stores
nothing in memory, so no stack is used.

The model has no register-offset addressing and no flags: a padded last
block is copied a byte at a time through advancing pointers, counting down to
zero with `cbnz`, and the tags are compared without a branch, as
`1 - ((x | -x) >> 63)` of the OR of their XORs `x`.

Only the pointers and the lengths can affect timing: the branches are on the
lengths, and every address is a pointer plus a constant or a count.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.AArch64

open VG.AArch64
open VG.Impl.ChaCha20.AArch64 (XorCallee)
open VG.Impl.ChaCha20.AArch64.Xor (mov)

/-- The registers saved in the context, and where: our caller's, our return
address and `tag` (`x6`). -/
def saved : List (Reg × Nat) := [(.x22, 584), (.x23, 592), (.x24, 600), (.x25, 608), (.x30, 616),
  (.x6, 624), (.x21, 576)]

/-- Save them, with the context in `x7`. -/
def save : List Instr := saved.map fun (r, d) => .str .x r .x7 d
/-- Restore them (`x21`, the base, last; `x6` needs no restoring, but this
does no harm). -/
def restore : List Instr := saved.map fun (r, d) => .ldr .x r .x21 d

/-- The arguments moved to where they are kept. -/
def moves : List Instr := [mov .x21 .x7, mov .x24 .x2, mov .x25 .x3, mov .x22 .x4, mov .x23 .x5]

/-- The ChaCha20 constants. -/
def consts : List (BitVec 32) := [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

/-- Word `k` of the ChaCha20 state for counter 0 into `w9`: a constant (0–3),
the key (4–11, at `x0`), the counter (12) or the nonce (13–15, at `x1`). -/
def stSrc (k : Nat) : List Instr :=
  if k < 4 then
    let c := consts.getD k 0
    [.movz .w .x9 (c.extractLsb' 0 16) 0, .movk .w .x9 (c.extractLsb' 16 16) 1]
  else if k < 12 then [.ldr .w .x9 .x0 (4 * (k - 4))]
  else if k = 12 then [.movz .w .x9 0 0]
  else [.ldr .w .x9 .x1 (4 * (k - 13))]

/-- Word `k` of the ChaCha20 state, at `x21 + b + 4k`. -/
def stWAt (b k : Nat) : List Instr := stSrc k ++ ([.str .w .x9 .x21 (b + 4 * k)] : List Instr)

/-- Word `k` of the ChaCha20 state, at `x21 + 64 + 4k`. -/
def stW (k : Nat) : List Instr := stWAt 64 k

/-- The ChaCha20 state for counter 0. -/
def initState : List Instr := (List.range 16).flatMap stW

/-- Saves the registers, moves the arguments, and computes the one-time key
and the Poly1305 state for it. -/
def prologue : Prog isa :=
  .seq (.block (save ++ moves ++ initState ++ ([.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 128] : List Instr)))
  (.seq (.call "vg_chacha20_block" VG.Impl.ChaCha20.AArch64.block)
  (.seq (.block [.addImm .x .x0 .x21 448, .addImm .x .x1 .x21 128])
    (.call "vg_poly1305_init" Impl.Poly1305.AArch64.init)))

/-- Copies the `x10` (nonzero) bytes at `x1` to `x9`, advancing both. -/
def copyLoop : Prog isa :=
  .loop (.block [.ldrb .x11 .x1 0, .strb .x11 .x9 0, .addImm .x .x1 .x1 1, .addImm .x .x9 .x9 1,
    .subImm .x .x10 .x10 1]) (.nonzero .x .x10)

/-- The last `x10` bytes (1 to 15), at `x1`, padded with zeros, absorbed. -/
def padTail : Prog isa :=
  .seq (.block [.movz .x .x11 0 0, .str .x .x11 .x21 16, .str .x .x11 .x21 24,
    .addImm .x .x9 .x21 16])
  (.seq copyLoop
  (.seq (.block [.addImm .x .x0 .x21 448, .addImm .x .x1 .x21 16, .movz .x .x2 1 0])
    (.call "vg_poly1305_blocks" Impl.Poly1305.AArch64.Radix64.blocks)))

/-- The `n` bytes at `p`, padded with zeros to a multiple of 16, absorbed. -/
def macPad (p n : Reg) : Prog isa :=
  .seq (.block [.addImm .x .x0 .x21 448, mov .x1 p, .lsr .x .x2 n 4])
  (.seq (.call "vg_poly1305_blocks" Impl.Poly1305.AArch64.Radix64.blocks)
  (.seq (.block [.lsl .x .x10 n 60, .lsr .x .x10 .x10 60])
    (.ite (.zero .x .x10) (.block [])
      (.seq (.block [.sub .x .x9 n .x10, .add .x .x1 p .x9]) padTail))))

/-- The ChaCha20 counter set to 1, and the data encrypted or decrypted into its
destination (`XorCallee.callWith to`). -/
def cryptWith (c : XorCallee) (to : Bool) : Prog isa :=
  .seq (.block [.movz .w .x9 1 0, .str .w .x9 .x21 112, .addImm .x .x0 .x21 64, mov .x1 .x22,
    mov .x2 .x23, .addImm .x .x3 .x21 128])
    (c.callWith to)

/-- The lengths block. -/
def lengths : List Instr := [.str .x .x25 .x21 0, .str .x .x23 .x21 8]

/-- The lengths block absorbed. -/
def absorbLengths : Prog isa :=
  .seq (.block [.addImm .x .x0 .x21 448, .addImm .x .x1 .x21 0, .movz .x .x2 1 0])
    (.call "vg_poly1305_blocks" Impl.Poly1305.AArch64.Radix64.blocks)

/-- The tag written to `x21 + out`: the message is whole blocks, so its
length (`count`) is 0 modulo 16, and nothing is buffered. -/
def finalizeTo (out : Nat) : Prog isa :=
  .seq (.block [.addImm .x .x0 .x21 448, .movz .x .x1 0 0, .addImm .x .x2 .x21 out,
    .addImm .x .x3 .x21 632])
    (.call "vg_poly1305_finalize_scratch" Impl.Poly1305.AArch64.Radix64.finalize)

/-- The tag written to `x2` (`tag`). -/
def finalizeTag : Prog isa :=
  .seq (.block [.addImm .x .x0 .x21 448, .movz .x .x1 0 0, .addImm .x .x3 .x21 632])
    (.call "vg_poly1305_finalize_scratch" Impl.Poly1305.AArch64.Radix64.finalize)

/-- `seal` but for the tag, with `crypt` encrypting the data. -/
def sealMainWith (crypt : Prog isa) : Prog isa :=
  .seq prologue
  (.seq (macPad .x24 .x25)
  (.seq (.block lengths)
  (.seq crypt
  (.seq (macPad .x22 .x23)
    absorbLengths))))

def sealMain (c : XorCallee) : Prog isa := sealMainWith (cryptWith c false)

/-- The tag written to `tag`, whose address is loaded from the context, and
the registers restored. -/
def sealTail : Prog isa :=
  .seq (.block [.ldr .x .x2 .x21 624]) (.seq finalizeTag (.block restore))

def sealWith (c : XorCallee) : Prog isa := .seq (sealMain c) sealTail

/-- `x0 = 1` if the computed tag (at `x21 + 48`) is the received one (at
`x12`), else 0, without a branch: with `x` the OR of the XORs of their
words, `(x | -x) >> 63` is 0 if `x = 0` and 1 otherwise. -/
def compare : List Instr :=
  [.ldr .x .x9 .x21 48, .ldr .x .x10 .x12 0, .logic .eor .x .x9 .x9 .x10,
   .ldr .x .x10 .x21 56, .ldr .x .x11 .x12 8, .logic .eor .x .x10 .x10 .x11,
   .logic .orr .x .x9 .x9 .x10,
   .movz .x .x10 0 0, .sub .x .x10 .x10 .x9, .logic .orr .x .x9 .x9 .x10, .lsr .x .x9 .x9 63,
   .movz .x .x10 1 0, .sub .x .x0 .x10 .x9]

/-- `open` up to the tag computed, with `crypt` decrypting the data. -/
def openMainWith (crypt : Prog isa) : Prog isa :=
  .seq prologue
  (.seq (macPad .x24 .x25)
  (.seq (macPad .x22 .x23)
  (.seq (.block lengths)
  (.seq absorbLengths
  (.seq crypt
    (finalizeTo 48))))))

def openMain (c : XorCallee) : Prog isa := openMainWith (cryptWith c true)

/-- `open`'s destination (`x8`), `len` and our caller's `x28` saved after the
context, at `work + 1280`, and `x28` set to the destination's distance from
the data (`x4`), which the code adds to the data's addresses to write the
plaintext (`XorCallee.callWith true`, `Short.dstOf true`). -/
def saveData : List Instr :=
  [.str .x .x8 .x7 1280, .str .x .x5 .x7 1288, .str .x .x28 .x7 1296, .sub .x .x28 .x8 .x4]

/-- The destination into `x9` and `len` into `x10`, from after the context,
and zero into `x11`. -/
def zeroLoad : List Instr := [.ldr .x .x9 .x21 1280, .ldr .x .x10 .x21 1288, .movz .x .x11 0 0]

/-- The `x10` bytes at `x9` zeroed, a byte at a time. -/
def zeroLoop : Prog isa :=
  .ite (.zero .x .x10) (.block [])
    (.loop (.block [.strb .x11 .x9 0, .addImm .x .x9 .x9 1, .subImm .x .x10 .x10 1])
      (.nonzero .x .x10))

/-- The `len` bytes at the destination, loaded from after the context, zeroed. -/
def zeroData : Prog isa := .seq (.block zeroLoad) zeroLoop

/-- The tags compared, with the address of `tag` loaded from the context,
the destination zeroed if they differ, and the registers restored, `x28` from
after the context. -/
def openTail : Prog isa :=
  .seq (.block [.ldr .x .x12 .x21 624])
  (.seq (.block compare)
  (.seq (.ite (.zero .w .x0) zeroData (.block []))
    (.block (.ldr .x .x28 .x21 1296 :: restore))))

def «seal» := sealWith .scalar

end VG.Impl.ChaCha20Poly1305.AArch64
