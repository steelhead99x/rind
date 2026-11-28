module

public import VerifiedGarbage.Impl.ChaCha20.AArch64.Callee

/-!
# ChaCha20 keystream XOR: AArch64 implementation

`vg_chacha20_xor(state = x0, src = x1, len = x2, buf = x3, dst = x4)`:
the `len` bytes at `src` XORed with the keystream, written to `dst`, which is
`src` itself or apart from it.

For each 64 bytes of the source (the last piece may be shorter),
`vg_chacha20_block(state, buf)` is called, the first `n = min(64, remaining)`
bytes of its output (the first 64 bytes of `buf`) are XORed with the source
into the destination a byte at a time, each source byte loaded before the
destination's is stored, and the block counter (word 12 of the state) is
incremented modulo 2³².

The block function takes `state` in `x0` and `buf` in `x1`, and writes
neither (it writes only `x2`–`x17`, and a call changes `x16`, `x17` and
`x30`), so they stay there throughout, and on return `x0` is `state` and
`x1` is `buf`. The data not yet processed and its length are kept across the
calls in `x19` and `x20`, and the destination in `x27`, which the block
function preserves. Our caller's values of those, and our return address
(`x30`, which each call replaces), are saved in `buf[256, 288)`, which is not
passed to the block function; so no stack is used.

The model has no register-offset addressing: the source is consumed through
`x19` and the destination through `x27`, which advance, and the keystream
through `x7 = buf + i`. It has no
flags either: `remaining < 64` iff `remaining >> 6 = 0`, and the loops count
down to zero, tested with `cbz`/`cbnz`. The branches are on the length only,
and every address is a pointer plus a constant or a count, so only the
pointers and the length can affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.AArch64.Xor

open VG.AArch64
open VG.Impl.ChaCha20.AArch64 (Callee)

/-- `mov d, n` (as `add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- The registers saved in `buf`, and where. -/
def saved : List (Reg × Nat) := [(.x19, 256), (.x20, 264), (.x30, 272), (.x27, 280)]

/-- Save them, with `buf` in `x3`. -/
def save : List Instr := saved.map fun (r, d) => .str .x r .x3 d
/-- Restore them, with `buf` in `x1`. -/
def restore : List Instr := saved.map fun (r, d) => .ldr .x r .x1 d

/-- XORs the next `x2` bytes of the source (at `x19`) with the keystream
(from `x7`) into the destination (at `x27`), advancing all three. -/
def xorLoop : Prog isa :=
  .loop (.block [.ldrb .x6 .x19 0, .ldrb .x8 .x7 0, .logic .eor .w .x6 .x6 .x8, .strb .x6 .x27 0,
    .addImm .x .x19 .x19 1, .addImm .x .x27 .x27 1, .addImm .x .x7 .x7 1, .subImm .x .x2 .x2 1])
    (.nonzero .x .x2)

/-- One block: the keystream into `buf`, `x2 = min(64, x20)` bytes of it
XORed with the source into the destination, and the counter incremented. -/
def bodyWith (c : Callee) : Prog isa :=
  .seq (.call c.name c.code)
  (.seq (.block [.lsr .x .x9 .x20 6, mov .x2 .x20])
  (.seq (.ite (.zero .x .x9) (.block []) (.block [.movz .x .x2 64 0]))
  (.seq (.block [.sub .x .x20 .x20 .x2, mov .x7 .x1])
  (.seq xorLoop
    (.block [.ldr .w .x3 .x0 48, .addImm .w .x3 .x3 1, .str .w .x3 .x0 48])))))

def xorWith (c : Callee) : Prog isa :=
  .seq (.block (save ++ [mov .x19 .x1, mov .x20 .x2, mov .x27 .x4, mov .x1 .x3]))
  (.seq (.ite (.zero .x .x20) (.block []) (.loop (bodyWith c) (.nonzero .x .x20)))
    (.block restore))

def xor := xorWith .scalar

end VG.Impl.ChaCha20.AArch64.Xor
