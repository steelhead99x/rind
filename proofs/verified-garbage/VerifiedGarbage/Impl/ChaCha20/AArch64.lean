module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# ChaCha20 block function: AArch64 implementation

`vg_chacha20_block(state = x0, buf = x1)`.

* Word `k` of the state lives in `w(k + 2)` (`x2`–`x17`) throughout; the ten
  double rounds are fully unrolled.
* Only caller-saved registers are used, and only the first 64 bytes of `buf`
  are written, so nothing is saved and no scratch space is needed.
* The input state is re-read from `state` to add it at the end, using `w2`
  (then `w3`) as a temporary once word 0 has been stored.
* Every address is `x0` or `x1` plus a constant, and there are no branches,
  so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.AArch64

open VG.AArch64

/-- The register holding word `k`. -/
def wreg (k : Nat) : Reg :=
  [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17].getD k .x2

/-- The quarter round (RFC 8439 §2.1) on `wa, wb, wc, wd`. A rotation left by
`k` is a rotation right by `32 - k`. -/
def qr (a b c d : Reg) : List Instr := [
  .add .w a a b, .logic .eor .w d d a, .ror .w d d 16,
  .add .w c c d, .logic .eor .w b b c, .ror .w b b 20,
  .add .w a a b, .logic .eor .w d d a, .ror .w d d 24,
  .add .w c c d, .logic .eor .w b b c, .ror .w b b 25]

/-- `QUARTERROUND(x, y, z, w)` (RFC 8439 §2.2). -/
def quarter (x y z w : Nat) : Prog isa := .block (qr (wreg x) (wreg y) (wreg z) (wreg w))

/-- `inner_block` (RFC 8439 §2.3.1): a column round and a diagonal round. -/
def doubleRound : Prog isa :=
  .seq (quarter 0 4 8 12) <| .seq (quarter 1 5 9 13) <| .seq (quarter 2 6 10 14) <|
  .seq (quarter 3 7 11 15) <| .seq (quarter 0 5 10 15) <| .seq (quarter 1 6 11 12) <|
  .seq (quarter 2 7 8 13) (quarter 3 4 9 14)

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

/-- Load the state into the registers. -/
def load : List Instr := (List.range 16).flatMap fun k => [.ldr .w (wreg k) .x0 (4 * k)]

/-- Add input word `k` (via `w2`) and store output word `k`. -/
def addWord (k : Nat) : List Instr :=
  [.ldr .w .x2 .x0 (4 * k), .add .w (wreg k) (wreg k) .x2, .str .w (wreg k) .x1 (4 * k)]

/-- Store word 0 to free `w2`, finish words 1–15, then finish word 0. -/
def finish : List Instr :=
  ([.str .w .x2 .x1 0] : List Instr) ++ (List.range 15).flatMap (fun i => addWord (i + 1)) ++
  ([.ldr .w .x2 .x0 0, .ldr .w .x3 .x1 0, .add .w .x2 .x3 .x2, .str .w .x2 .x1 0] : List Instr)

def block : Prog isa := .seq (.block load) (.seq (rounds 10) (.block finish))

end VG.Impl.ChaCha20.AArch64
