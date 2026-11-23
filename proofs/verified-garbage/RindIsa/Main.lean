import RindIsa.Proven

/-!
# `rind-asm`

Prints the machine code of each function rind proves in its model of
AArch64, and the statics it reads, for `admin/prove lean` to compare with
rind's build: for each, a line `function <Rust path>`, then one line
`insn <word>` for each instruction word, in hex, one `reloc <byte offset>
<type> <symbol>` for each relocation, and one `static <symbol> <Rust path>
<bytes>` for each static, the bytes it must begin with, in hex.
-/

open Rind.AArch64

def hex (n w : Nat) : String :=
  let ds := Nat.toDigits 16 (w % 2 ^ (4 * n))
  String.ofList (List.replicate (n - ds.length) '0' ++ ds)

/-- The little-endian bytes of `ws`, in hex. -/
def leHex (ws : List (BitVec 32)) : String :=
  String.join (ws.map fun w => String.join ((List.range 4).map fun i => hex 2 (w.toNat >>> (8 * i))))

def main : IO UInt32 := do
  for p in proven do
    let some (ws, rs) := function p.prog
      | IO.eprintln s!"rind-asm: {p.path} does not encode"; return 1
    IO.println s!"function {p.path}"
    for w in ws do
      IO.println s!"insn {hex 8 w}"
    for r in rs do
      IO.println s!"reloc {r.off} {r.type} {r.sym}"
    for (sym, path, words) in p.statics do
      IO.println s!"static {sym} {path} {leHex words}"
  return 0
