import RindIsa.Proven

/-!
# `rind-asm`

Prints the machine code of each function rind proves in its model of the
target its argument names, `aarch64` or `x86_64`, and the statics it reads,
for `admin/prove lean` to compare with rind's build: for each, a line
`function <Rust path>`, then on aarch64 one line `insn <word>` for each
instruction word, in hex, one `reloc <byte offset> <type> <symbol>` for each
relocation, and one `static <symbol> <Rust path> <bytes>` for each static,
the bytes it must begin with, in hex; on x86_64 one line `text <offset>
<bytes>` for each 16 bytes of its section, in hex.
-/

def hex (n w : Nat) : String :=
  let ds := Nat.toDigits 16 (w % 2 ^ (4 * n))
  String.ofList (List.replicate (n - ds.length) '0' ++ ds)

/-- The little-endian bytes of `ws`, in hex. -/
def leHex (ws : List (BitVec 32)) : String :=
  String.join (ws.map fun w => String.join ((List.range 4).map fun i => hex 2 (w.toNat >>> (8 * i))))

def aarch64 : IO UInt32 := do
  for p in Rind.AArch64.proven do
    let some (ws, rs) := Rind.AArch64.function p.prog
      | IO.eprintln s!"rind-asm: {p.path} does not encode"; return 1
    IO.println s!"function {p.path}"
    for w in ws do
      IO.println s!"insn {hex 8 w}"
    for r in rs do
      IO.println s!"reloc {r.off} {r.type} {r.sym}"
    for (sym, path, words) in p.statics do
      IO.println s!"static {sym} {path} {leHex words}"
  return 0

def x86_64 : IO UInt32 := do
  for p in Rind.X86_64.proven do
    let some bs := Rind.X86_64.function p.prog
      | IO.eprintln s!"rind-asm: {p.path} does not encode"; return 1
    IO.println s!"function {p.path}"
    for i in List.range ((bs.length + 15) / 16) do
      IO.println s!"text {hex 4 (16 * i)} {String.join (((bs.drop (16 * i)).take 16).map (hex 2))}"
  return 0

def main : List String → IO UInt32
  | ["aarch64"] => aarch64
  | ["x86_64"] => x86_64
  | _ => do IO.eprintln "usage: rind-asm aarch64 | x86_64"; return 2
