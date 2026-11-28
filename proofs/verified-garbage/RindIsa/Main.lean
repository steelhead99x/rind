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
<bytes>` for each 16 bytes of its section, in hex, one `reloc <byte offset>
<type> <symbol><addend>` for each relocation, its addend as `llvm-objdump`
prints it (`-0x4`), and the statics as on aarch64, a call's relocation
naming the callee by its Rust path. It fails if an instruction reads a
static the function does not list with its words, or if a call is of other
than a function it proves, by the same program.
-/

def hex (n w : Nat) : String :=
  let ds := Nat.toDigits 16 (w % 2 ^ (4 * n))
  String.ofList (List.replicate (n - ds.length) '0' ++ ds)

/-- The little-endian bytes of `ws`, `n` bytes each, in hex. -/
def leHex {w : Nat} (n : Nat) (ws : List (BitVec w)) : String :=
  String.join (ws.map fun x => String.join ((List.range n).map fun i => hex 2 (x.toNat >>> (8 * i))))

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
      IO.println s!"static {sym} {path} {leHex 4 words}"
  return 0

/-- A relocation's addend as `llvm-objdump -r` prints it after its target:
`+0x6c`, `-0x4`, or nothing for 0. -/
def addend (a : Int) : String :=
  let h := String.ofList (Nat.toDigits 16 a.natAbs)
  if a < 0 then s!"-0x{h}" else if a = 0 then "" else s!"+0x{h}"

/-- The calls in `c`: each callee's name and program. -/
def calls : VG.Prog Rind.X86_64.isa → List (String × VG.Prog Rind.X86_64.isa)
  | .seq a b | .ite _ a b => calls a ++ calls b
  | .loop b _ => calls b
  | .call n b => [(n, b)]
  | _ => []

def x86_64 : IO UInt32 := do
  for p in Rind.X86_64.proven do
    let some (bs, rs) := Rind.X86_64.function p.prog p.ret
      | IO.eprintln s!"rind-asm: {p.path} does not encode"; return 1
    for (name, ws) in Rind.X86_64.statics p.prog do
      unless p.statics.any fun (n, _, ws') => n == name && ws' == ws do
        IO.eprintln s!"rind-asm: {p.path} reads {name}, which it does not list with those words"; return 1
    for (n, b) in calls p.prog do
      let some q := Rind.X86_64.proven.find? (·.path == n)
        | IO.eprintln s!"rind-asm: {p.path} calls {n}, which rind does not prove"; return 1
      if (Rind.X86_64.function b q.ret).map (·.1) != (Rind.X86_64.function q.prog q.ret).map (·.1) then
        IO.eprintln s!"rind-asm: {p.path} calls {n} as a program other than its own"; return 1
    IO.println s!"function {p.path}"
    for i in List.range ((bs.length + 15) / 16) do
      IO.println s!"text {hex 4 (16 * i)} {String.join (((bs.drop (16 * i)).take 16).map (hex 2))}"
    for r in rs do
      IO.println s!"reloc {r.off} {r.type} {r.sym}{addend r.addend}"
    for (sym, path, words) in p.statics do
      IO.println s!"static {sym} {path} {leHex 8 words}"
  return 0

def main : List String → IO UInt32
  | ["aarch64"] => aarch64
  | ["x86_64"] => x86_64
  | _ => do IO.eprintln "usage: rind-asm aarch64 | x86_64"; return 2
