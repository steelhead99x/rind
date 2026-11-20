import Cosim.Progs
import VerifiedGarbage.TCB.AArch64.Print

/-!
# `vg-print`

`vg-print aarch64` prints, for each routine of `Cosim.Progs` and each
function it calls (`Code.call`, `Code.icall`, whose callee's code is part of
the `Prog` the proofs are about, though its caller's printed text only names
it), VG's printer's text of that function, as VG's assembly file
(`TCB/Rust.lean`'s `assembly`) has it: a line `function <name>`, then each
line of its text after a tab. It fails if two calls name one function with
different text. `admin/vg-bytes` checks that this is VG's assembly text of
each function, and so that VG's assembly files are the printed text of the
`Prog`s that rind's axioms are about; rind's machine code is checked against
that text.
-/

open VG

/-- The assembly file's lines of a function's printed lines
(`Rust.assembly`): a comment line, the text of an instruction the printer
emits as its machine code, stands for its directive after it. -/
def asmLines (call : String) : List Line → Bool → List String
  | [], _ => []
  | l :: ls, after =>
    let dir := match l with | .text s => s.startsWith "." | _ => false
    if after && dir then asmLines call ls false
    else match l with
      | .text s =>
        if s.startsWith "// " && !s.contains '\n' && !s.contains '\r' then
          (s.drop 3).toString :: asmLines call ls true
        else s :: asmLines call ls false
      | .call n => (call ++ " {" ++ n ++ "}") :: asmLines call ls false
      | .sym s _ n => (s ++ "{" ++ n ++ "}") :: asmLines call ls false

/-- Every function a code calls, with its code, the callers' first. -/
partial def callees {I C : Type} : Code I C → List (String × Code I C)
  | .block _ => []
  | .seq a b => callees a ++ callees b
  | .ite _ t e => callees t ++ callees e
  | .loop b _ => callees b
  | .call n b => (n, b) :: callees b
  | .frame _ b _ => callees b
  | .icall _ n b next => (n, b) :: callees b ++ callees next

def main (args : List String) : IO UInt32 := do
  unless args == ["aarch64"] do
    IO.eprintln "usage: vg-print aarch64"
    return 2
  let P := (inferInstance : Emitter AArch64.isa).printer
  let routines : List (String × Prog AArch64.isa) :=
    [("vg_chacha20_poly1305_seal_sve2", Cosim.Progs.chacha20Poly1305SealSve2),
     ("vg_chacha20_poly1305_open_sve2", Cosim.Progs.chacha20Poly1305OpenSve2)]
  let mut seen : List (String × List String) := []
  let mut failed := false
  for (name, code) in routines ++ routines.flatMap fun (_, c) => callees c do
    let text := asmLines P.call (P.function code) false
    match seen.lookup name with
    | some t =>
      if t != text then
        IO.eprintln s!"vg-print: {name} is two functions with different text"
        failed := true
    | none =>
      seen := seen ++ [(name, text)]
      IO.println s!"function {name}"
      for l in text do
        IO.println s!"\t{l}"
  return if failed then 1 else 0
