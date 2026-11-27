import Cosim.Progs
import Cosim.ProgsX86_64
import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.X86_64.Print

/-!
# `vg-print`

`vg-print aarch64` and `vg-print x86_64` print, for each routine of `Cosim.Progs` and each
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

/-- Prints each routine of `routines` and each function it calls, as the
module doc describes: `false` if two calls name one function with different
text. -/
def printRoutines {M : ISA} [Emitter M] (routines : List (String × Prog M)) : IO Bool := do
  let P := (inferInstance : Emitter M).printer
  let mut seen : List (String × List String) := []
  let mut ok := true
  for (name, code) in routines ++ routines.flatMap fun (_, c) => c.calls do
    let text := asmLines P.call (P.function code) false
    match seen.lookup name with
    | some t =>
      if t != text then
        IO.eprintln s!"vg-print: {name} is two functions with different text"
        ok := false
    | none =>
      seen := seen ++ [(name, text)]
      IO.println s!"function {name}"
      for l in text do
        IO.println s!"\t{l}"
  return ok

def aarch64Routines : List (String × Prog AArch64.isa) :=
  [("vg_chacha20_poly1305_seal_sve2", Cosim.Progs.chacha20Poly1305SealSve2),
   ("vg_chacha20_poly1305_open_sve2", Cosim.Progs.chacha20Poly1305OpenSve2)]

def x86_64Routines : List (String × Prog X86_64.isa) :=
  [("vg_mlkem768_keygen_avx512", Cosim.ProgsX86_64.keygenAvx512),
   ("vg_mlkem768_encaps_h_avx512", Cosim.ProgsX86_64.encapsHAvx512),
   ("vg_mlkem768_encaps_avx512", Cosim.ProgsX86_64.encapsAvx512),
   ("vg_mlkem768_decaps_avx512", Cosim.ProgsX86_64.decapsAvx512),
   ("vg_mlkem768_encaps_avx2", Cosim.ProgsX86_64.encapsAvx2),
   ("vg_mlkem768_encaps_h_avx2", Cosim.ProgsX86_64.encapsHAvx2),
   ("vg_mlkem768_encaps_avx", Cosim.ProgsX86_64.encapsAvx),
   ("vg_mlkem768_encaps_h_avx", Cosim.ProgsX86_64.encapsHAvx),
   ("vg_mlkem768_encaps", Cosim.ProgsX86_64.encapsBase),
   ("vg_mlkem768_encaps_h", Cosim.ProgsX86_64.encapsHBase)]

def main (args : List String) : IO UInt32 := do
  let ok ← if args == ["aarch64"] then printRoutines aarch64Routines
    else if args == ["x86_64"] then printRoutines x86_64Routines
    else do
      IO.eprintln "usage: vg-print aarch64 | x86_64"
      return 2
  return if ok then 0 else 1
