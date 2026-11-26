module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# x86-64: code that does not touch the vector registers

`scalCode` holds of code whose every instruction is one of a few scalar ones
(`scalarI`). `Proof/Framework/X86_64/VecKeep.lean` proves that such code
leaves the vector registers as they are; code may choose by it how to run
vector code beside scalar code (the comb's pipelined selection,
`TCombCfg.combJ`).
-/

@[expose] public section

namespace VG.X86_64

/-- The instructions that write only general-purpose registers, flags and memory, and
read nothing else but, for `movq r64, xmm`, an SSE register. -/
def scalarI : Instr → Bool
  | .mov .. | .store .. | .alu .. | .mov32 .. | .movzx8 .. | .movzx16 .. | .movImm64 .. | .leaSym .. | .mul ..
  | .store8 .. | .shift .. | .mulx .. | .adcx .. | .adox .. | .cmov .. | .alu32 .. | .imul .. | .bswap ..
  | .store32 .. | .store16 .. | .bswap32 .. | .movqR .. => true
  | _ => false

/-- Whether every instruction of `c`, and of the functions it calls, is in
`scalarI`, with no frames: a call and its return change only `rsp` and
memory. -/
def scalCode : Prog isa → Bool
  | .block is => is.all scalarI
  | .seq a b => scalCode a && scalCode b
  | .ite _ a b => scalCode a && scalCode b
  | .loop b _ => scalCode b
  | .call _ b => scalCode b
  | _ => false

end VG.X86_64
