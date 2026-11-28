module

public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Proof.Framework.UnfoldStep
public meta import VerifiedGarbage.Proof.Framework.UnfoldStep

/-!
# x86-64: the model's functions on constructors, without their equation lemmas

Each `dsimproc` here unfolds a function of the model applied to arguments
given by their constructors (`unfoldStep?`): pass it to `simp` in place of
the function (`reduceExec` for `exec`, `reduceInstrDst` for `Instr.dst`, `reduceXBinOpEval` for `XBinOp.eval`, `reduceVBinOpSse` for `VBinOp.sse`, `reduceVOpExec` for `VOp.exec`). Unlike the function's equation lemmas, it realizes
nothing in the module that uses it.
-/

public meta section

namespace VG.X86_64

/-- `exec` unfolded on constructors (see `unfoldStep?`). -/
dsimproc reduceExec (exec _ _) := fun e => do
  let some e' ← unfoldStep? e | return .continue
  return .visit e'

/-- `Instr.dst` unfolded on constructors (see `unfoldStep?`). -/
dsimproc reduceInstrDst (Instr.dst _) := fun e => do
  let some e' ← unfoldStep? e | return .continue
  return .visit e'

/-- `XBinOp.eval` unfolded on constructors (see `unfoldStep?`). -/
dsimproc reduceXBinOpEval (XBinOp.eval _ _ _) := fun e => do
  let some e' ← unfoldStep? e | return .continue
  return .visit e'

/-- `VBinOp.sse` unfolded on constructors (see `unfoldStep?`). -/
dsimproc reduceVBinOpSse (VBinOp.sse _) := fun e => do
  let some e' ← unfoldStep? e | return .continue
  return .visit e'

/-- `VOp.exec` unfolded on constructors (see `unfoldStep?`). -/
dsimproc reduceVOpExec (VOp.exec _ _) := fun e => do
  let some e' ← unfoldStep? e | return .continue
  return .visit e'

end VG.X86_64
