module

public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# Returning without secret residue (AArch64)

**Trusted.** What it means for a function to leave no secret where its Rust
caller cannot clear it, as on x86-64 (`TCB/X86_64/Residue.lean`). The caller
owns its buffers (Rust objects, which it wipes itself, `src/zeroize.rs`) and
the result; it cannot reach what the function leaves in registers, in the
condition flags, in PSTATE.DIT, or in the stack below its stack pointer,
where the function's frames were.

`NoResidue c k retBits` is a property of two runs, as `ConstantTime` is: any
two runs of `c` from states that satisfy `k.pre`, agree on what `k.pub` says
is public, and agree on everything outside the buffers (`Outside 0`), end in
states that agree on everything outside the buffers but the result
(`Outside retBits`). What the function leaves there is therefore a function
of what its caller left there and of public data, and of nothing else: not
of the contents of its buffers that are not public. It is the same whether
the function clears a location or leaves in it what was there on entry, so
no choice of what to keep (zero, or the entry value) can carry a secret.

`Outside` names every register the model has, not only the ones a callee
may change. AAPCS64 §6.1.1 makes `x0`–`x17` caller-saved (`x0`–`x7` the
argument and result registers, `x8` the indirect result register, `x9`–`x15`
temporaries, `x16` and `x17` the intra-procedure-call scratch registers IP0
and IP1), and the condition flags undefined on return; §6.1.2 makes
`v0`–`v7` and `v16`–`v31`, and the upper 64 bits of `v8`–`v15`, caller-saved:
these are where a secret can be left. The callee-saved registers (`x19`–`x28`,
`x30`, `sp` and the low 64 bits of `v8`–`v15`) are what they were on entry
(`abiPreserved`), so the two runs agree on them anyway. The result is in
`x0` (AAPCS64, "Result Return"), whose low `retBits` bits only may differ.
See https://github.com/ARM-software/abi-aa/blob/2025Q4/aapcs64/aapcs64.rst.

What was there on entry (all of the registers, and the memory outside the
buffers) is taken as given: a secret the caller passed in a register, or
left in one, is the caller's. So are the return addresses the code's calls
leave in `x30`, and what a linker veneer may leave in `x16`, `x17` and the
flags (`State.unknowns`), which the two runs share: they are where the code
is, not data. So is what replaces the bytes of a frame the function released
(`lose`, `TCB/AArch64/Isa.lean`): the unknowns say which bytes are replaced
and by what, the same in both runs, so a byte that is not replaced is
compared as the function left it, and a frame that held a secret must
still be wiped.

Not covered, because the model does not have them: `x18` and `x29` (which
no modelled instruction changes, see `TCB/AArch64/Target.lean`), FPCR and
FPSR (which no modelled instruction reads or writes), the SVE and SME
registers, and microarchitectural state.
-/

@[expose] public section

namespace VG.AArch64

/-- Two states agree on everything outside the buffers: on which regions
the code may read and write, every general-purpose register (but the low
`retBits` bits of `x0`, the result), the stack pointer, the condition flags,
PSTATE.DIT, every SIMD and floating-point register, and every byte of memory
outside those regions. -/
def Outside (retBits : Nat) (s₁ s₂ : State) : Prop :=
  s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧
  (∀ r, r ≠ .x0 → s₁.gpr r = s₂.gpr r) ∧
  s₁.gpr .x0 >>> retBits = s₂.gpr .x0 >>> retBits ∧
  s₁.sp = s₂.sp ∧
  s₁.c = s₂.c ∧ s₁.nf = s₂.nf ∧ s₁.zf = s₂.zf ∧ s₁.vf = s₂.vf ∧ s₁.dit = s₂.dit ∧
  s₁.v = s₂.v ∧
  ∀ x, (∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1) → s₁.mem x = s₂.mem x

/-- `c`, with contract `k` and a result of `retBits` bits, returns without
secret residue (see the module docs). -/
def NoResidue (c : Prog isa) (k : Contract isa) (retBits : Nat) : Prop :=
  ∀ s₁ s₂ t₁ t₂ s₁' s₂', k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ →
    s₁.unknowns = s₂.unknowns →
    Exec isa c s₁ t₁ s₁' → Exec isa c s₂ t₂ s₂' → Outside retBits s₁' s₂'

end VG.AArch64
