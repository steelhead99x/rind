module

public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# Returning without secret residue (x86-64)

**Trusted.** What it means for a function to leave no secret where its Rust
caller cannot clear it. The caller owns its buffers (Rust objects, which it
wipes itself, `src/zeroize.rs`) and the result; it cannot reach what the
function leaves in registers, in the flags, in MXCSR, or in the stack below
its stack pointer, where the function's frames and its calls' return
addresses were.

`NoResidue c k retBits` is a property of two runs, as `ConstantTime` is: any
two runs of `c` from states that satisfy `k.pre`, agree on what `k.pub` says
is public, and agree on everything outside the buffers (`Outside 0`), end in
states that agree on everything outside the buffers but the result
(`Outside retBits`). What the function leaves there is therefore a function
of what its caller left there and of public data, and of nothing else: not
of the contents of its buffers that are not public. It is the same whether
the function clears a location or leaves in it what was there on entry, so
no choice of what to keep (zero, or the entry value) can carry a secret.

The runs must also end with every flag defined (`FlagsDefined`). A flag the
model leaves undefined (`none`, see `TCB/X86_64/Isa.lean`) is not a value the
two runs share: `none` only says that the SDM does not say what the
instruction leaves there ("The SF, ZF, AF, and PF flags are undefined", of
`MUL` and `IMUL`), and a processor may leave something that depends on the
instruction's operands, as those that set SF and ZF from the product do. Two
undefined flags are equal in the model, so `Outside` alone would accept
them: an undefined flag on return counts as residue instead, whatever was
computed.

What was there on entry (all of the registers, and the memory outside the
buffers) is taken as given: a secret the caller passed in a register, or
left in one, is the caller's. So are the return addresses the code's calls
push (`State.unknowns`), which the two runs share: they are where the code
is, not data. So is what replaces the bytes of a frame the function released
(`lose`, `TCB/X86_64/Isa.lean`): the unknowns say which bytes are replaced
and by what, the same in both runs, so a byte that is not replaced is
compared as the function left it, and a frame that held a secret must
still be wiped.

Not covered, because the model does not have them: the opmask register `k1`
(which the masked AVX-512 moves set from a general-purpose register), the
parity and adjust flags, and microarchitectural state.
-/

@[expose] public section

namespace VG.X86_64

/-- Two states agree on everything outside the buffers: on which regions
the code may read and write, every general-purpose register (but the low
`retBits` bits of `rax`, the result), the flags, every vector register,
MXCSR, and every byte of memory outside those regions. -/
def Outside (retBits : Nat) (s₁ s₂ : State) : Prop :=
  s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧
  (∀ r, r ≠ .rax → s₁.gpr r = s₂.gpr r) ∧
  s₁.gpr .rax >>> retBits = s₂.gpr .rax >>> retBits ∧
  s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of ∧
  s₁.xmm = s₂.xmm ∧ s₁.ymmHi = s₂.ymmHi ∧ s₁.zmmHi = s₂.zmmHi ∧
  s₁.ymmH = s₂.ymmH ∧ s₁.zmmHiH = s₂.zmmHiH ∧ s₁.mxcsr = s₂.mxcsr ∧
  ∀ x, (∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1) → s₁.mem x = s₂.mem x

/-- Every flag is defined: none is one an instruction left undefined
(`none`), which a processor may have set from that instruction's operands. -/
def FlagsDefined (s : State) : Prop :=
  s.cf ≠ none ∧ s.zf ≠ none ∧ s.sf ≠ none ∧ s.of ≠ none

/-- `c`, with contract `k` and a result of `retBits` bits, returns without
secret residue (see the module docs). The flags of the second run are
defined too: `Outside` makes them those of the first. -/
def NoResidue (c : Prog isa) (k : Contract isa) (retBits : Nat) : Prop :=
  ∀ s₁ s₂ t₁ t₂ s₁' s₂', k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ →
    s₁.unknowns = s₂.unknowns →
    Exec isa c s₁ t₁ s₁' → Exec isa c s₂ t₂ s₂' → Outside retBits s₁' s₂' ∧ FlagsDefined s₁'

end VG.X86_64
