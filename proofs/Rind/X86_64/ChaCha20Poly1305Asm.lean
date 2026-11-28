import Rind.X86_64.Taint
import RindIsa.X86_64.ChaCha20Poly1305

open VG VG.X86_64 Rind.X86_64.ChaCha20Poly1305 rind.x86_64.taint

/-!
# rind's copy of aws-lc's AVX2 ChaCha20-Poly1305 seal runs in constant time

`seal_avx2_constant_time`: the program `RindIsa/X86_64/ChaCha20Poly1305.lean`
gives as `sealAvx2`, the body of rind's naked function
`low::x86_64::chacha20poly1305::seal_avx2` before its `rep ret` (`admin/prove
lean` checks that body then `rep ret` is the machine code rind's Linux
release build emits, but the trace here ends before the return's stack read
and jump), takes the same branches and accesses the same
addresses in any two runs that both finish without a fault in rind's
extension of VG's x86_64 model that agree on the arguments `rdi`, `rsi`,
`rdx`, `rcx`, `r8`, and `r9` (the output, input, length, AAD, AAD length,
and the data block's address), the stack pointer, and the constants'
address (`Pub`): whatever the key, nonce, message, and AAD. `check`
(`Rind/X86_64/Taint.lean`) shows it in a computation the kernel checks.

That the routine computes RFC 8439's seal is not yet proven: the quest
`quest/m4/verified/chacha20-poly1305-x86/aead.md` owns that.
-/

namespace rind.x86_64.chacha20poly1305asm

/-- What two runs are known to agree on at the start: `rcx`, `rdx`, `rsp`,
`rsi`, `rdi`, `r8`, and `r9`. -/
def start : Taint := ⟨2 ^ 1 + 2 ^ 2 + 2 ^ 4 + 2 ^ 6 + 2 ^ 7 + 2 ^ 8 + 2 ^ 9, false, false⟩

/-- Two states agree on the arguments, the stack pointer, and the address of
the constants. -/
def Pub (s₁ s₂ : Rind.X86_64.State) : Prop :=
  s₁.vg.gpr .rdi = s₂.vg.gpr .rdi ∧ s₁.vg.gpr .rsi = s₂.vg.gpr .rsi ∧
    s₁.vg.gpr .rdx = s₂.vg.gpr .rdx ∧ s₁.vg.gpr .rcx = s₂.vg.gpr .rcx ∧
    s₁.vg.gpr .r8 = s₂.vg.gpr .r8 ∧ s₁.vg.gpr .r9 = s₂.vg.gpr .r9 ∧
    s₁.vg.gpr .rsp = s₂.vg.gpr .rsp ∧ s₁.vg.syms constsName = s₂.vg.syms constsName

theorem agree_of_pub {s₁ s₂ : Rind.X86_64.State} (h : Pub s₁ s₂) :
    Agree [constsName] start s₁ s₂ := by
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9, hsp, hk⟩ := h
  refine ⟨fun r hr => ?_, fun hf => absurd hf (by decide), fun hf => absurd hf (by decide),
    fun n hn => ?_⟩
  · cases r <;> first | assumption | exact absurd hr (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    subst hn; exact hk

theorem check_seal_avx2 : (check [constsName] sealAvx2 start).isSome = true := by decide +kernel

/-- The AVX2 seal's trace of branches and addresses depends only on its
arguments, the stack pointer, and the constants' address. -/
theorem seal_avx2_constant_time : ConstantTime Rind.X86_64.isa (fun _ => True) Pub sealAvx2 := by
  obtain ⟨_, h⟩ := Option.isSome_iff_exists.mp check_seal_avx2
  exact fun s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hp e₁ e₂ =>
    constantTime_of_check h s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ (agree_of_pub hp) e₁ e₂

end rind.x86_64.chacha20poly1305asm

/-- info: 'rind.x86_64.chacha20poly1305asm.seal_avx2_constant_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rind.x86_64.chacha20poly1305asm.seal_avx2_constant_time
