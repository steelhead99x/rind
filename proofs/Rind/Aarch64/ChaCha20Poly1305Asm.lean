import Rind.Aarch64.Taint
import RindIsa.AArch64.ChaCha20Poly1305

open VG VG.AArch64 Rind.AArch64.ChaCha20Poly1305 rind.aarch64.taint

/-!
# rind's copy of aws-lc's NEON ChaCha20-Poly1305 seal and open run in constant time

`seal_constant_time` and `open_constant_time`: the programs
`RindIsa/AArch64/ChaCha20Poly1305.lean` gives as `sealProg` and `openProg`,
which `admin/prove lean` checks are the machine code of rind's naked
functions `low::aarch64::chacha20poly1305::chacha20_poly1305_seal` and
`chacha20_poly1305_open` as rind's Linux release build emits them, take the
same branches and access the same addresses in any two runs that both finish
without a fault in rind's extension of VG's AArch64 model that agree on the
arguments `x0`–`x5` (the
output, input, length, AAD, AAD length, and the data block's address), the
stack pointer, and the constants' address (`Pub`): whatever the key, nonce,
message, and AAD. `check` (`Rind/Aarch64/Taint.lean`) shows it for each
program in a computation the kernel checks.

That the routines compute RFC 8439's seal and open is not yet proven: the
quest `quest/m4/verified/chacha20-poly1305-aarch64/aead.md` owns that.
-/

namespace rind.aarch64.chacha20poly1305asm

/-- What two runs are known to agree on at the start: `x0`–`x5`. -/
def start : Taint := ⟨63, false⟩

/-- Two states agree on the arguments, the stack pointer, and the address of
the constants. -/
def Pub (s₁ s₂ : Rind.AArch64.State) : Prop :=
  s₁.vg.gpr .x0 = s₂.vg.gpr .x0 ∧ s₁.vg.gpr .x1 = s₂.vg.gpr .x1 ∧ s₁.vg.gpr .x2 = s₂.vg.gpr .x2 ∧
    s₁.vg.gpr .x3 = s₂.vg.gpr .x3 ∧ s₁.vg.gpr .x4 = s₂.vg.gpr .x4 ∧
    s₁.vg.gpr .x5 = s₂.vg.gpr .x5 ∧ s₁.vg.sp = s₂.vg.sp ∧ s₁.vg.syms constsName = s₂.vg.syms constsName

theorem agree_of_pub {s₁ s₂ : Rind.AArch64.State} (h : Pub s₁ s₂) :
    Agree [constsName] start s₁ s₂ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hsp, hk⟩ := h
  refine ⟨fun r hr => ?_, fun hf => absurd hf (by decide), hsp, fun n hn => ?_⟩
  · cases r <;> first | assumption | exact absurd hr (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    subst hn; exact hk

theorem check_seal : (check [constsName] sealProg start).isSome = true := by decide +kernel

theorem check_open : (check [constsName] openProg start).isSome = true := by decide +kernel

theorem constantTime {c : VG.Prog Rind.AArch64.isa} (h : (check [constsName] c start).isSome = true) :
    ConstantTime Rind.AArch64.isa (fun _ => True) Pub c := by
  obtain ⟨_, h⟩ := Option.isSome_iff_exists.mp h
  exact fun s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hp e₁ e₂ =>
    constantTime_of_check h s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ (agree_of_pub hp) e₁ e₂

/-- The seal's trace of branches and addresses depends only on its
arguments, the stack pointer, and the constants' address. -/
theorem seal_constant_time : ConstantTime Rind.AArch64.isa (fun _ => True) Pub sealProg :=
  constantTime check_seal

/-- The open's trace of branches and addresses depends only on its
arguments, the stack pointer, and the constants' address. -/
theorem open_constant_time : ConstantTime Rind.AArch64.isa (fun _ => True) Pub openProg :=
  constantTime check_open

end rind.aarch64.chacha20poly1305asm

/-- info: 'rind.aarch64.chacha20poly1305asm.seal_constant_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rind.aarch64.chacha20poly1305asm.seal_constant_time

/-- info: 'rind.aarch64.chacha20poly1305asm.open_constant_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rind.aarch64.chacha20poly1305asm.open_constant_time
