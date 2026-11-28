import RindIsa.AArch64
import Mathlib.Tactic
import Std.Tactic.BVDecide

open VG VG.AArch64

/-!
# Running rind's AArch64 programs symbolically

What the proofs of aws-lc's routines on rind's extension of VG's AArch64
model (`RindIsa/AArch64.lean`) share, as `Rind/X86_64/Asm.lean` is for
x86_64: `simp` runs a block one instruction at a time (`execAcc_cons`),
keeping each state a term of folded updates (VG's `write`, `addWithCarry`,
`flagsAdd`, and `setV`), whose projections it reads through the lemmas
below; `Frame` says what a block leaves unchanged; and `loop_ok` runs a
loop from an invariant.
-/

namespace rind.aarch64.asm

open Lean Elab Tactic in
/-- Runs `t` without error recovery, so that a discharger's failure stays a
failure rather than an error logged against an admitted goal. -/
elab "no_recover " t:tactic : tactic => withoutRecover (evalTactic t)

abbrev S := Rind.AArch64.State
abbrev I := Rind.AArch64.isa
abbrev Ins := Rind.AArch64.Instr

/-! ## Blocks, one instruction at a time -/

/-- The rest of a block, `is`, run from `o`, its trace appended to `acc`.
`execAcc_congr` keeps `simp` from running the rest of the block before the
instruction in front of it has run. -/
def execAcc (o : Option S) (acc : List Leak) (is : List Ins) : Option (S × List Leak) :=
  o.bind fun s => (execBlock I is s).map fun p => (p.1, acc ++ p.2)

@[congr] theorem execAcc_congr {o o' : Option S} {acc acc' : List Leak} (h : o = o') (h' : acc = acc')
    (is : List Ins) : execAcc o acc is = execAcc o' acc' is := h ▸ h' ▸ rfl

theorem execBlock_acc {is : List Ins} {s : S} : execBlock I is s = execAcc (some s) [] is := by
  simp only [execAcc, Option.bind_some, List.nil_append]
  cases execBlock I is s <;> rfl

theorem execAcc_cons {i : Ins} {is : List Ins} {s : S} {acc : List Leak} :
    execAcc (some s) acc (i :: is) =
      execAcc (Rind.AArch64.exec i s) (acc ++ (Rind.AArch64.addrs i s).map .addr) is := by
  simp only [execAcc, Option.bind_some]
  show ((execBlock I (i :: is) s).map _) = _
  simp only [execBlock]
  cases Rind.AArch64.exec i s with
  | none => rfl
  | some s₁ =>
    simp only [Option.bind_some, Option.map_map]
    cases execBlock I is s₁ <;> simp [I, List.append_assoc]

theorem execAcc_nil {s : S} {acc : List Leak} : execAcc (some s) acc [] = some (s, acc) := by
  simp [execAcc, execBlock]

theorem execBlock_append (a b : List Ins) (s : S) :
    execBlock I (a ++ b) s = (execBlock I a s).bind fun p =>
      (execBlock I b p.1).map fun q => (q.1, p.2 ++ q.2) := by
  induction a generalizing s with
  | nil => simp [execBlock]
  | cons i a ih =>
    simp only [List.cons_append, execBlock]
    cases Rind.AArch64.exec i s with
    | none => rfl
    | some s₁ =>
      simp only [ih]
      cases execBlock I a s₁ <;> simp [Function.comp_def]

/-- Two blocks run one after the other. -/
theorem execBlock_append_of {a b : List Ins} {s s₁ s₂ : S} {t₁ t₂ : List Leak}
    (h₁ : execBlock I a s = some (s₁, t₁)) (h₂ : execBlock I b s₁ = some (s₂, t₂)) :
    execBlock I (a ++ b) s = some (s₂, t₁ ++ t₂) := by
  rw [execBlock_append, h₁]
  simp [h₂]

theorem ex_of_eq {α : Type} {o : Option (α × List Leak)} {x : α} {t t' : List Leak} {P : α → Prop}
    (h : o = some (x, t)) (ht : t = t') (hp : P x) : ∃ s', o = some (s', t') ∧ P s' :=
  ⟨x, ht ▸ h, hp⟩

/-! ## Folded state updates -/

/-- What VG's part of the state keeps that no instruction of these
routines changes but through a frame: the stack pointer, DIT, the regions,
and what the model does not know. -/
def others (g : VG.AArch64.State) := (g.dit, g.rd, g.wr, g.unknowns, g.syms)

/-- The state with memory `m`. -/
def setMem (g : VG.AArch64.State) (m : Mem) : VG.AArch64.State := { g with mem := m }

/-- `x + y + c`, as ADDS (`c` false), ADCS, and ADC leave it. -/
def adcV (a b : BitVec 64) (c : Bool) : BitVec 64 := a + b + BitVec.ofNat 64 c.toNat

/-- The carry out of `a + b + c`. -/
def carry (a b : BitVec 64) (c : Bool) : Bool := decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)

/-- The high word of `a · b`, as UMULH leaves it. -/
def mulHi (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)

section
variable (g : VG.AArch64.State)

@[simp] theorem read_x (r : Reg) : g.read .x r = g.gpr r := by
  simp [VG.AArch64.State.read]

@[simp] theorem gpr_write (r : Reg) (x : BitVec 64) (r' : Reg) :
    (g.write .x r x).gpr r' = if r' = r then x else g.gpr r' := by
  simp [VG.AArch64.State.write]
@[simp] theorem gpr_write_w (r : Reg) (x : BitVec 32) (r' : Reg) :
    (g.write .w r x).gpr r' = if r' = r then x.setWidth 64 else g.gpr r' := rfl
@[simp] theorem v_write (sz : Size) (r : Reg) (x : BitVec sz.bits) : (g.write sz r x).v = g.v := rfl
@[simp] theorem mem_write (sz : Size) (r : Reg) (x : BitVec sz.bits) : (g.write sz r x).mem = g.mem := rfl
@[simp] theorem sp_write (sz : Size) (r : Reg) (x : BitVec sz.bits) : (g.write sz r x).sp = g.sp := rfl
@[simp] theorem c_write (sz : Size) (r : Reg) (x : BitVec sz.bits) : (g.write sz r x).c = g.c := rfl
@[simp] theorem nf_write (sz : Size) (r : Reg) (x : BitVec sz.bits) : (g.write sz r x).nf = g.nf := rfl
@[simp] theorem zf_write (sz : Size) (r : Reg) (x : BitVec sz.bits) : (g.write sz r x).zf = g.zf := rfl
@[simp] theorem vf_write (sz : Size) (r : Reg) (x : BitVec sz.bits) : (g.write sz r x).vf = g.vf := rfl
@[simp] theorem rd_write (sz : Size) (r : Reg) (x : BitVec sz.bits) : (g.write sz r x).rd = g.rd := rfl
@[simp] theorem wr_write (sz : Size) (r : Reg) (x : BitVec sz.bits) : (g.write sz r x).wr = g.wr := rfl
@[simp] theorem others_write (sz : Size) (r : Reg) (x : BitVec sz.bits) :
    others (g.write sz r x) = others g := rfl

@[simp] theorem gpr_addWithCarry (r : Reg) (a b : BitVec 64) (c : Bool) (r' : Reg) :
    (g.addWithCarry .x r a b c).gpr r' = if r' = r then adcV a b c else g.gpr r' := by
  simp [VG.AArch64.State.addWithCarry, VG.AArch64.State.write, adcV]
@[simp] theorem c_addWithCarry (r : Reg) (a b : BitVec 64) (c : Bool) :
    (g.addWithCarry .x r a b c).c = carry a b c := rfl
@[simp] theorem v_addWithCarry (r : Reg) (a b : BitVec 64) (c : Bool) :
    (g.addWithCarry .x r a b c).v = g.v := rfl
@[simp] theorem mem_addWithCarry (r : Reg) (a b : BitVec 64) (c : Bool) :
    (g.addWithCarry .x r a b c).mem = g.mem := rfl
@[simp] theorem sp_addWithCarry (r : Reg) (a b : BitVec 64) (c : Bool) :
    (g.addWithCarry .x r a b c).sp = g.sp := rfl
@[simp] theorem rd_addWithCarry (r : Reg) (a b : BitVec 64) (c : Bool) :
    (g.addWithCarry .x r a b c).rd = g.rd := rfl
@[simp] theorem wr_addWithCarry (r : Reg) (a b : BitVec 64) (c : Bool) :
    (g.addWithCarry .x r a b c).wr = g.wr := rfl
@[simp] theorem others_addWithCarry (r : Reg) (a b : BitVec 64) (c : Bool) :
    others (g.addWithCarry .x r a b c) = others g := rfl

@[simp] theorem gpr_flagsAdd (a b : BitVec 64) (c : Bool) : (g.flagsAdd a b c).gpr = g.gpr := rfl
@[simp] theorem c_flagsAdd (a b : BitVec 64) (c : Bool) : (g.flagsAdd a b c).c = carry a b c := rfl
@[simp] theorem v_flagsAdd (a b : BitVec 64) (c : Bool) : (g.flagsAdd a b c).v = g.v := rfl
@[simp] theorem mem_flagsAdd (a b : BitVec 64) (c : Bool) : (g.flagsAdd a b c).mem = g.mem := rfl
@[simp] theorem sp_flagsAdd (a b : BitVec 64) (c : Bool) : (g.flagsAdd a b c).sp = g.sp := rfl
@[simp] theorem rd_flagsAdd (a b : BitVec 64) (c : Bool) : (g.flagsAdd a b c).rd = g.rd := rfl
@[simp] theorem wr_flagsAdd (a b : BitVec 64) (c : Bool) : (g.flagsAdd a b c).wr = g.wr := rfl
@[simp] theorem others_flagsAdd (a b : BitVec 64) (c : Bool) :
    others (g.flagsAdd a b c) = others g := rfl

@[simp] theorem v_setV (r : VReg) (x : BitVec 128) (r' : VReg) :
    (g.setV r x).v r' = if r' = r then x else g.v r' := rfl
@[simp] theorem gpr_setV (r : VReg) (x : BitVec 128) : (g.setV r x).gpr = g.gpr := rfl
@[simp] theorem read_setV (r : VReg) (x : BitVec 128) (sz : Size) (r' : Reg) :
    (g.setV r x).read sz r' = g.read sz r' := rfl
@[simp] theorem c_setV (r : VReg) (x : BitVec 128) : (g.setV r x).c = g.c := rfl
@[simp] theorem nf_setV (r : VReg) (x : BitVec 128) : (g.setV r x).nf = g.nf := rfl
@[simp] theorem zf_setV (r : VReg) (x : BitVec 128) : (g.setV r x).zf = g.zf := rfl
@[simp] theorem vf_setV (r : VReg) (x : BitVec 128) : (g.setV r x).vf = g.vf := rfl
@[simp] theorem mem_setV (r : VReg) (x : BitVec 128) : (g.setV r x).mem = g.mem := rfl
@[simp] theorem sp_setV (r : VReg) (x : BitVec 128) : (g.setV r x).sp = g.sp := rfl
@[simp] theorem rd_setV (r : VReg) (x : BitVec 128) : (g.setV r x).rd = g.rd := rfl
@[simp] theorem wr_setV (r : VReg) (x : BitVec 128) : (g.setV r x).wr = g.wr := rfl
@[simp] theorem others_setV (r : VReg) (x : BitVec 128) : others (g.setV r x) = others g := rfl
@[simp] theorem syms_setV (r : VReg) (x : BitVec 128) : (g.setV r x).syms = g.syms := rfl
@[simp] theorem syms_write (sz : Size) (r : Reg) (x : BitVec sz.bits) : (g.write sz r x).syms = g.syms := rfl

@[simp] theorem gpr_setMem (m : Mem) : (setMem g m).gpr = g.gpr := rfl
@[simp] theorem v_setMem (m : Mem) : (setMem g m).v = g.v := rfl
@[simp] theorem mem_setMem (m : Mem) : (setMem g m).mem = m := rfl
@[simp] theorem sp_setMem (m : Mem) : (setMem g m).sp = g.sp := rfl
@[simp] theorem c_setMem (m : Mem) : (setMem g m).c = g.c := rfl
@[simp] theorem rd_setMem (m : Mem) : (setMem g m).rd = g.rd := rfl
@[simp] theorem wr_setMem (m : Mem) : (setMem g m).wr = g.wr := rfl
@[simp] theorem others_setMem (m : Mem) : others (setMem g m) = others g := rfl
@[simp] theorem setV_setMem (m : Mem) (r : VReg) (x : BitVec 128) :
    (setMem g m).setV r x = setMem (g.setV r x) m := rfl

theorem load_of {a : Addr} {n : Nat} (h : InRegions (g.rd ++ g.wr) a n) : g.load a n = some (g.mem.read a n) := by
  simp [VG.AArch64.State.load, h]

theorem store_of {a : Addr} {n : Nat} {v : BitVec (8 * n)} (h : InRegions g.wr a n) :
    g.store a n v = some (setMem g (g.mem.write a n v)) := by
  simp [VG.AArch64.State.store, h, setMem]
end

theorem decide_carry (a b : BitVec 64) (c : Bool) :
    decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat) = carry a b c := rfl
theorem decide_carry' (a b : BitVec 64) (c : Bool) :
    decide (18446744073709551616 ≤ a.toNat + b.toNat + c.toNat) = carry a b c := rfl

theorem mulHi_def (a b : BitVec 64) : BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64) = mulHi a b := rfl
theorem mulHi_def' (a b : BitVec 64) :
    BitVec.ofNat 64 (a.toNat * b.toNat / 18446744073709551616) = mulHi a b := rfl

theorem adcV_def (a b : BitVec 64) (c : Bool) : a + b + BitVec.ofNat 64 c.toNat = adcV a b c := rfl

/-! ## Products and carries as numbers -/

theorem mul_toNat (a b : BitVec 64) : (mulHi a b).toNat * 2 ^ 64 + (a * b).toNat = a.toNat * b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
  simp only [mulHi, BitVec.toNat_ofNat, BitVec.toNat_mul]
  rw [Nat.mod_eq_of_lt (by omega : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64)]
  omega

/-- A product of words below `2^60` and `2^64`, in its high word: below `2^60`. -/
theorem mulHi_lt (a b : BitVec 64) (ha : a.toNat < 2 ^ 60) : (mulHi a b).toNat < 2 ^ 60 := by
  have h := mul_toNat a b
  have : a.toNat * b.toNat < 2 ^ 60 * 2 ^ 64 := Nat.mul_lt_mul_of_lt_of_le ha b.isLt.le (by norm_num)
  have := (a * b).isLt
  omega

theorem mulHi_lt' (a b : BitVec 64) (hb : b.toNat < 2 ^ 60) : (mulHi a b).toNat < 2 ^ 60 := by
  rw [show mulHi a b = mulHi b a by simp only [mulHi, Nat.mul_comm]]
  exact mulHi_lt b a hb

theorem mul_small (a b : BitVec 64) (ha : a.toNat < 7) (hb : b.toNat < 2 ^ 60) :
    (a * b).toNat = a.toNat * b.toNat ∧ a.toNat * b.toNat ≤ 6 * (2 ^ 60 - 1) := by
  have : a.toNat * b.toNat ≤ 6 * (2 ^ 60 - 1) := Nat.mul_le_mul (by omega) (by omega)
  exact ⟨by rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)], this⟩

theorem carry_le (a b : BitVec 64) (c : Bool) : (carry a b c).toNat ≤ 1 := Bool.toNat_le _

/-- A sum and its carry. -/
theorem adc_carry (a b : BitVec 64) (c : Bool) :
    (adcV a b c).toNat + 2 ^ 64 * (carry a b c).toNat = a.toNat + b.toNat + c.toNat := by
  have := a.isLt; have := b.isLt; have : c.toNat ≤ 1 := Bool.toNat_le c
  simp only [adcV, carry, BitVec.toNat_add, BitVec.toNat_ofNat]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat
  · rw [decide_eq_true h, Bool.toNat_true]; omega
  · rw [decide_eq_false h, Bool.toNat_false]; omega

/-- A sum that does not overflow. -/
theorem adcV_exact (a b : BitVec 64) (c : Bool) (h : a.toNat + b.toNat + 1 < 2 ^ 64) :
    (adcV a b c).toNat = a.toNat + b.toNat + c.toNat := by
  have := adc_carry a b c
  have : c.toNat ≤ 1 := Bool.toNat_le c
  have : (carry a b c).toNat = 0 := by
    simp only [carry]; rw [decide_eq_false (by omega), Bool.toNat_false]
  omega

/-- A word plus a carry that does not overflow. -/
theorem addBit_exact (a : BitVec 64) (c : Bool) (h : a.toNat + 1 < 2 ^ 64) :
    (a + BitVec.ofNat 64 c.toNat).toNat = a.toNat + c.toNat := by
  have := Bool.toNat_le c
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c.toNat) (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-! ## Frames -/

/-- What a block leaves unchanged: the general registers but `gs`, the
vector registers but `vs`, the stack pointer, `x29`, and the rest of the
state but memory and the flags. -/
structure Frame (s s' : S) (vs : List VReg) (gs : List Reg) : Prop where
  gpr : ∀ r, r ∉ gs → s'.vg.gpr r = s.vg.gpr r
  v : ∀ r, r ∉ vs → s'.vg.v r = s.vg.v r
  sp : s'.vg.sp = s.vg.sp
  others : others s'.vg = others s.vg
  x29 : s'.x29 = s.x29

theorem Frame.refl (s : S) (vs : List VReg) (gs : List Reg) : Frame s s vs gs :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Frame.trans {s₁ s₂ s₃ : S} {vs gs} (h₁ : Frame s₁ s₂ vs gs) (h₂ : Frame s₂ s₃ vs gs) :
    Frame s₁ s₃ vs gs :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), fun r hr => (h₂.v r hr).trans (h₁.v r hr),
    h₂.sp.trans h₁.sp, h₂.others.trans h₁.others, h₂.x29.trans h₁.x29⟩

theorem Frame.mono {s s' : S} {vs gs vs' gs'} (h : Frame s s' vs gs) (hv : ∀ r ∈ vs, r ∈ vs')
    (hg : ∀ r ∈ gs, r ∈ gs') : Frame s s' vs' gs' :=
  ⟨fun r hr => h.gpr r fun m => hr (hg r m), fun r hr => h.v r fun m => hr (hv r m), h.sp, h.others,
    h.x29⟩

theorem Frame.rd {s s' : S} {vs gs} (h : Frame s s' vs gs) : s'.vg.rd = s.vg.rd :=
  congrArg (fun o => o.2.1) h.others
theorem Frame.wr {s s' : S} {vs gs} (h : Frame s s' vs gs) : s'.vg.wr = s.vg.wr :=
  congrArg (fun o => o.2.2.1) h.others
theorem Frame.syms {s s' : S} {vs gs} (h : Frame s s' vs gs) : s'.vg.syms = s.vg.syms :=
  congrArg (fun o => o.2.2.2.2) h.others

/-! ## Loops -/

/-- A loop's trace from index `j`, `m + 1` iterations long, each `d` on from the last. -/
def loopTrace (T : Nat → List Leak) (d j : Nat) : Nat → List Leak
  | 0 => T j ++ [.branch false]
  | m + 1 => T j ++ .branch true :: loopTrace T d (j + d) m

/-- A loop that runs `m + 1` times: each iteration, from index `j` in range, keeps `Inv`, and continues
while `go j`. -/
theorem loop_ok {body : Prog I} {c : Rind.AArch64.Cond} (Inv : Nat → S → Prop) (R : Nat → Prop)
    (go : Nat → Bool) (T : Nat → List Leak) (d : Nat)
    (hstep : ∀ j s, Inv j s → R j → ∃ s', Exec I body s (T j) s' ∧ I.eval c s' = some (go j) ∧
      Inv (j + d) s') :
    ∀ m j s, Inv j s → (∀ i ≤ m, R (j + d * i)) → (∀ i < m, go (j + d * i) = true) →
      go (j + d * m) = false →
      ∃ s', Exec I (.loop body c) s (loopTrace T d j m) s' ∧ Inv (j + d * (m + 1)) s' := by
  intro m
  induction m with
  | zero =>
    intro j s hI hR _ hg
    obtain ⟨s', hx, hc, hI'⟩ := hstep j s hI (by simpa using hR 0 (by omega))
    refine ⟨s', Exec.loopExit hx ?_, by simpa using hI'⟩
    rw [hc]; simpa using hg
  | succ m ih =>
    intro j s hI hR hgo hg
    obtain ⟨s₁, hx, hc, hI₁⟩ := hstep j s hI (by simpa using hR 0 (by omega))
    obtain ⟨s', hx', hI'⟩ := ih (j + d) s₁ hI₁
      (fun i hi => by
        have := hR (i + 1) (by omega); rwa [show j + d * (i + 1) = j + d + d * i by ring] at this)
      (fun i hi => by
        have := hgo (i + 1) (by omega); rwa [show j + d * (i + 1) = j + d + d * i by ring] at this)
      (by rwa [show j + d * (m + 1) = j + d + d * m by ring] at hg)
    refine ⟨s', Exec.loopNext hx (by rw [hc]; simpa using hgo 0 (by omega)) hx', ?_⟩
    rwa [show j + d * (m + 1 + 1) = j + d + d * (m + 1) by ring]

/-! ## Memory -/

theorem read_congr (m m' : Mem) (a : Addr) (n : Nat)
    (h : ∀ k < n, m' (a + BitVec.ofNat 64 k) = m (a + BitVec.ofNat 64 k)) : m'.read a n = m.read a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.read]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih (a + 1) fun k hk => by
      have e : a + 1 + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (k + 1) := by
        apply BitVec.eq_of_toNat_eq; simp; omega
      rw [e]; exact h (k + 1) (by omega)]

@[simp] theorem add_sub_left (a c : BitVec 64) : a + c - a = c := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem write_other (m : Mem) (a : Addr) (n : Nat) (v : BitVec (8 * n)) (x : Addr)
    (h : n ≤ (x - a).toNat) : m.write a n v x = m x := by
  simp only [Mem.write]; rw [ite_eq_right_iff.mpr (by omega)]

/-- `m` bytes from `k` into a readable range are readable. -/
theorem InRegions.sub {rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) (k m : Nat)
    (hk : k + m ≤ n) : InRegions rs (a + BitVec.ofNat 64 k) m := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  unfold Region.Contains at *
  have : ((a + BitVec.ofNat 64 k) - r.base).toNat ≤ (a - r.base).toNat + k := by bv_omega
  omega

theorem add_ofNat (a : Addr) (x y : Nat) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem ofNat_sub (n k : Nat) (h : k ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 k = BitVec.ofNat 64 (n - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-! ## Running a block -/

set_option hygiene false in
/-- Discharges the side conditions of a block's run: encodings, and the
regions an access needs, which the run's hypotheses state of the state it
started from. -/
macro "a64_disch" : tactic => `(tactic| no_recover first
  | decide
  | assumption
  | (try simp only [rd_write, wr_write, rd_addWithCarry, wr_addWithCarry, rd_flagsAdd, wr_flagsAdd,
        rd_setV, wr_setV, rd_setMem, wr_setMem]) <;> first
      | assumption
      | omega)

/-- Runs a block one instruction at a time, with the lemmas given. -/
syntax "a64_run " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| a64_run [$xs,*]) => `(tactic|
    simp (config := { maxSteps := 4000000 }) (disch := a64_disch) only [$xs,*, execAcc_cons, execAcc_nil,
      Rind.AArch64.exec, Rind.AArch64.addrs, VG.AArch64.addrs, VG.AArch64.exec, VG.AArch64.VOp.eval,
      Option.map_some, Option.bind_some, load_of, store_of, read_x, gpr_write, gpr_write_w, v_write,
      mem_write, sp_write, c_write, rd_write, wr_write, syms_write, gpr_addWithCarry, c_addWithCarry,
      v_addWithCarry, mem_addWithCarry, sp_addWithCarry, rd_addWithCarry, wr_addWithCarry, gpr_flagsAdd,
      c_flagsAdd, v_flagsAdd, mem_flagsAdd, sp_flagsAdd, rd_flagsAdd, wr_flagsAdd, v_setV, gpr_setV,
      read_setV, c_setV, mem_setV, sp_setV, rd_setV, wr_setV, syms_setV, gpr_setMem, v_setMem, mem_setMem,
      sp_setMem, c_setMem, rd_setMem, wr_setMem, setV_setMem, decide_carry, decide_carry', mulHi_def,
      mulHi_def', adcV_def, VG.AArch64.Size.bits, Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
      Nat.reduceDiv, Nat.reducePow, Nat.lt_irrefl, Nat.ofNat_pos, and_self, and_true, true_and,
      reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, List.map_nil, List.map_cons, List.append_nil,
      List.nil_append, List.cons_append])

/-- Reads what a block leaves: its registers, memory, and frame, each by
`rfl` once `simp` has read through the folded updates. -/
syntax "a64_out" : tactic
macro_rules
  | `(tactic| a64_out) => `(tactic| (
    repeat' apply And.intro
    all_goals try (apply Frame.mk <;> try intro r hr)
    all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    all_goals try simp (config := { maxSteps := 4000000 }) only [gpr_write, gpr_write_w, v_write, mem_write,
      sp_write, others_write, gpr_addWithCarry, v_addWithCarry, mem_addWithCarry, sp_addWithCarry,
      others_addWithCarry, gpr_flagsAdd, v_flagsAdd, mem_flagsAdd, sp_flagsAdd, others_flagsAdd, v_setV,
      gpr_setV, mem_setV, sp_setV, others_setV, gpr_setMem, v_setMem, mem_setMem, sp_setMem, others_setMem,
      c_addWithCarry, c_flagsAdd, c_write, c_setV, c_setMem, reduceCtorEq, ↓reduceIte, *]
    all_goals try rfl))

end rind.aarch64.asm
