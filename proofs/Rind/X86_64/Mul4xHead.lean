import Rind.X86_64.Mul4xHeadAsm
import Rind.X86_64.Mul4xLoop

/-! # bn_mul4x_mont's prologue and stack walk

The pushes, then `rsp` lowered a page at a time to `tp`, the scratch space `8k + 80` to `8k + 1103` bytes below
the stack pointer, 1024-byte aligned. -/

open VG VG.X86_64 Rind.X86_64.Mul4x rind.x86_64.asm

set_option linter.unusedSimpArgs false

namespace rind.x86_64.mul4x

theorem and_mask10 (x : BitVec 64) : x &&& BitVec.ofNat 64 18446744073709550592 = (x >>> 10) <<< 10 := by
  rw [BitVec.shiftLeft_ushiftRight]; rfl

theorem and_mask12 (x : BitVec 64) : x &&& BitVec.ofNat 64 18446744073709547520 = (x >>> 12) <<< 12 := by
  rw [BitVec.shiftLeft_ushiftRight]; rfl

theorem toNat_shr_shl (x : BitVec 64) (j : Nat) : ((x >>> j) <<< j).toNat = x.toNat / 2 ^ j * 2 ^ j := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ _) x.isLt)

theorem tpOf_toNat (sp0 : Addr) (k : Nat) (hk : k < 2 ^ 32) (h : 8 * k + 80 ≤ sp0.toNat) :
    (tpOf sp0 k).toNat = (sp0.toNat - 8 * k - 80) / 1024 * 1024 := by
  have e : sp0 - BitVec.ofNat 64 48 + (0 - BitVec.ofNat 64 k) * 8#64 + BitVec.ofNat 64 18446744073709551584 =
      sp0 - (BitVec.ofNat 64 k * 8#64 + 80#64) := by
    generalize BitVec.ofNat 64 k = x; bv_omega
  have hx : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
  unfold tpOf
  rw [e, and_mask10, toNat_shr_shl]
  congr 2
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, hx]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem pagesOf_toNat (sp0 tp : Addr) (h : tp.toNat + 48 ≤ sp0.toNat) :
    (pagesOf sp0 tp).toNat = (sp0.toNat - 48 - tp.toNat) / 4096 * 4096 := by
  unfold pagesOf
  rw [and_mask12, toNat_shr_shl]
  congr 2
  rw [BitVec.toNat_sub, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem FrameS.refl (s : S) (gs : List Reg) : FrameS s s gs := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem FrameS.trans {s₁ s₂ s₃ : S} {gs : List Reg} (h₁ : FrameS s₁ s₂ gs) (h₂ : FrameS s₂ s₃ gs) :
    FrameS s₁ s₃ gs :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.others.trans h₁.others,
    h₂.xmm.trans h₁.xmm, h₂.mxcsr.trans h₁.mxcsr, h₂.lo.trans h₁.lo⟩

/-- The walk down from `m` pages above `tp`, before step `i`. -/
structure WalkInv (s₀ s : S) (tp sp0 : Addr) (rest : List Region) (m i : Nat) : Prop where
  rsp : s.vg.gpr .rsp = tp + BitVec.ofNat 64 (4096 * (m - i))
  r10 : s.vg.gpr .r10 = tp
  wr : s.vg.wr = ⟨tp + BitVec.ofNat 64 (4096 * (m - i)), sp0.toNat + 8 - (tp + BitVec.ofNat 64 (4096 * (m - i))).toNat⟩ ::
    rest
  frame : FrameS s₀ s [.rsp, .r11]

/-- The walk's trace, from `m` pages above `tp`. -/
def walkTrace (tp : Addr) (m : Nat) : List Leak :=
  if m = 0 then [.branch false]
  else .branch true :: loopTrace (fun i => [.addr (tp + BitVec.ofNat 64 (4096 * (m - i - 1)))]) 1 0 (m - 1)

theorem walk_loop (s₀ : S) (tp sp0 : Addr) (rest : List Region) (m : Nat) (hm : 1 ≤ m)
    (hno : tp.toNat + 4096 * m + 48 ≤ sp0.toNat) (hsp : sp0.toNat + 8 ≤ 2 ^ 64) (hlo : s₀.lo.toNat ≤ tp.toNat)
    (hI : WalkInv s₀ s₀ tp sp0 rest m 0) :
    ∃ s', Exec I (.loop (.block walk) Rind.X86_64.Cond.a) s₀
      (loopTrace (fun i => [.addr (tp + BitVec.ofNat 64 (4096 * (m - i - 1)))]) 1 0 (m - 1)) s' ∧
      WalkInv s₀ s' tp sp0 rest m m := by
  have step : ∀ i s, WalkInv s₀ s tp sp0 rest m i → i < m →
      ∃ s', Exec I (.block walk) s [.addr (tp + BitVec.ofNat 64 (4096 * (m - i - 1)))] s' ∧
        I.eval Rind.X86_64.Cond.a s' = some (decide (i + 1 < m)) ∧ WalkInv s₀ s' tp sp0 rest m (i + 1) := by
    intro i s hI hi
    have e : tp + BitVec.ofNat 64 (4096 * (m - i)) =
        tp + (BitVec.ofNat 64 (4096 * (m - i - 1)) + BitVec.ofNat 64 4096) := by
      rw [BitVec.ofNat_add_ofNat]; congr 2; omega
    have hX : (BitVec.ofNat 64 (4096 * (m - i - 1))).toNat = 4096 * (m - i - 1) := by simp; omega
    obtain ⟨s', hx, o_sp, o10, owr, ocf, ozf, oF⟩ :=
      walk_ok s tp (BitVec.ofNat 64 (4096 * (m - i - 1))) _ rest (hI.rsp.trans e) hI.r10 (e ▸ hI.wr)
        (by rw [hX]; omega) (by rw [hI.frame.lo]; exact hlo)
    have hY : (tp + BitVec.ofNat 64 (4096 * (m - i - 1))).toNat = tp.toNat + 4096 * (m - i - 1) := by
      rw [BitVec.toNat_add, hX]; omega
    have hY' : (tp + BitVec.ofNat 64 (4096 * (m - i))).toNat = tp.toNat + 4096 * (m - i) := by
      rw [BitVec.toNat_add]; simp; omega
    refine ⟨s', Exec.block hx, ?_, ?_, o10, ?_, hI.frame.trans oF⟩
    · simp only [Rind.X86_64.isa, Rind.X86_64.eval, ocf, ozf, Option.bind_some, Option.map_some]
      have h1 : decide ((tp + BitVec.ofNat 64 (4096 * (m - i - 1))).toNat < tp.toNat) = false := by
        rw [hY]; simp
      have h2 : (tp + BitVec.ofNat 64 (4096 * (m - i - 1)) - tp == 0) = decide (m - i - 1 = 0) := by
        rw [show tp + BitVec.ofNat 64 (4096 * (m - i - 1)) - tp = BitVec.ofNat 64 (4096 * (m - i - 1)) by bv_omega]
        by_cases h : m - i - 1 = 0
        · simp [h]
        · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
          intro h'; have := congrArg BitVec.toNat h'; rw [hX] at this; simp at this; omega
      have h3 : (m - i - 1 = 0) ↔ ¬(i + 1 < m) := by omega
      rw [h1, h2]; simp only [h3, Bool.not_false, Bool.true_and, decide_not, Bool.not_not]
    · rw [o_sp]; rfl
    · rw [show m - (i + 1) = m - i - 1 by omega, owr, ← e, hY, hY']
      simp only [List.cons.injEq, Region.mk.injEq, true_and, and_true]
      omega
  obtain ⟨s', hx, hI'⟩ := loop_ok (body := .block walk) (c := Rind.X86_64.Cond.a)
    (fun i s => WalkInv s₀ s tp sp0 rest m i) (fun i => i < m) (fun i => decide (i + 1 < m))
    (fun i => [.addr (tp + BitVec.ofNat 64 (4096 * (m - i - 1)))]) 1 step (m - 1) 0 s₀ hI
    (fun i hi => by omega) (fun i hi => by simp; omega) (by simp; omega)
  rw [show 0 + 1 * (m - 1 + 1) = m by omega] at hI'
  exact ⟨s', hx, hI'⟩

set_option maxHeartbeats 1000000 in
theorem head_ok (s : S) (k : Nat) (sp0 : Addr) (rest : List Region)
    (hk : k < 2 ^ 32) (hlo : s.lo.toNat + 8 * k + 1104 ≤ sp0.toNat) (hsp : sp0.toNat + 8 ≤ 2 ^ 64)
    (hrsp : s.vg.gpr .rsp = sp0) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 k)
    (hwr : s.vg.wr = ⟨sp0, 8⟩ :: rest) :
    ∃ s₁ s', Exec I (.block prologue) s (prologueATrace sp0 ++ [.addr (tpOf sp0 k + pagesOf sp0 (tpOf sp0 k))]) s₁ ∧
      Exec I (.ite Rind.X86_64.Cond.a (.loop (.block walk) Rind.X86_64.Cond.a) (.block [])) s₁
        (walkTrace (tpOf sp0 k) ((pagesOf sp0 (tpOf sp0 k)).toNat / 4096)) s' ∧
      s'.vg.gpr .rsp = tpOf sp0 k ∧ s'.vg.gpr .rax = sp0 ∧ s'.vg.gpr .r9 = BitVec.ofNat 64 k ∧
      s'.vg.wr = ⟨tpOf sp0 k, sp0.toNat + 8 - (tpOf sp0 k).toNat⟩ :: rest ∧
      s'.vg.mem = (((((s.vg.mem.writeW (sp0 - BitVec.ofNat 64 8) (s.vg.gpr .rbx)).writeW (sp0 - BitVec.ofNat 64 16)
        (s.vg.gpr .rbp)).writeW (sp0 - BitVec.ofNat 64 24) (s.vg.gpr .r12)).writeW (sp0 - BitVec.ofNat 64 32)
        (s.vg.gpr .r13)).writeW (sp0 - BitVec.ofNat 64 40) (s.vg.gpr .r14)).writeW (sp0 - BitVec.ofNat 64 48)
        (s.vg.gpr .r15) ∧
      (∀ r, r ∉ [Reg.rsp, .rax, .r9, .r10, .r11] → s'.vg.gpr r = s.vg.gpr r) ∧ others s'.vg = others s.vg ∧
      s'.vg.mxcsr = s.vg.mxcsr ∧ s'.lo = s.lo := by
  obtain ⟨s₁, hxA, a_sp, a_ax, a9, a10, a11, awr, amem, ag, aoth, amx, alo⟩ :=
    prologueA_ok s k sp0 rest hk (by omega) hsp hrsp hr9 hwr
  have htp := tpOf_toNat sp0 k hk (by omega)
  generalize tpOf sp0 k = tp at htp a10 a11 ⊢
  have t1 := Nat.div_add_mod (sp0.toNat - 8 * k - 80) 1024
  have t2 := Nat.mod_lt (sp0.toNat - 8 * k - 80) (show 1024 > 0 by norm_num)
  have t3 : tp.toNat + 8 * k + 80 ≤ sp0.toNat ∧ sp0.toNat ≤ tp.toNat + 8 * k + 1103 := by
    rw [htp]; constructor <;> omega
  clear t1 t2
  have hP := pagesOf_toNat sp0 tp (by omega)
  have hq : (sp0 - BitVec.ofNat 64 48).toNat = sp0.toNat - 48 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  generalize pagesOf sp0 tp = P at hP a11 ⊢
  have p1 := Nat.div_add_mod (sp0.toNat - 48 - tp.toNat) 4096
  have p2 := Nat.mod_lt (sp0.toNat - 48 - tp.toNat) (show 4096 > 0 by norm_num)
  have p3 : P.toNat ≤ sp0.toNat - 48 - tp.toNat ∧ P.toNat % 4096 = 0 := by rw [hP]; omega
  clear p1 p2
  have hTP : (tp + P).toNat = tp.toNat + P.toNat := by rw [BitVec.toNat_add]; omega
  obtain ⟨s₂, hxB, b_sp, b10, bwr, bcf, bzf, bF⟩ :=
    prologueB_ok s₁ (sp0 - BitVec.ofNat 64 48) tp P 56 rest a_sp a10 a11 awr (by omega) (by omega)
      (by rw [alo]; omega)
  have hxP : execBlock I prologue s = some (s₂, prologueATrace sp0 ++ [.addr (tp + P)]) := by
    rw [prologue_split, execBlock_append, hxA]
    simp only [Option.bind_some, hxB, Option.map_some]
  set m := P.toNat / 4096 with hm
  have hPm : P = BitVec.ofNat 64 (4096 * m) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  have hev : I.eval Rind.X86_64.Cond.a s₂ = some (!decide (m = 0)) := by
    simp only [Rind.X86_64.isa, Rind.X86_64.eval, bcf, bzf, Option.bind_some, Option.map_some]
    have h1 : decide ((tp + P).toNat < tp.toNat) = false := by rw [hTP]; simp
    have h2 : (tp + P - tp == 0) = decide (m = 0) := by
      rw [show tp + P - tp = P by bv_omega]
      by_cases h : m = 0
      · have hP0 : P = 0 := BitVec.eq_of_toNat_eq (by rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega)
        simp only [h, hP0, decide_true, beq_self_eq_true]
      · have hP0 : P ≠ 0 := fun h' => by rw [h', show (0 : BitVec 64).toNat = 0 from rfl] at hm; exact h hm
        simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq, hP0, not_false_eq_true]
    rw [h1, h2, Bool.not_false, Bool.true_and]
  have hwalk : ∃ s₃, Exec I (.ite Rind.X86_64.Cond.a (.loop (.block walk) Rind.X86_64.Cond.a) (.block [])) s₂
      (walkTrace tp m) s₃ ∧ s₃.vg.gpr .rsp = tp ∧ s₃.vg.wr = ⟨tp, sp0.toNat + 8 - tp.toNat⟩ :: rest ∧
      FrameS s₂ s₃ [.rsp, .r11] := by
    by_cases h0 : m = 0
    · have hP0 : P = 0 := by rw [hPm, h0]; rfl
      refine ⟨s₂, ?_, by rw [b_sp, hP0]; exact BitVec.add_zero _, ?_, FrameS.refl _ _⟩
      · simp only [walkTrace, h0, ↓reduceIte]
        exact Exec.iteF (by rw [hev, h0]; rfl) (Exec.block rfl)
      · have hP0n : P.toNat = 0 := by omega
        rw [bwr, hTP, hq, hP0n, hP0]
        simp only [List.cons.injEq, Region.mk.injEq, and_true]
        exact ⟨BitVec.add_zero _, by omega⟩
    · have hI : WalkInv s₂ s₂ tp sp0 rest m 0 := by
        refine ⟨by rw [b_sp, hPm]; rfl, b10, ?_, FrameS.refl _ _⟩
        simp only [Nat.sub_zero]
        rw [bwr, hTP, hq, ← hPm, hTP]
        simp only [List.cons.injEq, Region.mk.injEq, true_and, and_true]
        omega
      obtain ⟨s₃, hx3, hI3⟩ := walk_loop s₂ tp sp0 rest m (by omega) (by omega) hsp
        (by rw [bF.lo, alo]; omega) hI
      refine ⟨s₃, ?_, ?_, ?_, hI3.frame⟩
      · simp only [walkTrace, h0, ↓reduceIte]
        exact Exec.iteT (by rw [hev]; simp [h0]) hx3
      · rw [hI3.rsp, Nat.sub_self, Nat.mul_zero]; exact BitVec.add_zero _
      · rw [hI3.wr, Nat.sub_self, Nat.mul_zero]; simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  obtain ⟨s₃, hx3, c_sp, cwr, cF⟩ := hwalk
  have F := bF.trans cF
  refine ⟨s₂, s₃, Exec.block hxP, hx3, c_sp, ?_, ?_, cwr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [F.gpr _ (by decide), a_ax]
  · rw [F.gpr _ (by decide), a9]
  · rw [F.mem, amem]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [F.gpr r (by simp [hr.1, hr.2.2.2.2]), ag r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]
  · rw [F.others, aoth]
  · rw [F.mxcsr, amx]
  · rw [F.lo, alo]

end rind.x86_64.mul4x
