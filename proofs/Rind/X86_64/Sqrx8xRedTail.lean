import Rind.X86_64.Sqrx8xRedLoop

/-! # bn_sqrx8x_internal's reduction tail

After a round's eight multipliers, their products with `n`'s words past its first eight, eight words of `n` at a
time: `tailHead` and a loop of `tail` for the first eight, then a loop of `tailPass` for each eight after. Each adds
the next eight words of `t` to the accumulator, keeping their carry in slot 3, and stores the eight words the
multipliers' products push out of it over them. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.sqrx8x

/-- The registers the reduction may change: all but the stack pointer. -/
abbrev RL : List Reg := [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem _root_.rind.x86_64.asm.Frame.toRL {s s' : S} {gs : List Reg} (h : Frame s s' gs) (hg : ∀ r ∈ gs, r ∈ RL := by decide) :
    Frame s s' RL := h.mono hg

theorem Mems.trans {M₀ M₁ M₂ : Mem} {k : Nat} {np fp : Addr} {n g g' : Nat → BitVec 64}
    (h₁ : Mems M₀ M₁ k np fp n g) (h₂ : Mems M₁ M₂ k np fp n g') : Mems M₀ M₂ k np fp n g' :=
  ⟨h₂.fw, h₂.nw, h₁.keeps.trans h₂.keeps⟩

theorem Mems.refl {M₀ M : Mem} {k : Nat} {np fp : Addr} {n g : Nat → BitVec 64} (h : Mems M₀ M k np fp n g) :
    Mems M M k np fp n g :=
  ⟨h.fw, h.nw, Keeps.refl _ _ _⟩

set_option exponentiation.threshold 1024 in
theorem hsum8_val (f : Nat → BitVec 64) (a : Nat) :
    hsum [f a, f (a + 1), f (a + 2), f (a + 3), f (a + 4), f (a + 5), f (a + 6), f (a + 7)] =
      val (fun i => f (a + i)) 8 := by
  simp only [hsum, val, gsum, Nat.add_zero, Nat.reduceMul, Nat.reducePow, Nat.mul_zero, Nat.pow_zero,
    Nat.mul_one, Nat.zero_add]
  omega

theorem val_eq {f g : Nat → BitVec 64} {m : Nat} (h : ∀ i < m, f i = g i) : val f m = val g m :=
  gsum_congr fun i hi => by rw [h i hi]

theorem nil_nm (r : Reg) : r ∉ ([] : List Reg) := fun h => by cases h

/-! ## A pass of the tail -/

set_option exponentiation.threshold 1024 in
/-- The sum a pass keeps: its stores and the accumulator with the carry, against the words it added, the
accumulator it started from, and the multipliers' multiples of `n`'s words. -/
theorem tp_arith (Vc Vb rb Ac Av Q8 Nn rs G8 cc V1c acc1 Nc Wc : Nat)
    (eLoop : 2 ^ 512 * rb + Vb = Av + Q8 * Nn) (eAdd : Av + 2 ^ 512 * Ac = rs + G8 + cc)
    (ePrev : Vc + Wc * (rs + cc) = V1c + acc1 + Q8 * Nc) :
    (Vc + Wc * Vb) + Wc * 2 ^ 512 * (rb + Ac) = (V1c + Wc * G8) + acc1 + Q8 * (Nc + Wc * Nn) := by
  zify at eLoop eAdd ePrev ⊢
  linear_combination (Wc : ℤ) * eLoop + (Wc : ℤ) * eAdd + ePrev

/-- The tail after its pass for `n`'s eight words from `c`, the round's window at `t`'s word `p` and `s₁` the state
it started from: `c` words stored from `t`'s word `p + 8`, `rdi` past them, `rbp` at `n`'s word `c`, and with the
accumulator and slot 3's carry, at the next word, as much as the words they replaced, the accumulator at the start,
and the multipliers' multiples of `n`'s words from 8 to `c + 8`. -/
structure TPInv (s₁ s : S) (k p : Nat) (np fp : Addr) (n g₁ : Nat → BitVec 64) (c : Nat) : Prop where
  frame : Frame s₁ s RL
  rbp : s.vg.gpr .rbp = wa np c
  rdi : s.vg.gpr .rdi = wa fp (p + c + 15)
  rsi : s.vg.gpr .rsi = 0
  rcx : s.vg.gpr .rcx = 0
  cf : s.vg.cf = some (decide (c + 8 < k))
  mem : ∃ g', Mems s₁.vg.mem s.vg.mem k np fp n g' ∧
    (∀ i, i ≠ 3 → (i < p + 15 ∨ p + c + 15 ≤ i) → g' i = g₁ i) ∧
    val (fun i => g' (p + 15 + i)) c + 2 ^ (64 * c) * (regs s + (unmask (g' 3)).toNat) =
      val (fun i => g₁ (p + 15 + i)) c + regs s₁ + val (fun i => g₁ (7 + i)) 8 * val (fun i => n (8 + i)) c

/-- The trace of a `tailPass` after `n`'s eight words from `c`. -/
def tailPassTrace (np fp : Addr) (p c : Nat) : List Leak :=
  tailNextTrace fp (p + c + 15) ++ (tailLoopTrace np fp (c + 8) (p + c + 15) ++ tailEndTrace fp)

theorem cmp_np {np : Addr} {k a b : Nat} (hnp : np.toNat + 8 * k ≤ 2 ^ 64) (ha : a < k) (hb : b < k) :
    decide ((wa np a).toNat < (wa np b).toNat) = decide (a < b) := by
  rw [wa_toNat hnp ha, wa_toNat hnp hb]; simp only [decide_eq_decide]; omega

set_option maxHeartbeats 1000000 in
theorem tailPass_step (s₁ s : S) (k p c : Nat) (ap np fp : Addr) (n g₁ : Nat → BitVec 64)
    (hk : 8 ≤ k) (hp : p + 8 ≤ k) (hc : c + 16 ≤ k) (ar : Arr s₁ k ap np fp) (hrsp : s₁.vg.gpr .rsp = fp)
    (hg1 : g₁ 1 = wa np (k - 8)) (hI : TPInv s₁ s k p np fp n g₁ c) :
    ∃ s', Exec I Rind.X86_64.Sqrx8x.tailPass s (tailPassTrace np fp p c) s' ∧
      I.eval (.vg .b) s' = some (decide (c + 16 < k)) ∧ TPInv s₁ s' k p np fp n g₁ (c + 8) := by
  have hb := ar
  obtain ⟨hk', hap, hnp, hfp, sepA, sepN, -, -, -, -, -⟩ := hb
  obtain ⟨hF, hbp, hdi, hsi, hcx, -, g', hM, hg', hv⟩ := hI
  have ar' := ar.frame hF
  have hsp : s.vg.gpr .rsp = fp := (hF.gpr .rsp (by simp)).trans hrsp
  obtain ⟨sa, hxa, amem, a8, a9, a10, a11, a12, a13, a14, a15, adx, abp, acx, adi, asi, acf, aof, aF⟩ :=
    tailNext_ok s k c (p + c + 15) ap np fp g' (by omega) hc ar' hsp hdi hbp hsi hcx hM.fw
  set A := add8 (s.vg.gpr .r8) (s.vg.gpr .r9) (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12)
    (s.vg.gpr .r13) (s.vg.gpr .r14) (s.vg.gpr .r15) (g' (p + c + 15)) (g' (p + c + 15 + 1)) (g' (p + c + 15 + 2))
    (g' (p + c + 15 + 3)) (g' (p + c + 15 + 4)) (g' (p + c + 15 + 5)) (g' (p + c + 15 + 6))
    (g' (p + c + 15 + 7)) (unmask (g' 3)) with hA
  set ga := Function.update g' 3 (mask A.c) with hga
  have hMa : Mems s₁.vg.mem sa.vg.mem k np fp n ga := by
    rw [amem]; exact hM.write hnp hfp sepN (by omega) _
  have ara := ar.frame (hF.trans aF.toRL)
  have hspa : sa.vg.gpr .rsp = fp := (aF.gpr .rsp (by simp)).trans hsp
  have hI0 : TailInv sa sa k np fp n ga (c + 8) (p + c + 15) 0 :=
    ⟨Frame.refl _ _, by rw [acx]; rfl, fun _ => by rw [adx, hga, Function.update_of_ne (by omega)], acf, aof, ga,
      hMa.refl, fun _ _ => rfl, by simp [val, gsum]⟩
  obtain ⟨sb, hxb, hIb⟩ := tailLoop_ok sa k (c + 8) (p + c + 15) ap np fp n ga (by omega) (by omega) (by omega)
    ara hspa abp asi adi hI0
  obtain ⟨hFb, hcxb, -, -, -, gb, hMb, hgb, hvb⟩ := hIb
  have arb := ara.frame hFb
  have hspb : sb.vg.gpr .rsp = fp := (hFb.gpr .rsp (by simp)).trans hspa
  obtain ⟨sc, hxc, ccf, cmem, cF⟩ := tailEnd_ok sb k ap np fp gb arb hspb hMb.fw
  have hbpb : sb.vg.gpr .rbp = wa np (c + 8) := (hFb.gpr .rbp (by simp)).trans abp
  have hgb_ga : ∀ i, i < p + c + 15 → gb i = ga i := fun i hi => hgb i (Or.inl hi)
  have hga_g' : ∀ i, i ≠ 3 → ga i = g' i := fun i hi => by rw [hga, Function.update_of_ne hi]
  have hgb1 : gb 1 = wa np (k - 8) := by
    rw [hgb_ga 1 (by omega), hga_g' 1 (by omega), hg' 1 (by omega) (by omega), hg1]
  refine ⟨sc, Exec.seq (Exec.block hxa) (Exec.seq hxb (Exec.block hxc)), ?_, ?_⟩
  · simp only [Rind.X86_64.isa, Rind.X86_64.eval, VG.X86_64.eval, ccf, hbpb, hgb1]
    rw [cmp_np hnp (by omega) (by omega)]; congr 1; exact decide_eq_decide.mpr (by omega)
  refine ⟨((hF.trans aF.toRL).trans hFb.toRL).trans cF.toRL, ?_, ?_, ?_, ?_, ?_, gb, ?_, ?_, ?_⟩
  · rw [cF.gpr .rbp (nil_nm _), hbpb]
  · rw [cF.gpr .rdi (nil_nm _), hFb.gpr .rdi (by simp), adi, show p + (c + 8) + 15 = p + c + 15 + 8 by omega]
  · rw [cF.gpr .rsi (nil_nm _), hFb.gpr .rsi (by simp), asi]
  · rw [cF.gpr .rcx (nil_nm _), hcxb]; decide
  · rw [ccf, hbpb, hgb1, cmp_np hnp (by omega) (by omega)]; congr 1; exact decide_eq_decide.mpr (by omega)
  · rw [cmem]; exact hMa.trans hMb
  · intro i h3 hi
    rw [hgb i (by omega), hga_g' i h3]; exact hg' i h3 (by omega)
  · -- the pass's sum
    have hregs : regs sc = regs sb := by
      simp only [regs, cF.gpr .r8 (nil_nm _), cF.gpr .r9 (nil_nm _), cF.gpr .r10 (nil_nm _), cF.gpr .r11 (nil_nm _),
        cF.gpr .r12 (nil_nm _), cF.gpr .r13 (nil_nm _), cF.gpr .r14 (nil_nm _), cF.gpr .r15 (nil_nm _)]
    have hrega : regs sa = A.val := by simp only [regs, a8, a9, a10, a11, a12, a13, a14, a15, Acc.val]
    have hadd := add8_acct (s.vg.gpr .r8) (s.vg.gpr .r9) (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12)
      (s.vg.gpr .r13) (s.vg.gpr .r14) (s.vg.gpr .r15) (g' (p + c + 15)) (g' (p + c + 15 + 1))
      (g' (p + c + 15 + 2)) (g' (p + c + 15 + 3)) (g' (p + c + 15 + 4)) (g' (p + c + 15 + 5))
      (g' (p + c + 15 + 6)) (g' (p + c + 15 + 7)) (unmask (g' 3))
    dsimp only at hadd
    rw [← hA, hsum8_val g' (p + c + 15)] at hadd
    have hG8 : val (fun i => g' (p + c + 15 + i)) 8 = val (fun i => g₁ (p + 15 + (c + i))) 8 :=
      val_eq fun i _ => by rw [hg' _ (by omega) (by omega)]; exact congrArg g₁ (by omega)
    have hQ : val (fun i => ga (7 + i)) 8 = val (fun i => g₁ (7 + i)) 8 :=
      val_eq fun i _ => by rw [hga_g' _ (by omega), hg' _ (by omega) (by omega)]
    have hNn : hsum [n (c + 8), n (c + 8 + 1), n (c + 8 + 2), n (c + 8 + 3), n (c + 8 + 4), n (c + 8 + 5),
        n (c + 8 + 6), n (c + 8 + 7)] = val (fun i => n (8 + (c + i))) 8 := by
      rw [hsum8_val n (c + 8)]; exact val_eq fun i _ => congrArg n (by omega)
    have hVb : val (fun i => gb (p + 15 + (c + i))) 8 = val (fun i => gb (p + c + 15 + i)) 8 :=
      val_eq fun i _ => congrArg gb (by omega)
    have hVc : val (fun i => gb (p + 15 + i)) c = val (fun i => g' (p + 15 + i)) c :=
      val_eq fun i _ => by rw [hgb_ga _ (by omega), hga_g' _ (by omega)]
    have hu : unmask (gb 3) = A.c := by
      rw [hgb_ga 3 (by omega), hga, Function.update_self, unmask_mask]
    rw [hrega, hQ, hNn] at hvb
    norm_num only at hvb
    rw [val_split (fun i => gb (p + 15 + i)) c 8, val_split (fun i => g₁ (p + 15 + i)) c 8,
      val_split (fun i => n (8 + i)) c 8, hregs, hu, hVc, hVb, ← hG8,
      show 64 * (c + 8) = 64 * c + 512 by ring, pow_add]
    exact tp_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ hvb hadd hv

set_option exponentiation.threshold 1024 in
theorem tf_arith (Vb rb Ac Av Q8 Nn rs G8 : Nat) (eLoop : 2 ^ 512 * rb + Vb = Av + Q8 * Nn)
    (eAdd : Av + 2 ^ 512 * Ac = rs + G8) : Vb + 2 ^ 512 * (rb + Ac) = G8 + rs + Q8 * Nn := by
  omega

set_option maxHeartbeats 1000000 in
/-- The tail's first pass, for `n`'s words 8 to 16. -/
theorem tailFirst_ok (s₁ : S) (k p : Nat) (ap np fp : Addr) (n g₁ : Nat → BitVec 64)
    (hk : 16 ≤ k) (hp : p + 8 ≤ k) (ar : Arr s₁ k ap np fp) (hrsp : s₁.vg.gpr .rsp = fp)
    (hrdi : s₁.vg.gpr .rdi = wa fp (p + 15)) (hrbp : s₁.vg.gpr .rbp = np) (hrax : s₁.vg.gpr .rax = 0)
    (hM : Mems s₁.vg.mem s₁.vg.mem k np fp n g₁) (hg1 : g₁ 1 = wa np (k - 8)) :
    ∃ sa sb sc, Exec I (.block Rind.X86_64.Sqrx8x.tailHead) s₁ (tailHeadTrace fp (p + 15)) sa ∧
      Exec I (.loop (.block Rind.X86_64.Sqrx8x.tail) (.vg .ne)) sa (tailLoopTrace np fp 8 (p + 15)) sb ∧
      Exec I (.block Rind.X86_64.Sqrx8x.tailEnd) sb (tailEndTrace fp) sc ∧ TPInv s₁ sc k p np fp n g₁ 8 := by
  have hb := ar
  obtain ⟨hk', hap, hnp, hfp, sepA, sepN, -, -, -, -, -⟩ := hb
  obtain ⟨sa, hxa, amem, a8, a9, a10, a11, a12, a13, a14, a15, adx, abp, acx, adi, asi, acf, aof, aF⟩ :=
    tailHead_ok s₁ k (p + 15) ap np fp g₁ (by omega) ar hrsp hrdi hrbp hrax hM.fw
  set A := add8' (s₁.vg.gpr .r8) (s₁.vg.gpr .r9) (s₁.vg.gpr .r10) (s₁.vg.gpr .r11) (s₁.vg.gpr .r12)
    (s₁.vg.gpr .r13) (s₁.vg.gpr .r14) (s₁.vg.gpr .r15) (g₁ (p + 15)) (g₁ (p + 15 + 1)) (g₁ (p + 15 + 2))
    (g₁ (p + 15 + 3)) (g₁ (p + 15 + 4)) (g₁ (p + 15 + 5)) (g₁ (p + 15 + 6)) (g₁ (p + 15 + 7)) with hA
  set ga := Function.update g₁ 3 (mask A.c) with hga
  have hMa : Mems s₁.vg.mem sa.vg.mem k np fp n ga := by
    rw [amem]; exact hM.write hnp hfp sepN (by omega) _
  have ara := ar.frame aF
  have hspa : sa.vg.gpr .rsp = fp := (aF.gpr .rsp (by simp)).trans hrsp
  have hI0 : TailInv sa sa k np fp n ga 8 (p + 15) 0 :=
    ⟨Frame.refl _ _, by rw [acx]; rfl, fun _ => by rw [adx, hga, Function.update_of_ne (by omega)], acf, aof, ga,
      hMa.refl, fun _ _ => rfl, by simp [val, gsum]⟩
  obtain ⟨sb, hxb, hIb⟩ := tailLoop_ok sa k 8 (p + 15) ap np fp n ga (by omega) (by omega) (by omega)
    ara hspa abp asi adi hI0
  obtain ⟨hFb, hcxb, -, -, -, gb, hMb, hgb, hvb⟩ := hIb
  have arb := ara.frame hFb
  have hspb : sb.vg.gpr .rsp = fp := (hFb.gpr .rsp (by simp)).trans hspa
  obtain ⟨sc, hxc, ccf, cmem, cF⟩ := tailEnd_ok sb k ap np fp gb arb hspb hMb.fw
  have hbpb : sb.vg.gpr .rbp = wa np 8 := (hFb.gpr .rbp (by simp)).trans abp
  have hgb_ga : ∀ i, i < p + 15 → gb i = ga i := fun i hi => hgb i (Or.inl hi)
  have hga_g : ∀ i, i ≠ 3 → ga i = g₁ i := fun i hi => by rw [hga, Function.update_of_ne hi]
  have hgb1 : gb 1 = wa np (k - 8) := by rw [hgb_ga 1 (by omega), hga_g 1 (by omega), hg1]
  refine ⟨sa, sb, sc, Exec.block hxa, hxb, Exec.block hxc, (aF.toRL.trans hFb.toRL).trans cF.toRL, ?_, ?_, ?_, ?_,
    ?_, gb, ?_, ?_, ?_⟩
  · rw [cF.gpr .rbp (nil_nm _), hbpb]
  · rw [cF.gpr .rdi (nil_nm _), hFb.gpr .rdi (by simp), adi]
  · rw [cF.gpr .rsi (nil_nm _), hFb.gpr .rsi (by simp), asi]
  · rw [cF.gpr .rcx (nil_nm _), hcxb]; decide
  · rw [ccf, hbpb, hgb1, cmp_np hnp (by omega) (by omega)]; congr 1; exact decide_eq_decide.mpr (by omega)
  · rw [cmem]; exact hMa.trans hMb
  · intro i h3 hi
    rw [hgb i (by omega), hga_g i h3]
  · have hregs : regs sc = regs sb := by
      simp only [regs, cF.gpr .r8 (nil_nm _), cF.gpr .r9 (nil_nm _), cF.gpr .r10 (nil_nm _),
        cF.gpr .r11 (nil_nm _), cF.gpr .r12 (nil_nm _), cF.gpr .r13 (nil_nm _), cF.gpr .r14 (nil_nm _),
        cF.gpr .r15 (nil_nm _)]
    have hrega : regs sa = A.val := by simp only [regs, a8, a9, a10, a11, a12, a13, a14, a15, Acc.val]
    have hadd := add8'_acct (s₁.vg.gpr .r8) (s₁.vg.gpr .r9) (s₁.vg.gpr .r10) (s₁.vg.gpr .r11) (s₁.vg.gpr .r12)
      (s₁.vg.gpr .r13) (s₁.vg.gpr .r14) (s₁.vg.gpr .r15) (g₁ (p + 15)) (g₁ (p + 15 + 1)) (g₁ (p + 15 + 2))
      (g₁ (p + 15 + 3)) (g₁ (p + 15 + 4)) (g₁ (p + 15 + 5)) (g₁ (p + 15 + 6)) (g₁ (p + 15 + 7))
    dsimp only at hadd
    rw [← hA, hsum8_val g₁ (p + 15)] at hadd
    have hQ : val (fun i => ga (7 + i)) 8 = val (fun i => g₁ (7 + i)) 8 :=
      val_eq fun i _ => hga_g _ (by omega)
    have hNn : hsum [n 8, n (8 + 1), n (8 + 2), n (8 + 3), n (8 + 4), n (8 + 5), n (8 + 6), n (8 + 7)] =
        val (fun i => n (8 + i)) 8 := hsum8_val n 8
    have hu : unmask (gb 3) = A.c := by
      rw [hgb_ga 3 (by omega), hga, Function.update_self, unmask_mask]
    rw [hrega, hQ, hNn] at hvb
    norm_num only at hvb
    rw [hregs, hu]
    norm_num only
    exact tf_arith _ _ _ _ _ _ _ _ hvb hadd

/-- What the tail leaves for `noTail`, from `s₁`, after `redEnd`, with the window at `t`'s word `p`: `rdi` at
`t`'s word `p + k`, `rbp` at `n`'s last eight words, `rax` a bit and the carry `cc` in CF, slot 3 and `t`'s words
`p + 8` to `p + k` changed, and the stores, accumulator, `rax`, and carry as much as the words they replaced, the
accumulator at the start, the multipliers' multiples of `n`'s words from 8, and slot 4's top carry. -/
structure PreNT (s₁ s : S) (k p : Nat) (np fp : Addr) (n g₁ : Nat → BitVec 64) (cc : Bool) : Prop where
  frame : Frame s₁ s RL
  rdi : s.vg.gpr .rdi = wa fp (p + k + 7)
  rbp : s.vg.gpr .rbp = wa np (k - 8)
  rax : (s.vg.gpr .rax).toNat ≤ 1
  cf : s.vg.cf = some cc
  mem : ∃ g', Mems s₁.vg.mem s.vg.mem k np fp n g' ∧
    (∀ i, i ≠ 3 → (i < p + 15 ∨ p + k + 7 ≤ i) → g' i = g₁ i) ∧
    val (fun i => g' (p + 15 + i)) (k - 8) +
        2 ^ (64 * (k - 8)) * (regs s + 2 ^ 512 * (s.vg.gpr .rax).toNat + cc.toNat) =
      val (fun i => g₁ (p + 15 + i)) (k - 8) + regs s₁ +
        val (fun i => g₁ (7 + i)) 8 * val (fun i => n (8 + i)) (k - 8) + 2 ^ (64 * (k - 8)) * (g₁ 4).toNat

/-- The tail's trace. -/
def tailSegTrace (np fp : Addr) (k p : Nat) : List Leak :=
  tailHeadTrace fp (p + 15) ++ (tailLoopTrace np fp 8 (p + 15) ++ (tailEndTrace fp ++
    ((if k = 16 then [.branch true] else .branch false :: loopTrace (tailPassTrace np fp p) 8 8 (k / 8 - 3)) ++
      tailDoneTrace fp)))

set_option exponentiation.threshold 1024 in
theorem td_arith (V W rd Ac cc rt g4 R : Nat) (eDone : rd + 2 ^ 512 * Ac = rt + g4)
    (eTP : V + W * (rt + cc) = R) : V + W * (rd + 2 ^ 512 * Ac + cc) = R + W * g4 := by
  zify at eDone eTP ⊢
  linear_combination (W : ℤ) * eDone + eTP

/-- The tail's program. -/
abbrev tailSeg : Prog I :=
  .seq (.block Rind.X86_64.Sqrx8x.tailHead) (.seq (.loop (.block Rind.X86_64.Sqrx8x.tail) (.vg .ne))
    (.seq (.block Rind.X86_64.Sqrx8x.tailEnd) (.seq (.ite (.vg .ae) (.block [])
      (.loop Rind.X86_64.Sqrx8x.tailPass (.vg .b))) (.block Rind.X86_64.Sqrx8x.tailDone))))

set_option maxHeartbeats 1000000 in
/-- The tail, for `k` from 16. -/
theorem tailSeg_ok (s₁ : S) (k p : Nat) (ap np fp : Addr) (n g₁ : Nat → BitVec 64)
    (hk : 16 ≤ k) (hk8 : k % 8 = 0) (hp : p + 8 ≤ k) (ar : Arr s₁ k ap np fp) (hrsp : s₁.vg.gpr .rsp = fp)
    (hrdi : s₁.vg.gpr .rdi = wa fp (p + 15)) (hrbp : s₁.vg.gpr .rbp = np) (hrax : s₁.vg.gpr .rax = 0)
    (hM : Mems s₁.vg.mem s₁.vg.mem k np fp n g₁) (hg1 : g₁ 1 = wa np (k - 8)) :
    ∃ s₂ cc, Exec I tailSeg s₁ (tailSegTrace np fp k p) s₂ ∧ PreNT s₁ s₂ k p np fp n g₁ cc := by
  obtain ⟨sa, sb, sc, xa, xb, xc, hI8⟩ := tailFirst_ok s₁ k p ap np fp n g₁ hk hp ar hrsp hrdi hrbp hrax hM hg1
  have hT : ∃ st, Exec I (.ite (.vg .ae) (.block []) (.loop Rind.X86_64.Sqrx8x.tailPass (.vg .b))) sc
      (if k = 16 then [.branch true] else .branch false :: loopTrace (tailPassTrace np fp p) 8 8 (k / 8 - 3)) st ∧
      TPInv s₁ st k p np fp n g₁ (k - 8) := by
    have hcf := hI8.cf
    by_cases h16 : k = 16
    · subst h16
      refine ⟨sc, ?_, hI8⟩
      simp only [↓reduceIte]
      exact Exec.iteT (by simp [Rind.X86_64.isa, Rind.X86_64.eval, VG.X86_64.eval, hcf])
        (Exec.block (is := []) (s := sc) (s' := sc) (t := []) rfl)
    · simp only [h16, ↓reduceIte]
      obtain ⟨st, hx, hI⟩ := loop_ok (body := Rind.X86_64.Sqrx8x.tailPass) (c := .vg .b)
        (fun c s => TPInv s₁ s k p np fp n g₁ c) (fun c => c + 16 ≤ k) (fun c => decide (c + 16 < k))
        (tailPassTrace np fp p) 8
        (fun c s hI hc => tailPass_step s₁ s k p c ap np fp n g₁ (by omega) hp hc ar hrsp hg1 hI)
        (k / 8 - 3) 8 sc hI8 (fun i hi => by omega) (fun i hi => by simp; omega) (by simp; omega)
      refine ⟨st, Exec.iteF (by simp [Rind.X86_64.isa, Rind.X86_64.eval, VG.X86_64.eval, hcf]; omega) hx, ?_⟩
      rwa [show 8 + 8 * (k / 8 - 3 + 1) = k - 8 by omega] at hI
  obtain ⟨st, xt, hIt⟩ := hT
  obtain ⟨hFt, hbpt, hdit, hsit, -, -, g', hM', hg', hv⟩ := hIt
  have art := ar.frame hFt
  have hspt : st.vg.gpr .rsp = fp := (hFt.gpr .rsp (by simp)).trans hrsp
  obtain ⟨sd, xd, dmem, d8, d9, d10, d11, d12, d13, d14, d15, dax, dcf, dF⟩ :=
    tailDone_ok st k ap np fp g' art hspt hsit hM'.fw
  set A := add8' (st.vg.gpr .r8) (st.vg.gpr .r9) (st.vg.gpr .r10) (st.vg.gpr .r11) (st.vg.gpr .r12)
    (st.vg.gpr .r13) (st.vg.gpr .r14) (st.vg.gpr .r15) (g' 4) 0 0 0 0 0 0 0 with hA
  refine ⟨sd, unmask (g' 3), Exec.seq xa (Exec.seq xb (Exec.seq xc (Exec.seq xt (Exec.block xd)))),
    hFt.trans dF.toRL, ?_, ?_, ?_, dcf, g', ?_, fun i h3 hi => hg' i h3 (by omega), ?_⟩
  · rw [dF.gpr .rdi (by simp), hdit, show p + (k - 8) + 15 = p + k + 7 by omega]
  · rw [dF.gpr .rbp (by simp), hbpt]
  · rw [dax, ofBool_toNat]; exact Bool.toNat_le _
  · rw [dmem]; exact hM'
  · have hadd := add8'_acct (st.vg.gpr .r8) (st.vg.gpr .r9) (st.vg.gpr .r10) (st.vg.gpr .r11) (st.vg.gpr .r12)
      (st.vg.gpr .r13) (st.vg.gpr .r14) (st.vg.gpr .r15) (g' 4) 0 0 0 0 0 0 0
    dsimp only at hadd
    rw [← hA] at hadd
    have hrd : regs sd = A.val := by simp only [regs, d8, d9, d10, d11, d12, d13, d14, d15, Acc.val]
    have h4 : hsum [g' 4, 0, 0, 0, 0, 0, 0, 0] = (g₁ 4).toNat := by
      rw [hg' 4 (by omega) (by omega)]; simp [hsum]
    rw [h4] at hadd
    rw [hrd, dax, ofBool_toNat]
    exact td_arith _ _ _ _ _ _ _ _ hadd hv

end rind.x86_64.sqrx8x
