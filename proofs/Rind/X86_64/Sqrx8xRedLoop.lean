import Rind.X86_64.Sqrx8xRedAsm

/-! # bn_sqrx8x_internal's reduction loops

The frame's words as a function of their index, kept across stores; the loop of `red`, which takes eight
multipliers and adds their multiples of `n`'s first eight words; and the loop of `tail`, which adds the same
multipliers' multiples of `n`'s next eight words. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.sqrx8x

/-! ## Memory -/

/-- The frame's `2k + 9` words are `g` of their index. -/
def FW (M : Mem) (k : Nat) (fp : Addr) (g : Nat → BitVec 64) : Prop :=
  ∀ i < 2 * k + 9, M.readW (wa fp i) 64 = g i

theorem FW.write {M : Mem} {k : Nat} {fp : Addr} {g : Nat → BitVec 64} (h : FW M k fp g)
    (hfp : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 64) {j : Nat} (hj : j < 2 * k + 9) (v : BitVec 64) :
    FW (M.writeW (wa fp j) v) k fp (Function.update g j v) := by
  intro i hi
  by_cases e : i = j
  · subst e; rw [readW_writeW_self, Function.update_self]
  · rw [Function.update_of_ne e,
      readW_writeW_sep _ _ _ _ (by unfold Apart; simp only [wa]; constructor <;> bv_omega)]
    exact h i hi

/-- `n`'s `k` words are `n`. -/
def NW (M : Mem) (k : Nat) (np : Addr) (n : Nat → BitVec 64) : Prop :=
  ∀ i < k, M.readW (wa np i) 64 = n i

theorem NW.write {M : Mem} {k : Nat} {np fp : Addr} {n : Nat → BitVec 64} (h : NW M k np n)
    (hnp : np.toNat + 8 * k ≤ 2 ^ 64) (hfp : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 64)
    (sepN : np.toNat + 8 * k ≤ fp.toNat ∨ fp.toNat + 8 * (2 * k + 9) ≤ np.toNat) {j : Nat}
    (hj : j < 2 * k + 9) (v : BitVec 64) : NW (M.writeW (wa fp j) v) k np n := by
  intro i hi
  rw [readW_writeW_sep _ _ _ _ (by unfold Apart; simp only [wa]; constructor <;> bv_omega)]
  exact h i hi

theorem Keeps.refl (M : Mem) (fp : Addr) (k : Nat) : Keeps M M fp k := fun _ _ _ => rfl

theorem Keeps.trans {M₀ M₁ M₂ : Mem} {fp : Addr} {k : Nat} (h₁ : Keeps M₀ M₁ fp k) (h₂ : Keeps M₁ M₂ fp k) :
    Keeps M₀ M₂ fp k := fun y a b => (h₂ y a b).trans (h₁ y a b)

/-- A store to slots 1 to 4 or `t` keeps `Keeps`. -/
theorem Keeps.write {M₀ M : Mem} {fp : Addr} {k j : Nat} (h : Keeps M₀ M fp k)
    (hfp : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 64) (hj : (1 ≤ j ∧ j ≤ 4) ∨ (7 ≤ j ∧ j < 2 * k + 9))
    (v : BitVec 64) : Keeps M₀ (M.writeW (wa fp j) v) fp k := by
  intro y h1 h2
  have e : (M.writeW (wa fp j) v) y = M y := by
    unfold Mem.writeW; apply write_other; simp only [wa]
    rcases hj with hj | hj <;> bv_omega
  rw [e]; exact h y h1 h2

/-- The words a block's stores leave, as `FW`, `NW`, and `Keeps` see them. -/
structure Mems (M₀ M : Mem) (k : Nat) (np fp : Addr) (n g : Nat → BitVec 64) : Prop where
  fw : FW M k fp g
  nw : NW M k np n
  keeps : Keeps M₀ M fp k

theorem Mems.write {M₀ M : Mem} {k : Nat} {np fp : Addr} {n g : Nat → BitVec 64} (h : Mems M₀ M k np fp n g)
    (hnp : np.toNat + 8 * k ≤ 2 ^ 64) (hfp : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 64)
    (sepN : np.toNat + 8 * k ≤ fp.toNat ∨ fp.toNat + 8 * (2 * k + 9) ≤ np.toNat) {j : Nat}
    (hj : (1 ≤ j ∧ j ≤ 4) ∨ (7 ≤ j ∧ j < 2 * k + 9)) (v : BitVec 64) :
    Mems M₀ (M.writeW (wa fp j) v) k np fp n (Function.update g j v) :=
  ⟨h.fw.write hfp (by omega) v, h.nw.write hnp hfp sepN (by omega) v, h.keeps.write hfp hj v⟩

/-! ## Counters -/

theorem rcx_succ (j : Nat) (hj : j < 8) :
    BitVec.ofNat 64 (2 ^ 64 - 8 + j) + 1 = BitVec.ofNat 64 (2 ^ 64 - 8 + (j + 1)) := by
  interval_cases j <;> decide

theorem rcx_ne (j : Nat) (hj : j < 8) :
    (!(BitVec.ofNat 64 (2 ^ 64 - 8 + j) + 1 == 0)) = decide (j + 1 < 8) := by
  interval_cases j <;> decide

/-! ## Sums -/

/-- The accumulator's value. -/
abbrev regs (s : S) : Nat :=
  hsum [s.vg.gpr .r8, s.vg.gpr .r9, s.vg.gpr .r10, s.vg.gpr .r11, s.vg.gpr .r12, s.vg.gpr .r13,
    s.vg.gpr .r14, s.vg.gpr .r15]

theorem hsum8_lt (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 64) : hsum [x0, x1, x2, x3, x4, x5, x6, x7] < 2 ^ 512 := by
  have := x0.isLt; have := x1.isLt; have := x2.isLt; have := x3.isLt
  have := x4.isLt; have := x5.isLt; have := x6.isLt; have := x7.isLt
  simp only [hsum]; omega

/-- A Montgomery step's sum: the low word it drops is zero, and nothing carries out of the ninth. -/
theorem redF_step (q m n0 n1 n2 n3 n4 n5 n6 n7 r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64)
    (hq : q = mulLo r8 m) (hm : (n0.toNat * m.toNat + 1) % 2 ^ 64 = 0) :
    let F := redF q n0 n1 n2 n3 n4 n5 n6 n7 r8 r9 r10 r11 r12 r13 r14 r15 false false
    2 ^ 64 * hsum [F.r8, F.r9, F.r10, F.r11, F.r12, F.r13, F.r14, F.r15] =
      hsum [r8, r9, r10, r11, r12, r13, r14, r15] + q.toNat * hsum [n0, n1, n2, n3, n4, n5, n6, n7] ∧
      F.cf = false ∧ F.of = false := by
  intro F
  have h : hsum [F.w, F.r8, F.r9, F.r10, F.r11, F.r12, F.r13, F.r14, F.r15] + 2 ^ 576 * (F.cf.toNat + F.of.toNat) =
      hsum [r8, r9, r10, r11, r12, r13, r14, r15] + q.toNat * hsum [n0, n1, n2, n3, n4, n5, n6, n7] +
        false.toNat + 2 ^ 64 * false.toNat :=
    redF_acct q n0 n1 n2 n3 n4 n5 n6 n7 r8 r9 r10 r11 r12 r13 r14 r15 false false
  have hw : F.w.toNat = 0 := by
    show (adcS (mulLo q n0) r8 false).toNat = 0
    simp only [adcS, mulLo, hq, BitVec.toNat_add, BitVec.toNat_ofNat, ofBool_toNat, Bool.toNat_false,
      Nat.add_zero, Nat.mod_mod_of_dvd, Nat.mod_mod]
    have := redc_zero r8.toNat m.toNat n0.toNat hm
    rw [Nat.mul_mod (r8.toNat * m.toNat % 2 ^ 64) n0.toNat] at this ⊢
    simpa [Nat.mod_mod, Nat.add_mod] using this
  have hA := hsum8_lt r8 r9 r10 r11 r12 r13 r14 r15
  have hN := hsum8_lt n0 n1 n2 n3 n4 n5 n6 n7
  have hF := hsum8_lt F.r8 F.r9 F.r10 F.r11 F.r12 F.r13 F.r14 F.r15
  have hqN : q.toNat * hsum [n0, n1, n2, n3, n4, n5, n6, n7] ≤ (2 ^ 64 - 1) * (2 ^ 512 - 1) :=
    Nat.mul_le_mul (by have := q.isLt; omega) (by omega)
  have hc := Bool.toNat_le F.cf
  have ho := Bool.toNat_le F.of
  rw [show hsum [F.w, F.r8, F.r9, F.r10, F.r11, F.r12, F.r13, F.r14, F.r15] =
    F.w.toNat + 2 ^ 64 * hsum [F.r8, F.r9, F.r10, F.r11, F.r12, F.r13, F.r14, F.r15] from rfl] at h
  generalize hsum [F.r8, F.r9, F.r10, F.r11, F.r12, F.r13, F.r14, F.r15] = X at h hF ⊢
  generalize hsum [r8, r9, r10, r11, r12, r13, r14, r15] = Y at h hA ⊢
  generalize q.toNat * hsum [n0, n1, n2, n3, n4, n5, n6, n7] = P at h hqN ⊢
  simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at h
  have h1 : F.cf.toNat = 0 := by omega
  have h2 : F.of.toNat = 0 := by omega
  exact ⟨by omega, by simpa using h1, by simpa using h2⟩

/-- A step of the tail's sum: nothing carries out of the ninth word. -/
theorem innerF_step (q n0 n1 n2 n3 n4 n5 n6 n7 r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64) :
    let F := innerF q n0 n1 n2 n3 n4 n5 n6 n7 r8 r9 r10 r11 r12 r13 r14 r15 false false
    F.w.toNat + 2 ^ 64 * hsum [F.r8, F.r9, F.r10, F.r11, F.r12, F.r13, F.r14, F.r15] =
      hsum [r8, r9, r10, r11, r12, r13, r14, r15] + q.toNat * hsum [n0, n1, n2, n3, n4, n5, n6, n7] ∧
      F.cf = false ∧ F.of = false := by
  intro F
  have h : hsum [F.w, F.r8, F.r9, F.r10, F.r11, F.r12, F.r13, F.r14, F.r15] + 2 ^ 576 * (F.cf.toNat + F.of.toNat) =
      hsum [r8, r9, r10, r11, r12, r13, r14, r15] + q.toNat * hsum [n0, n1, n2, n3, n4, n5, n6, n7] +
        false.toNat + 2 ^ 64 * false.toNat :=
    innerF_acct q n0 n1 n2 n3 n4 n5 n6 n7 r8 r9 r10 r11 r12 r13 r14 r15 false false
  have hA := hsum8_lt r8 r9 r10 r11 r12 r13 r14 r15
  have hN := hsum8_lt n0 n1 n2 n3 n4 n5 n6 n7
  have hF := hsum8_lt F.r8 F.r9 F.r10 F.r11 F.r12 F.r13 F.r14 F.r15
  have hqN : q.toNat * hsum [n0, n1, n2, n3, n4, n5, n6, n7] ≤ (2 ^ 64 - 1) * (2 ^ 512 - 1) :=
    Nat.mul_le_mul (by have := q.isLt; omega) (by omega)
  have hc := Bool.toNat_le F.cf
  have ho := Bool.toNat_le F.of
  have hw := F.w.isLt
  rw [show hsum [F.w, F.r8, F.r9, F.r10, F.r11, F.r12, F.r13, F.r14, F.r15] =
    F.w.toNat + 2 ^ 64 * hsum [F.r8, F.r9, F.r10, F.r11, F.r12, F.r13, F.r14, F.r15] from rfl] at h
  generalize hsum [F.r8, F.r9, F.r10, F.r11, F.r12, F.r13, F.r14, F.r15] = X at h hF ⊢
  generalize hsum [r8, r9, r10, r11, r12, r13, r14, r15] = Y at h hA ⊢
  generalize q.toNat * hsum [n0, n1, n2, n3, n4, n5, n6, n7] = P at h hqN ⊢
  simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at h
  have h1 : F.cf.toNat = 0 := by omega
  have h2 : F.of.toNat = 0 := by omega
  exact ⟨by omega, by simpa using h1, by simpa using h2⟩

theorem red_arith (X X' R0 V q N j : Nat) (hs : 2 ^ 64 * X' = X + q * N) (hv : 2 ^ (64 * j) * X = R0 + V * N) :
    2 ^ (64 * (j + 1)) * X' = R0 + (V + q * 2 ^ (64 * j)) * N := by
  rw [show 64 * (j + 1) = 64 * j + 64 by ring, pow_add]
  zify at hs hv ⊢
  linear_combination (2 : ℤ) ^ (64 * j) * hs + hv

theorem tail_arith (X X' R0 V V0 q N w j : Nat) (hs : w + 2 ^ 64 * X' = X + q * N)
    (hv : 2 ^ (64 * j) * X + V = R0 + V0 * N) :
    2 ^ (64 * (j + 1)) * X' + (V + w * 2 ^ (64 * j)) = R0 + (V0 + q * 2 ^ (64 * j)) * N := by
  rw [show 64 * (j + 1) = 64 * j + 64 by ring, pow_add]
  zify at hs hv ⊢
  linear_combination (2 : ℤ) ^ (64 * j) * hs + hv

/-! ## The multipliers' loop -/

/-- The trace of `red`'s loop. -/
def redLoopTrace (np fp : Addr) : List Leak := loopTrace (redTraceJ np fp) 1 0 7

/-- `red`'s loop before its run `j`: `j` multipliers stored in `t`'s first words, and the accumulator times
`2^(64j)` the window plus their multiples of `n`'s first eight words. -/
structure RedInv (s₀ s : S) (k : Nat) (np fp n0 : Addr) (n g : Nat → BitVec 64) (j : Nat) : Prop where
  frame : Frame s₀ s [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]
  rcx : s.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8 + j)
  rdx : s.vg.gpr .rdx = mulLo (s.vg.gpr .r8) n0
  cf : s.vg.cf = some false
  of : s.vg.of = some false
  mem : ∃ g', Mems s₀.vg.mem s.vg.mem k np fp n g' ∧ (∀ i, (i < 7 ∨ 7 + j ≤ i) → g' i = g i) ∧
    2 ^ (64 * j) * regs s =
      regs s₀ + val (fun i => g' (7 + i)) j * hsum [n 0, n 1, n 2, n 3, n 4, n 5, n 6, n 7]

theorem redLoop_ok (s₀ : S) (k : Nat) (ap np fp n0 : Addr) (n g : Nat → BitVec 64) (hk : 8 ≤ k)
    (ar : Arr s₀ k ap np fp) (hrsp : s₀.vg.gpr .rsp = fp) (hrbp : s₀.vg.gpr .rbp = np)
    (hrsi : s₀.vg.gpr .rsi = 0) (hg5 : g 5 = n0) (hn0 : ((n 0).toNat * n0.toNat + 1) % 2 ^ 64 = 0)
    (hI : RedInv s₀ s₀ k np fp n0 n g 0) :
    ∃ s', Exec I (.loop (.block Rind.X86_64.Sqrx8x.red) (.vg .ne)) s₀ (redLoopTrace np fp) s' ∧
      RedInv s₀ s' k np fp n0 n g 8 := by
  have hb := ar
  obtain ⟨hk', hap, hnp, hfp, sepA, sepN, -, -, -, -, -⟩ := hb
  have step : ∀ j s, RedInv s₀ s k np fp n0 n g j → j < 8 →
      ∃ s', Exec I (.block Rind.X86_64.Sqrx8x.red) s (redTraceJ np fp j) s' ∧
        I.eval (.vg .ne) s' = some (decide (j + 1 < 8)) ∧ RedInv s₀ s' k np fp n0 n g (j + 1) := by
    intro j s hI hj
    obtain ⟨hF, hcx, hdx, hcf, hof, g', hM, hg', hv⟩ := hI
    have ar' := ar.frame hF
    have hsp : s.vg.gpr .rsp = fp := (hF.gpr .rsp (by simp)).trans hrsp
    have hbp : s.vg.gpr .rbp = np := (hF.gpr .rbp (by simp)).trans hrbp
    have hsi : s.vg.gpr .rsi = 0 := (hF.gpr .rsi (by simp)).trans hrsi
    have hq : fp + (s.vg.gpr .rcx + 15#64) * 8#64 = wa fp (7 + j) := by
      rw [hcx]; simp only [wa]; bv_omega
    have hN0 : s.vg.mem.readW np 64 = n 0 := by
      have := hM.nw 0 (by omega); rwa [wa_zero] at this
    obtain ⟨s', hx, omem, ocx, odx, osi, o8, o9, o10, o11, o12, o13, o14, o15, ocf, ozf, oof, oF⟩ :=
      redBlock_ok s k j ap np fp (s.vg.gpr .rdx) n g' hj hk ar' hsp hbp rfl hsi hq hcf hof hN0 hM.nw hM.fw
    have hst := redF_step (s.vg.gpr .rdx) n0 (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (s.vg.gpr .r8)
      (s.vg.gpr .r9) (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12) (s.vg.gpr .r13) (s.vg.gpr .r14)
      (s.vg.gpr .r15) hdx hn0
    dsimp only at hst
    obtain ⟨hs, hc, ho⟩ := hst
    refine ⟨s', Exec.block hx, ?_, hF.trans oF, by rw [ocx, hcx, rcx_succ j hj], ?_, by rw [ocf, hc],
      by rw [oof, hcx, rcx_of j hj], Function.update g' (7 + j) (s.vg.gpr .rdx), ?_, ?_, ?_⟩
    · simp only [Rind.X86_64.isa, Rind.X86_64.eval, VG.X86_64.eval, ozf, hcx, Option.map_some]
      exact congrArg some (rcx_ne j hj)
    · rw [odx, o8, hg' 5 (by omega), hg5]
    · rw [omem]; exact hM.write hnp hfp sepN (by omega) _
    · intro i hi; rw [Function.update_of_ne (by omega)]; exact hg' i (by omega)
    · have e1 : gsum (fun i => (Function.update g' (7 + j) (s.vg.gpr .rdx) (7 + i)).toNat) j =
          gsum (fun i => (g' (7 + i)).toNat) j :=
        gsum_congr fun i hi => by rw [Function.update_of_ne (by omega)]
      have e : val (fun i => Function.update g' (7 + j) (s.vg.gpr .rdx) (7 + i)) (j + 1) =
          val (fun i => g' (7 + i)) j + (s.vg.gpr .rdx).toNat * 2 ^ (64 * j) := by
        simp only [val, gsum, Function.update_self, e1]
      simp only [regs] at hv ⊢
      rw [e, o8, o9, o10, o11, o12, o13, o14, o15]
      exact red_arith _ _ _ _ _ _ j hs hv
  obtain ⟨s', hx, hI'⟩ := loop_ok (body := .block Rind.X86_64.Sqrx8x.red) (c := .vg .ne)
    (fun j s => RedInv s₀ s k np fp n0 n g j) (fun j => j < 8) (fun j => decide (j + 1 < 8))
    (redTraceJ np fp) 1 step 7 0 s₀ hI (fun i hi => by omega) (fun i hi => by simp; omega) (by simp)
  exact ⟨s', hx, hI'⟩

/-! ## The tail's loop -/

/-- The trace of `tail`'s loop, at `n`'s word `c`, storing from the frame's word `D`. -/
def tailLoopTrace (np fp : Addr) (c D : Nat) : List Leak := loopTrace (fun j => tailTraceJ np fp c (D + j) j) 1 0 7

/-- `tail`'s loop before its run `j`, at `n`'s word `c`, storing from the frame's word `D`: `j` words stored,
and with the accumulator times `2^(64j)` the accumulator at the start plus the first `j` multipliers' multiples
of `n`'s eight words from `c`. -/
structure TailInv (s₀ s : S) (k : Nat) (np fp : Addr) (n g : Nat → BitVec 64) (c D j : Nat) : Prop where
  frame : Frame s₀ s [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]
  rcx : s.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8 + j)
  rdx : j < 8 → s.vg.gpr .rdx = g (7 + j)
  cf : s.vg.cf = some false
  of : s.vg.of = some false
  mem : ∃ g', Mems s₀.vg.mem s.vg.mem k np fp n g' ∧ (∀ i, (i < D ∨ D + j ≤ i) → g' i = g i) ∧
    2 ^ (64 * j) * regs s + val (fun i => g' (D + i)) j =
      regs s₀ + val (fun i => g (7 + i)) j *
        hsum [n c, n (c + 1), n (c + 2), n (c + 3), n (c + 4), n (c + 5), n (c + 6), n (c + 7)]

theorem tailLoop_ok (s₀ : S) (k c D : Nat) (ap np fp : Addr) (n g : Nat → BitVec 64)
    (hc : c + 8 ≤ k) (hD : 15 ≤ D) (hD' : D + 8 ≤ 2 * k + 9)
    (ar : Arr s₀ k ap np fp) (hrsp : s₀.vg.gpr .rsp = fp) (hrbp : s₀.vg.gpr .rbp = wa np c)
    (hrsi : s₀.vg.gpr .rsi = 0) (hrdi : s₀.vg.gpr .rdi = wa fp (D + 8))
    (hI : TailInv s₀ s₀ k np fp n g c D 0) :
    ∃ s', Exec I (.loop (.block Rind.X86_64.Sqrx8x.tail) (.vg .ne)) s₀ (tailLoopTrace np fp c D) s' ∧
      TailInv s₀ s' k np fp n g c D 8 := by
  have hb := ar
  obtain ⟨hk', hap, hnp, hfp, sepA, sepN, -, -, -, -, -⟩ := hb
  have step : ∀ j s, TailInv s₀ s k np fp n g c D j → j < 8 →
      ∃ s', Exec I (.block Rind.X86_64.Sqrx8x.tail) s (tailTraceJ np fp c (D + j) j) s' ∧
        I.eval (.vg .ne) s' = some (decide (j + 1 < 8)) ∧ TailInv s₀ s' k np fp n g c D (j + 1) := by
    intro j s hI hj
    obtain ⟨hF, hcx, hdx, hcf, hof, g', hM, hg', hv⟩ := hI
    have ar' := ar.frame hF
    have hsp : s.vg.gpr .rsp = fp := (hF.gpr .rsp (by simp)).trans hrsp
    have hbp : s.vg.gpr .rbp = wa np c := (hF.gpr .rbp (by simp)).trans hrbp
    have hsi : s.vg.gpr .rsi = 0 := (hF.gpr .rsi (by simp)).trans hrsi
    have hdi : s.vg.gpr .rdi = wa fp (D + 8) := (hF.gpr .rdi (by simp)).trans hrdi
    have hst : s.vg.gpr .rdi + s.vg.gpr .rcx * 8#64 = wa fp (D + j) := by
      rw [hcx, hdi]; simp only [wa]; bv_omega
    have hld : fp + (s.vg.gpr .rcx + 2#64 * 8#64) * 8#64 = wa fp (8 + j) := by
      rw [hcx]; simp only [wa]; bv_omega
    obtain ⟨s', hx, omem, ocx, odx, osi, o8, o9, o10, o11, o12, o13, o14, o15, ocf, ozf, oof, oF⟩ :=
      redTail_ok s k c (D + j) j ap np fp (s.vg.gpr .rdx) n g' hj hc (by omega) ar' hsp hbp rfl hsi hst hld hcf hof
        hM.nw hM.fw
    have hs := innerF_step (s.vg.gpr .rdx) (n c) (n (c + 1)) (n (c + 2)) (n (c + 3)) (n (c + 4)) (n (c + 5))
      (n (c + 6)) (n (c + 7)) (s.vg.gpr .r8) (s.vg.gpr .r9) (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12)
      (s.vg.gpr .r13) (s.vg.gpr .r14) (s.vg.gpr .r15)
    dsimp only at hs
    obtain ⟨hs, hc', ho⟩ := hs
    set F := innerF (s.vg.gpr .rdx) (n c) (n (c + 1)) (n (c + 2)) (n (c + 3)) (n (c + 4)) (n (c + 5))
      (n (c + 6)) (n (c + 7)) (s.vg.gpr .r8) (s.vg.gpr .r9) (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12)
      (s.vg.gpr .r13) (s.vg.gpr .r14) (s.vg.gpr .r15) false false with hFd
    refine ⟨s', Exec.block hx, ?_, hF.trans oF, by rw [ocx, hcx, rcx_succ j hj], ?_, by rw [ocf, hc'],
      by rw [oof, hcx, rcx_of j hj], Function.update g' (D + j) F.w, ?_, ?_, ?_⟩
    · simp only [Rind.X86_64.isa, Rind.X86_64.eval, VG.X86_64.eval, ozf, hcx, Option.map_some]
      exact congrArg some (rcx_ne j hj)
    · intro hj'; rw [odx, hg' (8 + j) (by omega)]; exact congrArg g (by omega)
    · rw [omem]; exact hM.write hnp hfp sepN (by omega) _
    · intro i hi; rw [Function.update_of_ne (by omega)]; exact hg' i (by omega)
    · have e1 : gsum (fun i => (Function.update g' (D + j) F.w (D + i)).toNat) j =
          gsum (fun i => (g' (D + i)).toNat) j :=
        gsum_congr fun i hi => by rw [Function.update_of_ne (by omega)]
      have e : val (fun i => Function.update g' (D + j) F.w (D + i)) (j + 1) =
          val (fun i => g' (D + i)) j + F.w.toNat * 2 ^ (64 * j) := by
        simp only [val, gsum, Function.update_self, e1]
      have e2 : val (fun i => g (7 + i)) (j + 1) =
          val (fun i => g (7 + i)) j + (g (7 + j)).toNat * 2 ^ (64 * j) := by
        simp only [val, gsum]
      simp only [regs] at hv ⊢
      rw [e, e2, o8, o9, o10, o11, o12, o13, o14, o15, ← hdx hj]
      exact tail_arith _ _ _ _ _ _ _ _ j hs hv
  obtain ⟨s', hx, hI'⟩ := loop_ok (body := .block Rind.X86_64.Sqrx8x.tail) (c := .vg .ne)
    (fun j s => TailInv s₀ s k np fp n g c D j) (fun j => j < 8) (fun j => decide (j + 1 < 8))
    (fun j => tailTraceJ np fp c (D + j) j) 1 step 7 0 s₀ hI (fun i hi => by omega) (fun i hi => by simp; omega)
    (by simp)
  exact ⟨s', hx, hI'⟩

end rind.x86_64.sqrx8x
