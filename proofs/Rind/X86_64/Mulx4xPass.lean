import Rind.X86_64.Mulx4xLoop

/-! # bn_mulx4x_mont's passes, whole

The first pass, `body0`, its loop of `first`, and `firstTail`; an outer pass, `outerHead`, its loop of `inner`,
and `outerTail`; and the loop of outer passes, which leaves `V = t + 2^(64k)·c` with `V < a + n` and
`2^(64k)·V = a·b + Q·n`. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.mul4x

set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 512

namespace rind.x86_64.mulx4x

theorem ofNat_mul8 (k : Nat) : BitVec.ofNat 64 (8 * k) = BitVec.ofNat 64 k * 8#64 := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_mul]; omega

theorem body0F_of (a0 a1 a2 a3 n0 n1 n2 n3 b q : BitVec 64) : (body0F a0 a1 a2 a3 n0 n1 n2 n3 b q).of = false := by
  unfold body0F; exact nhead_of _ _ _ _ _ _ _ _ _ _ _ _

theorem outerHeadF_of (a0 a1 a2 a3 n0 n1 n2 n3 t0 t1 t2 t3 b q : BitVec 64) :
    (outerHeadF a0 a1 a2 a3 n0 n1 n2 n3 t0 t1 t2 t3 b q).of = false := by
  unfold outerHeadF; exact nhead_of _ _ _ _ _ _ _ _ _ _ _ _

/-- `t`'s words after a pass's top word's store. -/
theorem tail_val {M : Mem} {fp : Addr} {K : Nat} (hfp : fp.toNat + 8 * (K + 1 + 9) ≤ 2 ^ 64) (w : BitVec 64) :
    val (tw (M.writeW (wa fp (K + 8)) w) fp) (K + 1) = val (tw M fp) K + w.toNat * 2 ^ (64 * K) := by
  show val (tw (M.writeW (wa fp (K + 8)) w) fp) K + (tw (M.writeW (wa fp (K + 8)) w) fp K).toNat * 2 ^ (64 * K) = _
  rw [show val (tw (M.writeW (wa fp (K + 8)) w) fp) K = val (tw M fp) K from
    gsum_congr fun i hi => by simp only [tw]; rw [readW_wa_ne _ hfp (by omega) (by omega) (by omega)]]
  simp only [tw, readW_writeW_self]

/-- A pass's top word and its identity before it add up to the pass's identity. -/
theorem tail_sum (W A N T b q c top1 top2 cOld K : Nat)
    (hI : 2 ^ 64 * W + 2 ^ (64 * (K + 1)) * c = b * A + q * N + T) (hT : top1 + 2 ^ 64 * top2 = c + cOld) :
    2 ^ 64 * (W + top1 * 2 ^ (64 * K) + 2 ^ (64 * (K + 1)) * top2) = T + 2 ^ (64 * (K + 1)) * cOld + A * b + q * N := by
  have e : 2 ^ (64 * (K + 1)) = 2 ^ (64 * K) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
  rw [e] at hI ⊢
  zify at hI hT ⊢
  linear_combination hI + (2 : ℤ) ^ (64 * K) * 2 ^ 64 * hT

theorem bp_ne (bp : Addr) (i k : Nat) (hi : i < k) (hbp : bp.toNat + 8 * k ≤ 2 ^ 64) :
    (!(wa bp (i + 1) - wa bp k == 0)) = decide (i + 1 < k) := by
  by_cases h : i + 1 < k
  · have : (wa bp (i + 1) - wa bp k == 0) = false := by
      rw [beq_eq_false_iff_ne]; simp only [wa]; bv_omega
    rw [this]; simp [h]
  · obtain rfl : k = i + 1 := by omega
    simp

/-- The loop of outer passes before pass `i`: the words `t` and the top bit `c` the passes so far left, with
their bound and value. -/
structure OInv (s₀ s : S) (k : Nat) (ap bp np fp : Addr) (a bw n : Nat → BitVec 64) (i : Nat) : Prop where
  frame : Frame s₀ s allButSp
  rax : s.vg.gpr .rax = BitVec.ofNat 64 (8 * k)
  rdi : s.vg.gpr .rdi = wa bp i
  rsi : s.vg.gpr .rsi = wa ap k
  rcx : s.vg.gpr .rcx = wa np k
  rbx : s.vg.gpr .rbx = wa fp (k + 8)
  keep : Keep s₀.vg.mem s.vg.mem fp k
  words : ∃ c : Bool, s.vg.gpr .r15 = 0 - (BitVec.ofBool c).setWidth 64 ∧
    val (tw s.vg.mem fp) k + 2 ^ (64 * k) * c.toNat < val a k + val n k ∧
    ∃ Q, 2 ^ (64 * i) * (val (tw s.vg.mem fp) k + 2 ^ (64 * k) * c.toNat) = val a k * val bw i + Q * val n k

/-- The first pass's loop's trace. -/
def firstLoopTrace (ap np fp : Addr) (k : Nat) : List Leak := loopTrace (firstTrace ap np fp) 4 3 ((k - 8) / 4)

set_option maxHeartbeats 4000000 in
/-- The first pass: `body0`, its loop of `first`, and `firstTail`. -/
theorem pass0_ok (s : S) (k : Nat) (ap bp np fp rp sp0 n0' : Addr) (a bw n : Nat → BitVec 64)
    (hk8 : 8 ≤ k) (hk4 : k % 4 = 0) (ar : Arr s k ap bp np fp) (sl : Slots s.vg.mem k bp fp rp sp0 n0')
    (hrsi : s.vg.gpr .rsi = ap) (hrdx : s.vg.gpr .rdx = bp) (hrcx : s.vg.gpr .rcx = np)
    (hrsp : s.vg.gpr .rsp = fp)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hB : ∀ i < k, s.vg.mem.readW (wa bp i) 64 = bw i)
    (hn0 : ((n 0).toNat * n0'.toNat + 1) % 2 ^ 64 = 0) (hpos : 0 < val a k + val n k) :
    ∃ s₁ s₂ s₃, Exec I (.block Rind.X86_64.Mulx4x.body0) s (body0Trace ap bp np fp) s₁ ∧
      Exec I (.loop (.block Rind.X86_64.Mulx4x.first) (Rind.X86_64.Cond.vg .ne)) s₁
        (firstLoopTrace ap np fp k) s₂ ∧
      Exec I (.block Rind.X86_64.Mulx4x.firstTail) s₂ (firstTailTrace fp k) s₃ ∧
      OInv s s₃ k ap bp np fp a bw n 1 := by
  have hfp := ar.hfp
  have hk := ar.k29
  have hA0 : s.vg.mem.readW ap 64 = a 0 := by have := hA 0 (by omega); rwa [wa_zero] at this
  have hN0 : s.vg.mem.readW np 64 = n 0 := by have := hN 0 (by omega); rwa [wa_zero] at this
  have hB0 : s.vg.mem.readW bp 64 = bw 0 := by have := hB 0 (by omega); rwa [wa_zero] at this
  obtain ⟨s₁, hx1, p_si, p_cx, p_bx, p_dx, p_9, p_8, p_bp, p_di, p_14, p_15, p_cf, p_of, pmem, pF⟩ :=
    body0_ok s k (k / 4 - 1) ap bp np fp n0' a bw n hk8 ar hrsi hrdx hrcx hrsp hA hN hA0 hN0 hB0 sl.s3 sl.s6
  have BN := body0_nat (a 0) (a 1) (a 2) (a 3) (n 0) (n 1) (n 2) (n 3) (bw 0) n0' hn0
  dsimp only at BN
  have BO := body0F_of (a 0) (a 1) (a 2) (a 3) (n 0) (n 1) (n 2) (n 3) (bw 0) (mulLo (bw 0) (a 0) * n0')
  generalize mulLo (bw 0) (a 0) * n0' = q at p_8 p_14 p_15 p_cf p_of pmem BN BO
  generalize body0F (a 0) (a 1) (a 2) (a 3) (n 0) (n 1) (n 2) (n 3) (bw 0) q = F at p_14 p_15 p_cf p_of pmem BN BO
  obtain ⟨BW0, BS, BL⟩ := BN
  have ar1 := ar.frame pF
  have g1 : ∀ r, r ∉ allButSp → s₁.vg.gpr r = s.vg.gpr r := pF.gpr
  -- The loop of `first`.
  have hI1 : PInv s₁ s₁ k ap np fp a n (fun _ => 0) (bw 0) q 3 := by
    refine ⟨rfl, by omega, Frame.refl _ _, p_si, p_cx, p_bx, p_dx, ?_, ?_, Agree.refl _ _ _,
      ⟨_, _, _, p_14, p_15, p_cf, BL, ?_⟩⟩
    · rw [p_di]; congr 1; omega
    · rw [p_of, BO]
    · have r : ∀ i, i < 3 → tw s₁.vg.mem fp i = [F.w1, F.w2, F.w3].getD i 0 := by
        intro i hi
        simp only [tw, pmem]
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        · rw [readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega),
            readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega), readW_writeW_self]; rfl
        · rw [readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega), readW_writeW_self]; rfl
        · rw [readW_writeW_self]; rfl
      rw [val_three, r 0 (by omega), r 1 (by omega), r 2 (by omega)]
      show v4 0 F.w1 F.w2 F.w3 + 2 ^ 256 * _ = _ * val a 4 + _ * val n 4 + val (fun _ => 0) 4
      rw [val_four, val_four, val_zero, ← BW0, Nat.add_zero]
      exact BS
  have keep1 : Keep s.vg.mem s₁.vg.mem fp k := by
    rw [pmem]
    exact ((((Keep.refl _ _ _).write1 _).writeT (i := 0) _ (by omega)).writeT (i := 1) _ (by omega)).writeT
      (i := 2) _ (by omega)
  obtain ⟨s₂, hx2, hI2⟩ := loop_ok (body := .block Rind.X86_64.Mulx4x.first) (c := Rind.X86_64.Cond.vg .ne)
    (fun j s => PInv s₁ s k ap np fp a n (fun _ => 0) (bw 0) q j) (fun j => j + 5 ≤ k) (fun j => decide (j + 5 < k))
    (firstTrace ap np fp) 4
    (fun j s' hI hR => first_step s₁ k ap bp np fp (bw 0) q a n ar1 p_9 p_8 p_bp
      (fun i hi => (keep1.arr hfp ar.hap ar.sepA hi).trans (hA i hi))
      (fun i hi => (keep1.arr hfp ar.hnp ar.sepN hi).trans (hN i hi)) hk4 j s' hI hR)
    ((k - 8) / 4) 3 s₁ hI1 (fun i hi => by omega) (fun i hi => by simp; omega) (by simp; omega)
  rw [show 3 + 4 * ((k - 8) / 4 + 1) = k - 1 by omega] at hI2
  have F2 := hI2.frame
  have ar2 := ar1.frame F2
  have keep2 : Keep s.vg.mem s₂.vg.mem fp k := keep1.agree hI2.agree (by omega)
  have sl2 := sl.keep keep2 hfp
  have h0 : s₂.vg.mem.readW fp 64 = BitVec.ofNat 64 (8 * k) := by have := sl2.s0; rwa [wa_zero] at this
  have h1 : s₂.vg.mem.readW (wa fp 1) 64 = wa bp 1 := by
    rw [hI2.agree.slotF (k := k) (i := 1) (by omega) hfp (by omega), pmem,
      readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega),
      readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega),
      readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega), readW_writeW_self]
  obtain ⟨cA, cN, cf, h14, h15, hcf, hlt, hsum⟩ := hI2.sum
  obtain ⟨s₃, hx3, oax, odi, o14, o15, omem, oF⟩ :=
    firstTail_ok s₂ k ap bp np fp cA cN _ _ cf hk8 ar2
      ((F2.gpr .rsp (by decide)).trans ((g1 .rsp (by decide)).trans hrsp))
      (by rw [hI2.rbx, show k - 1 + 9 = k + 8 by omega]) ((F2.gpr .rbp (by decide)).trans p_bp) h14 h15 hcf h0 h1
  refine ⟨s₁, s₂, s₃, Exec.block hx1, hx2, Exec.block hx3,
    ⟨pF.trans ((F2.mono (by decide)).trans (oF.mono (by decide))), oax, odi, ?_, ?_, ?_, ?_, ⟨_, o15, ?_⟩⟩⟩
  · rw [oF.gpr .rsi (by decide), hI2.rsi, show k - 1 + 1 = k by omega]
  · rw [oF.gpr .rcx (by decide), hI2.rcx, show k - 1 + 1 = k by omega]
  · rw [oF.gpr .rbx (by decide), hI2.rbx, show k - 1 + 9 = k + 8 by omega]
  · rw [omem, show k + 7 = k - 1 + 8 by omega]; exact keep2.writeT _ (by omega)
  -- The pass's arithmetic.
  have TV := tail_val (M := s₂.vg.mem) (fp := fp) (K := k - 1) (by omega) (topF cA cN cf).1
  rw [show k - 1 + 1 = k by omega, show k - 1 + 8 = k + 7 by omega, ← omem] at TV
  have TN := topF_nat cA cN cf hlt
  have H := tail_sum _ _ _ _ _ _ _ _ _ 0 (k - 1) hsum (by rw [TN]; ring)
  rw [show k - 1 + 1 = k by omega, ← TV, val_zero] at H
  obtain ⟨m1, m2⟩ := mont_step (val a k) (val n k) 0 _ 0 0 (bw 0).toNat q.toNat 0 (bw 0).isLt q.isLt
    (by rw [H]; ring) hpos (by simp)
  exact ⟨m1, _, m2⟩

/-- An outer pass's trace. -/
def passTrace (ap bp np fp : Addr) (k i : Nat) : List Leak :=
  outerHeadTrace ap bp np fp k i ++ (loopTrace (innerTrace ap np fp) 4 3 ((k - 8) / 4) ++ outerTailTrace fp k)

set_option maxHeartbeats 4000000 in
/-- Outer pass `i`: `outerHead`, its loop of `inner`, and `outerTail`. -/
theorem outer_step (s₀ : S) (k : Nat) (ap bp np fp rp sp0 n0' : Addr) (a bw n : Nat → BitVec 64)
    (hk8 : 8 ≤ k) (hk4 : k % 4 = 0) (ar : Arr s₀ k ap bp np fp) (sl : Slots s₀.vg.mem k bp fp rp sp0 n0')
    (hrsp : s₀.vg.gpr .rsp = fp)
    (hA : ∀ i < k, s₀.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s₀.vg.mem.readW (wa np i) 64 = n i)
    (hB : ∀ i < k, s₀.vg.mem.readW (wa bp i) 64 = bw i)
    (hn0 : ((n 0).toNat * n0'.toNat + 1) % 2 ^ 64 = 0)
    (i : Nat) (s : S) (hI : OInv s₀ s k ap bp np fp a bw n i) (hi : i < k) :
    ∃ s', Exec I Rind.X86_64.Mulx4x.pass s (passTrace ap bp np fp k i) s' ∧
      I.eval (Rind.X86_64.Cond.vg .ne) s' = some (decide (i + 1 < k)) ∧
      OInv s₀ s' k ap bp np fp a bw n (i + 1) := by
  obtain ⟨hF, hax, hdi, hsi, hcx, hbx, hkeep, c, h15, hV, Q, hQ⟩ := hI
  have hfp := ar.hfp
  have hk := ar.k29
  have g : ∀ r, r ∉ allButSp → s.vg.gpr r = s₀.vg.gpr r := hF.gpr
  have sl1 := sl.keep hkeep hfp
  have hA' : ∀ j < k, s.vg.mem.readW (wa ap j) 64 = a j := fun j hj =>
    (hkeep.arr hfp ar.hap ar.sepA hj).trans (hA j hj)
  have hN' : ∀ j < k, s.vg.mem.readW (wa np j) 64 = n j := fun j hj =>
    (hkeep.arr hfp ar.hnp ar.sepN hj).trans (hN j hj)
  have hB' : ∀ j < k, s.vg.mem.readW (wa bp j) 64 = bw j := fun j hj =>
    (hkeep.arr hfp ar.hbp ar.sepB hj).trans (hB j hj)
  have hA0 : s.vg.mem.readW ap 64 = a 0 := by have := hA' 0 (by omega); rwa [wa_zero] at this
  have hN0 : s.vg.mem.readW np 64 = n 0 := by have := hN' 0 (by omega); rwa [wa_zero] at this
  obtain ⟨s₁, hx1, p_si, p_cx, p_bx, p_dx, p_9, p_8, p_bp, p_di, p_14, p_15, p_cf, p_of, pmem, pF⟩ :=
    outerHead_ok s k i (k / 4 - 1) ap bp np fp n0' (0 - (BitVec.ofBool c).setWidth 64) a bw n
      (fun j => tw s.vg.mem fp (j - 8)) hk8 hi (ar.frame hF) hdi hsi hcx (by rw [hax, ofNat_mul8]) hbx h15
      ((g .rsp (by decide)).trans hrsp) hA' hN' hB' hA0 hN0
      (fun j h1 h2 => by show _ = s.vg.mem.readW (wa fp (j - 8 + 8)) 64; rw [show j - 8 + 8 = j by omega])
      sl1.s3 sl1.s6
  simp only [Nat.reduceSub] at p_8 p_14 p_15 p_cf p_of pmem
  have ON := outerHead_nat (a 0) (a 1) (a 2) (a 3) (n 0) (n 1) (n 2) (n 3) (tw s.vg.mem fp 0) (tw s.vg.mem fp 1)
    (tw s.vg.mem fp 2) (tw s.vg.mem fp 3) (bw i) n0' hn0
  dsimp only at ON
  have OO := outerHeadF_of (a 0) (a 1) (a 2) (a 3) (n 0) (n 1) (n 2) (n 3) (tw s.vg.mem fp 0) (tw s.vg.mem fp 1)
    (tw s.vg.mem fp 2) (tw s.vg.mem fp 3) (bw i) (outerHeadX (a 0) (tw s.vg.mem fp 0) (bw i) * n0')
  generalize outerHeadX (a 0) (tw s.vg.mem fp 0) (bw i) * n0' = q at p_8 p_14 p_15 p_cf p_of pmem ON OO
  generalize outerHeadF (a 0) (a 1) (a 2) (a 3) (n 0) (n 1) (n 2) (n 3) (tw s.vg.mem fp 0) (tw s.vg.mem fp 1)
    (tw s.vg.mem fp 2) (tw s.vg.mem fp 3) (bw i) q = F at p_14 p_15 p_cf p_of pmem ON OO
  obtain ⟨OW0, OS, OL⟩ := ON
  have ar1 := (ar.frame hF).frame pF
  have hI1 : PInv s₁ s₁ k ap np fp a n (tw s.vg.mem fp) (bw i) q 3 := by
    refine ⟨rfl, by omega, Frame.refl _ _, p_si, p_cx, p_bx, p_dx, ?_, ?_, Agree.refl _ _ _,
      ⟨_, _, _, p_14, p_15, p_cf, OL, ?_⟩⟩
    · rw [p_di]; congr 1; omega
    · rw [p_of, OO]
    · have r : ∀ i, i < 3 → tw s₁.vg.mem fp i = [F.w1, F.w2, F.w3].getD i 0 := by
        intro i hi
        simp only [tw, pmem]
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        · rw [readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega),
            readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega), readW_writeW_self]; rfl
        · rw [readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega), readW_writeW_self]; rfl
        · rw [readW_writeW_self]; rfl
      rw [val_three, r 0 (by omega), r 1 (by omega), r 2 (by omega)]
      show v4 0 F.w1 F.w2 F.w3 + 2 ^ 256 * _ = _ * val a 4 + _ * val n 4 + val (tw s.vg.mem fp) 4
      rw [val_four, val_four, val_four, ← OW0]
      exact OS
  have hT1 : ∀ j, 3 ≤ j → j < k → s₁.vg.mem.readW (wa fp (j + 8)) 64 = tw s.vg.mem fp j := by
    intro j h1 h2
    rw [pmem, readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega),
      readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega),
      readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega),
      readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega),
      readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega)]
  have keep1 : Keep s.vg.mem s₁.vg.mem fp k := by
    rw [pmem]
    exact (((((Keep.refl _ _ _).writeT (i := k) _ (by omega)).write1 _).writeT (i := 0) _ (by omega)).writeT
      (i := 1) _ (by omega)).writeT (i := 2) _ (by omega)
  have keep1' := hkeep.trans keep1
  obtain ⟨s₂, hx2, hI2⟩ := loop_ok (body := .block Rind.X86_64.Mulx4x.inner) (c := Rind.X86_64.Cond.vg .ne)
    (fun j s' => PInv s₁ s' k ap np fp a n (tw s.vg.mem fp) (bw i) q j) (fun j => j + 5 ≤ k)
    (fun j => decide (j + 5 < k)) (innerTrace ap np fp) 4
    (fun j s' hI hR => inner_step s₁ k ap bp np fp (bw i) q a n (tw s.vg.mem fp) ar1 p_9 p_8 p_bp
      (fun i hi => (keep1'.arr hfp ar.hap ar.sepA hi).trans (hA i hi))
      (fun i hi => (keep1'.arr hfp ar.hnp ar.sepN hi).trans (hN i hi)) hT1 hk4 j s' hI hR)
    ((k - 8) / 4) 3 s₁ hI1 (fun i hi => by omega) (fun i hi => by simp; omega) (by simp; omega)
  rw [show 3 + 4 * ((k - 8) / 4 + 1) = k - 1 by omega] at hI2
  have F2 := hI2.frame
  have ar2 := ar1.frame F2
  have keep2 : Keep s₀.vg.mem s₂.vg.mem fp k := keep1'.agree hI2.agree (by omega)
  have sl2 := sl.keep keep2 hfp
  have h0 : s₂.vg.mem.readW fp 64 = BitVec.ofNat 64 (8 * k) := by have := sl2.s0; rwa [wa_zero] at this
  have h1 : s₂.vg.mem.readW (wa fp 1) 64 = wa bp (i + 1) := by
    rw [hI2.agree.slotF (k := k) (i := 1) (by omega) hfp (by omega), pmem,
      readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega),
      readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega),
      readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega), readW_writeW_self]
  have hT : s₂.vg.mem.readW (wa fp (k + 8)) 64 = 0 - (BitVec.ofBool c).setWidth 64 := by
    rw [hI2.agree.twF (k := k) (i := k) (by omega) (le_refl _) hfp, pmem,
      readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega),
      readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega),
      readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega),
      readW_wa_ne (L := k + 9) _ hfp (by omega) (by omega) (by omega), readW_writeW_self]
  obtain ⟨cA, cN, cf, h14, h15', hcf, hlt, hsum⟩ := hI2.sum
  obtain ⟨s₃, hx3, oax, odi, o14, o15, ozf, omem, oF⟩ :=
    outerTail_ok s₂ k ap bp np fp cA cN _ _ _ _ cf hk8 ar2
      ((F2.gpr .rsp (by decide)).trans ((pF.gpr .rsp (by decide)).trans ((g .rsp (by decide)).trans hrsp)))
      (by rw [hI2.rbx, show k - 1 + 9 = k + 8 by omega]) ((F2.gpr .rbp (by decide)).trans p_bp) h14 h15' hcf h0 h1
      sl2.s2 hT
  refine ⟨s₃, Exec.seq (Exec.block hx1) (Exec.seq hx2 (Exec.block hx3)), ?_,
    ⟨hF.trans (pF.trans ((F2.mono (by decide)).trans (oF.mono (by decide)))), oax, odi, ?_, ?_, ?_, ?_,
      ⟨_, o15, ?_⟩⟩⟩
  · rw [eval_ne ozf, bp_ne bp i k hi ar.hbp]
  · rw [oF.gpr .rsi (by decide), hI2.rsi, show k - 1 + 1 = k by omega]
  · rw [oF.gpr .rcx (by decide), hI2.rcx, show k - 1 + 1 = k by omega]
  · rw [oF.gpr .rbx (by decide), hI2.rbx, show k - 1 + 9 = k + 8 by omega]
  · rw [omem, show k + 7 = k - 1 + 8 by omega]; exact keep2.writeT _ (by omega)
  -- The pass's arithmetic.
  have TV := tail_val (M := s₂.vg.mem) (fp := fp) (K := k - 1) (by omega) (topT cA cN (0 - (BitVec.ofBool c).setWidth 64) cf).1
  rw [show k - 1 + 1 = k by omega, show k - 1 + 8 = k + 7 by omega, ← omem] at TV
  have TN := topT_nat cA cN cf c hlt
  have H := tail_sum _ _ _ _ _ _ _ _ _ c.toNat (k - 1) hsum TN
  rw [show k - 1 + 1 = k by omega, ← TV] at H
  obtain ⟨m1, m2⟩ := mont_step (val a k) (val n k) _ _ (val bw i) Q (bw i).toNat q.toNat i (bw i).isLt q.isLt
    H hV hQ
  exact ⟨m1, _, m2⟩

/-- The loop of outer passes' trace. -/
def outerTrace (ap bp np fp : Addr) (k : Nat) : List Leak := loopTrace (passTrace ap bp np fp k) 1 1 (k - 2)

/-- The loop of outer passes, from pass 1 to pass `k - 1`. -/
theorem outer_ok (s₀ : S) (k : Nat) (ap bp np fp rp sp0 n0' : Addr) (a bw n : Nat → BitVec 64)
    (hk8 : 8 ≤ k) (hk4 : k % 4 = 0) (ar : Arr s₀ k ap bp np fp) (sl : Slots s₀.vg.mem k bp fp rp sp0 n0')
    (hrsp : s₀.vg.gpr .rsp = fp)
    (hA : ∀ i < k, s₀.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s₀.vg.mem.readW (wa np i) 64 = n i)
    (hB : ∀ i < k, s₀.vg.mem.readW (wa bp i) 64 = bw i)
    (hn0 : ((n 0).toNat * n0'.toNat + 1) % 2 ^ 64 = 0) (s₁ : S) (hI : OInv s₀ s₁ k ap bp np fp a bw n 1) :
    ∃ s', Exec I (.loop Rind.X86_64.Mulx4x.pass (Rind.X86_64.Cond.vg .ne)) s₁ (outerTrace ap bp np fp k) s' ∧
      OInv s₀ s' k ap bp np fp a bw n k := by
  obtain ⟨s', hx, hI'⟩ := loop_ok (body := Rind.X86_64.Mulx4x.pass) (c := Rind.X86_64.Cond.vg .ne)
    (fun i s => OInv s₀ s k ap bp np fp a bw n i) (fun i => i < k) (fun i => decide (i + 1 < k))
    (passTrace ap bp np fp k) 1
    (fun i s hI hi => outer_step s₀ k ap bp np fp rp sp0 n0' a bw n hk8 hk4 ar sl hrsp hA hN hB hn0 i s hI hi)
    (k - 2) 1 s₁ hI (fun i hi => by omega) (fun i hi => by simp; omega) (by simp; omega)
  rw [show 1 + 1 * (k - 2 + 1) = k by omega] at hI'
  exact ⟨s', hx, hI'⟩

end rind.x86_64.mulx4x
