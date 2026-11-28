import Rind.X86_64.Sqrx8xRedTail

/-! # bn_sqrx8x_internal's reduction

`redPass`'s loop, which reduces `t`'s `2k` words by `n` eight words at a time. Each round takes the window at
`t`'s word `p`: eight multipliers, which make it zero, saved in `t`'s first eight words; their products with all of
`n`; and the next `k` words of `t`, which the round leaves as the sum shifted down eight words, its top carry in
`rax`. After `k / 8` rounds, `t`'s upper `k` words and `rax` are `(A + Q·n) / 2^(64k)`. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.sqrx8x

theorem mulLo_eq (x y : BitVec 64) : mulLo x y = x * y := by
  apply BitVec.eq_of_toNat_eq; simp [mulLo, BitVec.toNat_mul]

/-- The frame's words after `store8`. -/
def upd8 (g : Nat → BitVec 64) (e : Nat) (A : Acc) : Nat → BitVec 64 :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update g e A.r8) (e + 1) A.r9) (e + 2) A.r10) (e + 3) A.r11) (e + 4) A.r12)
    (e + 5) A.r13) (e + 6) A.r14) (e + 7) A.r15

theorem Mems.store8 {M₀ M : Mem} {k : Nat} {np fp : Addr} {n g : Nat → BitVec 64} (h : Mems M₀ M k np fp n g)
    (hnp : np.toNat + 8 * k ≤ 2 ^ 64) (hfp : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 64)
    (sepN : np.toNat + 8 * k ≤ fp.toNat ∨ fp.toNat + 8 * (2 * k + 9) ≤ np.toNat) {e : Nat} (he : 7 ≤ e)
    (he' : e + 8 ≤ 2 * k + 9) (A : Acc) : Mems M₀ (store8 M fp e A) k np fp n (upd8 g e A) :=
  ((((((((h.write hnp hfp sepN (j := e) (by omega) _).write hnp hfp sepN (j := e + 1) (by omega) _).write hnp hfp
    sepN (j := e + 2) (by omega) _).write hnp hfp sepN (j := e + 3) (by omega) _).write hnp hfp sepN (j := e + 4)
    (by omega) _).write hnp hfp sepN (j := e + 5) (by omega) _).write hnp hfp sepN (j := e + 6) (by omega) _).write
    hnp hfp sepN (j := e + 7) (by omega) _)

theorem upd8_out (g : Nat → BitVec 64) (e : Nat) (A : Acc) {i : Nat} (hi : i < e ∨ e + 8 ≤ i) :
    upd8 g e A i = g i := by
  simp (disch := omega) only [upd8, Function.update_of_ne]

set_option exponentiation.threshold 1024 in
theorem upd8_val (g : Nat → BitVec 64) (e : Nat) (A : Acc) : val (fun i => upd8 g e A (e + i)) 8 = A.val := by
  simp [upd8, val, gsum, Function.update_apply, Acc.val, hsum]
  omega

theorem adcS0_toNat (x : BitVec 64) (c : Bool) (hx : x.toNat ≤ 1) : (adcS x 0 c).toNat = x.toNat + c.toNat := by
  have := Bool.toNat_le c
  simp only [adcS, BitVec.toNat_add, ofBool_toNat]
  rw [show (0 : BitVec 64).toNat = 0 from rfl]
  omega

/-! ## A round's multipliers -/

set_option maxHeartbeats 1000000 in
/-- A round's first part, at the window `t`'s word `p`, `R` the top carry: `redHead`, `red`'s loop, and `redEnd`. -/
theorem roundA_ok (s : S) (k p : Nat) (ap np fp n0 R : Addr) (n g : Nat → BitVec 64) (hk : 8 ≤ k)
    (hp : p + 8 ≤ k) (ar : Arr s k ap np fp) (hrsp : s.vg.gpr .rsp = fp) (hrdi : s.vg.gpr .rdi = wa fp (p + 7))
    (hrbp : s.vg.gpr .rbp = np) (hrbx : s.vg.gpr .rbx = n0) (hrdx : s.vg.gpr .rdx = g (p + 7))
    (hrax : s.vg.gpr .rax = R) (hM : Mems s.vg.mem s.vg.mem k np fp n g) (hg1 : g 1 = wa np (k - 8))
    (hg5 : g 5 = n0) (hn0 : ((n 0).toNat * n0.toNat + 1) % 2 ^ 64 = 0) :
    ∃ sh sr se, Exec I (.block Rind.X86_64.Sqrx8x.redHead) s (redHeadTrace fp p) sh ∧
      Exec I (.loop (.block Rind.X86_64.Sqrx8x.red) (.vg .ne)) sh (redLoopTrace np fp) sr ∧
      Exec I (.block Rind.X86_64.Sqrx8x.redEnd) sr (redEndTrace fp) se ∧
      Frame s se RL ∧ se.vg.gpr .rdi = wa fp (p + 15) ∧ se.vg.gpr .rbp = np ∧ se.vg.gpr .rax = 0 ∧
      se.vg.cf = some (decide (8 < k)) ∧
      ∃ ge, Mems s.vg.mem se.vg.mem k np fp n ge ∧ (∀ i, i ≠ 4 → (i < 7 ∨ 15 ≤ i) → ge i = g i) ∧ ge 4 = R ∧
        2 ^ 512 * regs se = val (fun i => g (p + 7 + i)) 8 + val (fun i => ge (7 + i)) 8 * val n 8 := by
  have hb := ar
  obtain ⟨hk', hap, hnp, hfp, sepA, sepN, -, -, -, -, -⟩ := hb
  obtain ⟨sh, xh, h8, h9, h10, h11, h12, h13, h14, h15, hdx, hdi, hsi, hcx, hcf, hof, hmem, hF⟩ :=
    redHead_ok s k p ap np fp (g (p + 7)) n0 R g (by omega) ar hrsp hrdi hrdx hrbx hrax hM.fw
  set gh := Function.update g 4 R with hghd
  have hMh : Mems s.vg.mem sh.vg.mem k np fp n gh := by
    rw [hmem]; exact hM.write hnp hfp sepN (by omega) _
  have arh := ar.frame hF
  have hsph : sh.vg.gpr .rsp = fp := (hF.gpr .rsp (by simp)).trans hrsp
  have hbph : sh.vg.gpr .rbp = np := (hF.gpr .rbp (by simp)).trans hrbp
  have hgh : ∀ i, i ≠ 4 → gh i = g i := fun i hi => by rw [hghd, Function.update_of_ne hi]
  have hI0 : RedInv sh sh k np fp n0 n gh 0 :=
    ⟨Frame.refl _ _, by rw [hcx]; rfl, by rw [hdx, h8, mulLo_eq], hcf, hof, gh, hMh.refl, fun _ _ => rfl,
      by simp [val, gsum]⟩
  obtain ⟨sr, xr, hIr⟩ := redLoop_ok sh k ap np fp n0 n gh hk arh hsph hbph hsi
    (by rw [hgh 5 (by omega), hg5]) hn0 hI0
  obtain ⟨hFr, -, -, -, -, gr, hMr, hgr, hvr⟩ := hIr
  have arr := arh.frame hFr
  have hspr : sr.vg.gpr .rsp = fp := (hFr.gpr .rsp (by simp)).trans hsph
  have hsir : sr.vg.gpr .rsi = 0 := (hFr.gpr .rsi (by simp)).trans hsi
  obtain ⟨se, xe, eax, ecf, emem, eF⟩ := redEnd_ok sr k ap np fp gr arr hspr hsir hMr.fw
  have hgr_g : ∀ i, i ≠ 4 → (i < 7 ∨ 15 ≤ i) → gr i = g i := fun i h4 hi => by
    rw [hgr i (by omega), hgh i h4]
  refine ⟨sh, sr, se, Exec.block xh, xr, Exec.block xe, (hF.toRL.trans hFr.toRL).trans eF.toRL, ?_, ?_, eax, ?_,
    gr, ?_, hgr_g, ?_, ?_⟩
  · rw [eF.gpr .rdi (by simp), hFr.gpr .rdi (by simp), hdi]
  · rw [eF.gpr .rbp (by simp), hFr.gpr .rbp (by simp), hbph]
  · rw [ecf, hFr.gpr .rbp (by simp), hbph, hgr_g 1 (by omega) (by omega), hg1]
    have := cmp_np (a := 0) (b := k - 8) hnp (by omega) (by omega)
    rw [wa_zero] at this
    rw [this]; congr 1; exact decide_eq_decide.mpr (by omega)
  · rw [emem]; exact hMh.trans hMr
  · rw [hgr 4 (by omega), hghd, Function.update_self]
  · have hre : regs se = regs sr := by
      simp only [regs, eF.gpr .r8 (by simp), eF.gpr .r9 (by simp), eF.gpr .r10 (by simp), eF.gpr .r11 (by simp),
        eF.gpr .r12 (by simp), eF.gpr .r13 (by simp), eF.gpr .r14 (by simp), eF.gpr .r15 (by simp)]
    have hrh : regs sh = val (fun i => g (p + 7 + i)) 8 := by
      rw [← hsum8_val g (p + 7)]
      simp only [regs, h8, h9, h10, h11, h12, h13, h14, h15]
    have hn8 : hsum [n 0, n 1, n 2, n 3, n 4, n 5, n 6, n 7] = val n 8 := by
      rw [show hsum [n 0, n 1, n 2, n 3, n 4, n 5, n 6, n 7] = hsum [n 0, n (0 + 1), n (0 + 2), n (0 + 3),
        n (0 + 4), n (0 + 5), n (0 + 6), n (0 + 7)] from rfl, hsum8_val n 0]
      exact val_eq fun i _ => congrArg n (by omega)
    rw [hrh, hn8] at hvr
    norm_num only at hvr
    rw [hre, hvr]

/-! ## A round -/

/-- A round's trace, at the window `t`'s word `p`. -/
def roundTrace (np fp : Addr) (k p : Nat) : List Leak :=
  [] ++ (redHeadTrace fp p ++ (redLoopTrace np fp ++ (redEndTrace fp ++
    ((if k = 8 then [.branch true] else .branch false :: tailSegTrace np fp k p) ++
      noTailTrace np fp k (p + k + 7)))))

/-- The reduction's trace: `k / 8` rounds. -/
def redTrace (k : Nat) (np fp : Addr) : List Leak := loopTrace (roundTrace np fp k) 8 0 (k / 8 - 1)

/-- The reduction before the round at the window `t`'s word `p`, from `s₀`: `rdi` at the window, `rbp` at `n`,
`rbx` `n0`, `rdx` the window's first word, slots 1, 2, and 5 as the reduction found them, and `2^(64p)` times
`t` from the window and `rax` at `t`'s word `p + k` as much as `A` plus a multiple `Q < 2^(64p)` of `n`. -/
structure OInv (s₀ s : S) (k : Nat) (np fp n0 : Addr) (n : Nat → BitVec 64) (A p : Nat) : Prop where
  frame : Frame s₀ s RL
  rdi : s.vg.gpr .rdi = wa fp (p + 7)
  rbp : s.vg.gpr .rbp = np
  rbx : s.vg.gpr .rbx = n0
  rax0 : p = 0 → s.vg.gpr .rax = 0
  late : 0 < p → s.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8 * k) ∧ s.vg.gpr .r8 = wa fp (p + k + 7)
  mem : ∃ g, Mems s₀.vg.mem s.vg.mem k np fp n g ∧ g 1 = wa np (k - 8) ∧ g 2 = wa fp (2 * k + 7) ∧ g 5 = n0 ∧
    (p + 8 ≤ k → s.vg.gpr .rdx = g (p + 7)) ∧
    ∃ Q, Q < 2 ^ (64 * p) ∧
      2 ^ (64 * p) * (val (fun i => g (p + 7 + i)) (2 * k - p) + 2 ^ (64 * k) * (s.vg.gpr .rax).toNat) =
        A + Q * val n k

set_option exponentiation.threshold 1024 in
theorem round_arith (V2 A2v A2c rax2 regs2 G8 cc V1 regsE Q8 Nn R W regsH N8 : Nat)
    (eNT : A2v + 2 ^ 512 * A2c = regs2 + G8 + cc)
    (ePN : V2 + W * (regs2 + 2 ^ 512 * rax2 + cc) = V1 + regsE + Q8 * Nn + W * R)
    (eRL : 2 ^ 512 * regsE = regsH + Q8 * N8) :
    2 ^ 512 * ((V2 + W * A2v) + W * 2 ^ 512 * (rax2 + A2c)) =
      (regsH + 2 ^ 512 * (V1 + W * G8)) + Q8 * (N8 + 2 ^ 512 * Nn) + W * 2 ^ 512 * R := by
  zify at eNT ePN eRL ⊢
  linear_combination (2 ^ 512 * W : ℤ) * eNT + (2 ^ 512 : ℤ) * ePN + eRL

set_option exponentiation.threshold 1024 in
theorem oinv_arith (P Vk rax T Wk X R Q Q8 N A : Nat)
    (eR : 2 ^ 512 * (Vk + Wk * rax) = X + Q8 * N + Wk * R)
    (eP : P * (X + Wk * 2 ^ 512 * T + Wk * R) = A + Q * N) :
    P * 2 ^ 512 * ((Vk + Wk * T) + Wk * rax) = A + (Q + P * Q8) * N := by
  zify at eR eP ⊢
  linear_combination (P : ℤ) * eR + eP

theorem q_lt (P Q Q8 : Nat) (hQ : Q < P) (hQ8 : Q8 < 2 ^ 512) : Q + P * Q8 < P * 2 ^ 512 := by
  have h := Nat.mul_le_mul_left P (show Q8 + 1 ≤ 2 ^ 512 by omega)
  rw [Nat.mul_add, Nat.mul_one] at h
  generalize P * Q8 = x at h ⊢
  generalize P * 2 ^ 512 = y at h ⊢
  omega

theorem val_split' (f : Nat → BitVec 64) (a b : Nat) (h : a ≤ b) :
    val f b = val f a + 2 ^ (64 * a) * val (fun i => f (a + i)) (b - a) := by
  have := val_split f a (b - a); rwa [Nat.add_sub_cancel' h] at this

/-- `noTail`'s step back to the next window, `rdi` at the frame's word `e`. -/
theorem nt_addr (fp X : Addr) (k e : Nat) (hk : 8 ≤ k) (hke : k ≤ e) (_he : e + 8 ≤ 2 * k + 9)
    (_hfp : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 64) (hk' : k < 2 ^ 29) (hX : X.toNat = 2 ^ 64 - 8 * k) :
    wa fp e + X * 1#64 + 8#64 * 8#64 = wa fp (e + 8 - k) := by
  simp only [Nat.reducePow] at _hfp hk' hX
  apply BitVec.eq_of_toNat_eq
  simp only [wa, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hX, Nat.reducePow, Nat.reduceMod,
    Nat.mul_one, Nat.reduceMul]
  omega

set_option exponentiation.threshold 1024 in
set_option maxHeartbeats 4000000 in
/-- A round keeps `OInv`, from the window at `t`'s word `p` to the next. -/
theorem oinv_step (s₀ s : S) (k p : Nat) (ap np fp n0 : Addr) (n : Nat → BitVec 64) (A : Nat)
    (hk : 8 ≤ k) (hk8 : k % 8 = 0) (hp : p + 8 ≤ k) (ar₀ : Arr s₀ k ap np fp) (hrsp : s₀.vg.gpr .rsp = fp)
    (hx2 : xlo s₀ .xmm2 = np) (hx3 : xlo s₀ .xmm3 = BitVec.ofNat 64 (2 ^ 64 - 8 * k))
    (hn0 : ((n 0).toNat * n0.toNat + 1) % 2 ^ 64 = 0) (hI : OInv s₀ s k np fp n0 n A p) :
    ∃ s', Exec I Rind.X86_64.Sqrx8x.redPass s (roundTrace np fp k p) s' ∧
      I.eval (.vg .b) s' = some (decide (p + 8 < k)) ∧ OInv s₀ s' k np fp n0 n A (p + 8) := by
  have hb := ar₀
  obtain ⟨hk', hap, hnp, hfp, sepA, sepN, -, -, -, -, -⟩ := hb
  obtain ⟨hF, hdi, hbp, hbx, hax0, -, g, hM, hg1, hg2, hg5, hdx, Q, hQ, hv⟩ := hI
  have ar := ar₀.frame hF
  have hsp : s.vg.gpr .rsp = fp := (hF.gpr .rsp (by simp)).trans hrsp
  obtain ⟨sh, sr, se, xh, xr, xe, hFe, edi, ebp, eax, ecf, ge, hMe, hge, hge4, hve⟩ :=
    roundA_ok s k p ap np fp n0 (s.vg.gpr .rax) n g hk hp ar hsp hdi hbp hbx (hdx hp) rfl hM.refl hg1 hg5 hn0
  have are := ar.frame hFe
  have hspe : se.vg.gpr .rsp = fp := (hFe.gpr .rsp (by simp)).trans hsp
  have hge1 : ge 1 = wa np (k - 8) := by rw [hge 1 (by omega) (by omega), hg1]
  -- the tail, if `n` has more than eight words
  have hT : ∃ s₂ cc, Exec I (.ite (.vg .ae) (.block []) tailSeg) se
      (if k = 8 then [.branch true] else .branch false :: tailSegTrace np fp k p) s₂ ∧
      PreNT se s₂ k p np fp n ge cc := by
    by_cases h8 : k = 8
    · subst h8
      refine ⟨se, false, ?_, Frame.refl _ _, by rw [edi], by rw [ebp]; simp [wa], by rw [eax]; simp,
        by rw [ecf]; rfl, ge, hMe.refl, fun _ _ _ => rfl, ?_⟩
      · simp only [↓reduceIte]
        exact Exec.iteT (by simp [Rind.X86_64.isa, Rind.X86_64.eval, VG.X86_64.eval, ecf])
          (Exec.block (is := []) (s := se) (s' := se) (t := []) rfl)
      · rw [eax, hge4, hax0 (by omega)]; simp [val, gsum]
    · simp only [h8, ↓reduceIte]
      obtain ⟨s₂, cc, x2, hP⟩ := tailSeg_ok se k p ap np fp n ge (by omega) hk8 hp are hspe edi ebp eax hMe.refl
        hge1
      exact ⟨s₂, cc, Exec.iteF (by simp [Rind.X86_64.isa, Rind.X86_64.eval, VG.X86_64.eval, ecf]; omega) x2, hP⟩
  obtain ⟨s₂, cc, xT, hF2, di2, bp2, ax2, cf2, g₂, hM2, hg₂, hv2⟩ := hT
  have ar2 := are.frame hF2
  have hsp2 : s₂.vg.gpr .rsp = fp := (hF2.gpr .rsp (by simp)).trans hspe
  have hxmm : s₂.vg.xmm = s₀.vg.xmm := ((hF.trans hFe).trans hF2).xmm
  have hx2' : (s₂.vg.xmm .xmm2).setWidth 64 = np := by rw [hxmm]; exact hx2
  have hx3' : (s₂.vg.xmm .xmm3).setWidth 64 = BitVec.ofNat 64 (2 ^ 64 - 8 * k) := by rw [hxmm]; exact hx3
  have hrd : wa fp (p + k + 7) + (s₂.vg.xmm .xmm3).setWidth 64 * 1#64 + 8#64 * 8#64 = wa fp (p + k + 7 + 8 - k) := by
    have hX : ((s₂.vg.xmm .xmm3).setWidth 64).toNat = 2 ^ 64 - 8 * k := by
      rw [hx3', BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    exact nt_addr fp _ k (p + k + 7) (by omega) (by omega) (by omega) hfp hk' hX
  obtain ⟨s', xN, nmem, nax, ncx, nbp, nbx, ndx, n8, ndi, ncf, nF⟩ :=
    noTail_ok s₂ k (p + k + 7) ap np fp (s₂.vg.gpr .rax) n g₂ cc hk (by omega) (by omega) ar2 hsp2 di2 bp2 rfl cf2
      hx2' hrd hM2.nw hM2.fw
  set A2 := add8 (s₂.vg.gpr .r8) (s₂.vg.gpr .r9) (s₂.vg.gpr .r10) (s₂.vg.gpr .r11) (s₂.vg.gpr .r12)
    (s₂.vg.gpr .r13) (s₂.vg.gpr .r14) (s₂.vg.gpr .r15) (g₂ (p + k + 7)) (g₂ (p + k + 7 + 1)) (g₂ (p + k + 7 + 2))
    (g₂ (p + k + 7 + 3)) (g₂ (p + k + 7 + 4)) (g₂ (p + k + 7 + 5)) (g₂ (p + k + 7 + 6)) (g₂ (p + k + 7 + 7)) cc
    with hA2
  have hM' : Mems s₀.vg.mem s'.vg.mem k np fp n (upd8 g₂ (p + k + 7) A2) := by
    rw [nmem]; exact ((hM.trans hMe).trans hM2).store8 hnp hfp sepN (by omega) (by omega) A2
  -- the frame's words the round leaves alone
  have hgg : ∀ i, i ≠ 3 → i ≠ 4 → (i < 7 ∨ p + k + 15 ≤ i) → upd8 g₂ (p + k + 7) A2 i = g i := by
    intro i h3 h4 hi
    rw [upd8_out _ _ _ (by omega), hg₂ i h3 (by omega), hge i h4 (by omega)]
  have hg₂e : ∀ i, p + k + 7 ≤ i → g₂ i = g i := fun i hi => by
    rw [hg₂ i (by omega) (by omega), hge i (by omega) (by omega)]
  refine ⟨s', Exec.seq (Exec.block (M := I) (is := [Rind.X86_64.Instr.align 32]) (s := s) (s' := s) (t := []) rfl)
    (Exec.seq xh (Exec.seq xr (Exec.seq xe (Exec.seq xT (Exec.block xN))))), ?_,
    ((hF.trans hFe).trans hF2).trans nF.toRL, ?_, nbp, ?_, fun h => absurd h (by omega), fun _ => ⟨?_, ?_⟩,
    upd8 g₂ (p + k + 7) A2, hM', ?_, ?_, ?_, ?_, Q + 2 ^ (64 * p) * val (fun i => ge (7 + i)) 8, ?_, ?_⟩
  · simp only [Rind.X86_64.isa, Rind.X86_64.eval, VG.X86_64.eval, ncf]
    rw [hg₂ 2 (by omega) (by omega), hge 2 (by omega) (by omega), hg2, wa_toNat hfp (by omega),
      wa_toNat hfp (by omega)]
    congr 1; exact decide_eq_decide.mpr (by omega)
  · rw [ndi, show p + k + 7 + 8 - k = p + 8 + 7 by omega]
  · rw [nbx, hg₂ 5 (by omega) (by omega), hge 5 (by omega) (by omega), hg5]
  · rw [ncx, hx3']
  · rw [n8, show p + k + 7 + 8 = p + 8 + k + 7 by omega]
  · rw [hgg 1 (by omega) (by omega) (by omega), hg1]
  · rw [hgg 2 (by omega) (by omega) (by omega), hg2]
  · rw [hgg 5 (by omega) (by omega) (by omega), hg5]
  · intro h16
    rw [ndx, upd8_out _ _ _ (by omega)]; exact congrArg g₂ (by omega)
  · rw [show 64 * (p + 8) = 64 * p + 512 by ring, pow_add]
    have hQ8 := val_lt (fun i => ge (7 + i)) 8
    simp only [Nat.reduceMul] at hQ8
    exact q_lt _ _ _ hQ hQ8
  · -- the sums
    have hNT := add8_acct (s₂.vg.gpr .r8) (s₂.vg.gpr .r9) (s₂.vg.gpr .r10) (s₂.vg.gpr .r11) (s₂.vg.gpr .r12)
      (s₂.vg.gpr .r13) (s₂.vg.gpr .r14) (s₂.vg.gpr .r15) (g₂ (p + k + 7)) (g₂ (p + k + 7 + 1))
      (g₂ (p + k + 7 + 2)) (g₂ (p + k + 7 + 3)) (g₂ (p + k + 7 + 4)) (g₂ (p + k + 7 + 5)) (g₂ (p + k + 7 + 6))
      (g₂ (p + k + 7 + 7)) cc
    dsimp only at hNT
    rw [← hA2, hsum8_val g₂ (p + k + 7)] at hNT
    have hG8 : val (fun i => g₂ (p + k + 7 + i)) 8 = val (fun i => g (p + 15 + (k - 8) + i)) 8 :=
      val_eq fun i _ => by rw [hg₂e _ (by omega)]; exact congrArg g (by omega)
    have hV1 : val (fun i => ge (p + 15 + i)) (k - 8) = val (fun i => g (p + 15 + i)) (k - 8) :=
      val_eq fun i _ => hge _ (by omega) (by omega)
    have hre : regs se = regs se := rfl
    have hrax' : (s'.vg.gpr .rax).toNat = (s₂.vg.gpr .rax).toNat + A2.c.toNat := by
      rw [nax]; exact adcS0_toNat _ _ ax2
    rw [hge4, hV1] at hv2
    rw [hG8] at hNT
    -- the round's sum, `2^512` times `t` from the next window and `rax`
    have hW : 2 ^ (64 * k) = 2 ^ (64 * (k - 8)) * 2 ^ 512 := by
      rw [← pow_add, show 64 * (k - 8) + 512 = 64 * k by omega]
    have hVk : val (fun i => upd8 g₂ (p + k + 7) A2 (p + 15 + i)) k =
        val (fun i => g₂ (p + 15 + i)) (k - 8) + 2 ^ (64 * (k - 8)) * A2.val := by
      have e1 : val (fun i => upd8 g₂ (p + k + 7) A2 (p + 15 + i)) (k - 8) =
          val (fun i => g₂ (p + 15 + i)) (k - 8) := val_eq fun i _ => upd8_out _ _ _ (by omega)
      have e2 : val (fun i => upd8 g₂ (p + k + 7) A2 (p + 15 + (k - 8 + i))) (k - (k - 8)) = A2.val := by
        rw [Nat.sub_sub_self hk, ← upd8_val g₂ (p + k + 7) A2]
        exact val_eq fun i _ => congrArg _ (by omega)
      rw [val_split' _ (k - 8) k (by omega)]
      rw [e1, e2]
    have hX : val (fun i => g (p + 7 + i)) (k + 8) = val (fun i => g (p + 7 + i)) 8 +
        2 ^ 512 * (val (fun i => g (p + 15 + i)) (k - 8) +
          2 ^ (64 * (k - 8)) * val (fun i => g (p + 15 + (k - 8) + i)) 8) := by
      have f1 : val (fun i => g (p + 7 + (8 + i))) (k + 8 - 8) = val (fun i => g (p + 15 + i)) k := by
        rw [show k + 8 - 8 = k by omega]; exact val_eq fun i _ => congrArg g (by omega)
      have f3 : val (fun i => g (p + 15 + (k - 8 + i))) (k - (k - 8)) =
          val (fun i => g (p + 15 + (k - 8) + i)) 8 := by
        rw [Nat.sub_sub_self hk]; exact val_eq fun i _ => congrArg g (by omega)
      have f2 : val (fun i => g (p + 15 + i)) k = val (fun i => g (p + 15 + i)) (k - 8) +
          2 ^ (64 * (k - 8)) * val (fun i => g (p + 15 + (k - 8) + i)) 8 := by
        rw [val_split' _ (k - 8) k (by omega)]
        rw [f3]
      rw [val_split' _ 8 (k + 8) (by omega)]
      rw [f1, f2]
    have hN : val n k = val n 8 + 2 ^ 512 * val (fun i => n (8 + i)) (k - 8) := by
      rw [val_split' n 8 k (by omega)]
    have eR : 2 ^ 512 * (val (fun i => upd8 g₂ (p + k + 7) A2 (p + 15 + i)) k +
        2 ^ (64 * k) * (s'.vg.gpr .rax).toNat) =
        val (fun i => g (p + 7 + i)) (k + 8) + val (fun i => ge (7 + i)) 8 * val n k +
          2 ^ (64 * k) * (s.vg.gpr .rax).toNat := by
      rw [hVk, hrax', hX, hN, hW]
      exact round_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNT hv2 hve
    -- the rest of `t`, which the round leaves alone
    have hT1 : val (fun i => upd8 g₂ (p + k + 7) A2 (p + 8 + 7 + i)) (2 * k - (p + 8)) =
        val (fun i => upd8 g₂ (p + k + 7) A2 (p + 15 + i)) k +
          2 ^ (64 * k) * val (fun i => g (p + 7 + (k + 8 + i))) (k - p - 8) := by
      have h1 : val (fun i => upd8 g₂ (p + k + 7) A2 (p + 8 + 7 + i)) k =
          val (fun i => upd8 g₂ (p + k + 7) A2 (p + 15 + i)) k :=
        val_eq fun i _ => congrArg _ (by omega)
      have h2 : val (fun i => upd8 g₂ (p + k + 7) A2 (p + 8 + 7 + (k + i))) (2 * k - (p + 8) - k) =
          val (fun i => g (p + 7 + (k + 8 + i))) (k - p - 8) := by
        rw [show 2 * k - (p + 8) - k = k - p - 8 by omega]
        exact val_eq fun i _ => by
          rw [upd8_out _ _ _ (by omega), hg₂e _ (by omega)]; exact congrArg g (by omega)
      rw [val_split' _ k (2 * k - (p + 8)) (by omega)]
      rw [h1, h2]
    have hT0 : val (fun i => g (p + 7 + i)) (2 * k - p) = val (fun i => g (p + 7 + i)) (k + 8) +
        2 ^ (64 * k) * 2 ^ 512 * val (fun i => g (p + 7 + (k + 8 + i))) (k - p - 8) := by
      rw [val_split' _ (k + 8) (2 * k - p) (by omega), show 2 * k - p - (k + 8) = k - p - 8 by omega,
        show 64 * (k + 8) = 64 * k + 512 by ring, pow_add]
    rw [hT0] at hv
    rw [hT1, show 64 * (p + 8) = 64 * p + 512 by ring, pow_add]
    exact oinv_arith _ _ _ _ _ _ _ _ _ _ _ eR hv

/-! ## The reduction -/

/-- `bn_sqrx8x_internal`'s reduction: from `RedPre`, `redPass`'s loop leaves `RedPost`, and its trace is a
function of `k`, `np`, and `fp` alone. -/
theorem red_ok (s : S) (k : Nat) (ap np fp : Addr) (a n : Nat → BitVec 64) (n0 : BitVec 64) (A : Nat)
    (h : RedPre s k ap np fp a n n0 A) :
    ∃ s', Exec I (.loop Rind.X86_64.Sqrx8x.redPass (.vg .b)) s (redTrace k np fp) s' ∧
      RedPost s s' k np fp n A := by
  have ctx := h.ctx
  have hk := ctx.k8
  have hk8 := ctx.k0
  have hb := ctx.ar
  obtain ⟨hk', hap, hnp, hfp, sepA, sepN, -, -, -, -, -⟩ := hb
  set g₀ : Nat → BitVec 64 := fun i => s.vg.mem.readW (wa fp i) 64 with hg₀
  have hI0 : OInv s s k np fp n0 n A 0 := by
    refine ⟨Frame.refl _ _, by simpa using h.rdi, h.rbp, h.rbx, fun _ => h.rax, fun h0 => absurd h0 (by omega),
      g₀, ⟨fun _ _ => rfl, ctx.hN, Keeps.refl _ _ _⟩, h.s1, h.s2, ctx.s5, fun _ => h.rdx, 0, by simp, ?_⟩
    rw [h.rax, ← h.val]
    simp only [Nat.mul_zero, BitVec.toNat_zero, Nat.add_zero, pow_zero, Nat.one_mul, Nat.zero_mul, Nat.sub_zero]
    exact val_eq fun i _ => by simp only [hg₀, tw]; exact congrArg (fun j => s.vg.mem.readW (wa fp j) 64) (by omega)
  obtain ⟨s', hx, hI⟩ := loop_ok (body := Rind.X86_64.Sqrx8x.redPass) (c := .vg .b)
    (fun p s' => OInv s s' k np fp n0 n A p) (fun p => p + 8 ≤ k) (fun p => decide (p + 8 < k))
    (roundTrace np fp k) 8
    (fun p s' hI hp => oinv_step s s' k p ap np fp n0 n A hk hk8 hp ctx.ar h.rsp ctx.x2 ctx.x3 ctx.n0 hI)
    (k / 8 - 1) 0 s hI0 (fun i hi => by omega) (fun i hi => by simp; omega) (by simp; omega)
  rw [show 0 + 8 * (k / 8 - 1 + 1) = k by omega] at hI
  obtain ⟨hF, -, hbp, -, -, hlate, g, hM, -, -, -, -, Q, hQ, hv⟩ := hI
  obtain ⟨hcx, h8⟩ := hlate (by omega)
  rw [show 2 * k - k = k by omega] at hv
  have hV : val (fun i => tw s'.vg.mem fp (k + i)) k = val (fun i => g (k + 7 + i)) k :=
    val_eq fun i _ => by rw [tw, show k + i + 7 = k + 7 + i by omega]; exact hM.fw _ (by omega)
  refine ⟨s', hx, ⟨Q, hQ, ?_⟩, ?_, hcx, by rw [h8, show k + k + 7 = 2 * k + 7 by omega], hbp, hM.keeps, hF⟩
  · rw [hV]; rw [← hv]; ring
  · -- `rax` is a bit, as `A + Q·n < 2·2^(128k)`
    have hA : A < 2 ^ (64 * k) * 2 ^ (64 * k) := by
      rw [← h.val, ← pow_add, show 64 * k + 64 * k = 64 * (2 * k) by ring]; exact val_lt _ _
    have hN := val_lt n k
    have hQN : Q * val n k ≤ 2 ^ (64 * k) * 2 ^ (64 * k) :=
      Nat.mul_le_mul (Nat.le_of_lt hQ) (Nat.le_of_lt hN)
    by_contra hr
    have hr2 : 2 ≤ (s'.vg.gpr .rax).toNat := by omega
    have h1 : 2 ^ (64 * k) * (2 ^ (64 * k) * 2) ≤
        2 ^ (64 * k) * (val (fun i => g (k + 7 + i)) k + 2 ^ (64 * k) * (s'.vg.gpr .rax).toNat) :=
      Nat.mul_le_mul_left _ (le_trans (Nat.mul_le_mul_left _ hr2) (Nat.le_add_left _ _))
    rw [hv, show 2 ^ (64 * k) * (2 ^ (64 * k) * 2) = 2 * (2 ^ (64 * k) * 2 ^ (64 * k)) by ring] at h1
    generalize 2 ^ (64 * k) * 2 ^ (64 * k) = Z at h1 hA hQN
    generalize Q * val n k = P at h1 hQN
    omega

end rind.x86_64.sqrx8x
