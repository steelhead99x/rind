import Rind.X86_64.Sqrx8xPass

/-! # bn_sqrx8x_internal's triangle phase

Row block `R`'s triangle, then the passes: each adds the row block times every column block past it into `t`
and runs the next row block's triangle. Two invariants carry the phase: `PB R`, before row block `R`'s triangle,
whose words `16R + 1` to `16R + 7` are in `r9` to `r15` rather than in `t`, and `OA R`, after it, whose words
`16R + 9` to `16R + 14` and carry are in `r9` to `r14` and `rcx` on top of `t`'s. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.sqrx8x

/-- `r9` to `r15`. -/
abbrev regs7 (s : S) : List (BitVec 64) :=
  [s.vg.gpr .r9, s.vg.gpr .r10, s.vg.gpr .r11, s.vg.gpr .r12, s.vg.gpr .r13, s.vg.gpr .r14, s.vg.gpr .r15]

/-- `r9` to `r14`. -/
abbrev regs6 (s : S) : List (BitVec 64) :=
  [s.vg.gpr .r9, s.vg.gpr .r10, s.vg.gpr .r11, s.vg.gpr .r12, s.vg.gpr .r13, s.vg.gpr .r14]

theorem hsum_twl_succ (M : Mem) (fp : Addr) (q n : Nat) :
    hsum (twl M fp q (n + 1)) = hsum (twl M fp q n) + 2 ^ (64 * n) * (tw M fp (q + n)).toNat := by
  induction n generalizing q with
  | zero => simp [twl, hsum]
  | succ n ih =>
    rw [twl, hsum, ih (q + 1), twl, hsum, show q + 1 + n = q + (n + 1) by omega,
      show 64 * (n + 1) = 64 + 64 * n by ring, pow_add]
    ring

theorem hsum_twl_zero (M : Mem) (fp : Addr) (q n : Nat) (h : ∀ i < n, tw M fp (q + i) = 0) :
    hsum (twl M fp q n) = 0 := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [twl, hsum, ih (q + 1) (fun i hi => by rw [Nat.add_assoc]; exact h (1 + i) (by omega))]
    have := h 0 (by omega)
    simp only [Nat.add_zero] at this
    simp [this]

/-- Two frame words are the same exactly when their indices are. -/
theorem wa_beq2 (p : Addr) (i j n : Nat) (hi : i ≤ n) (hj : j ≤ n) (hn : n < 2 ^ 31)
    (hp : p.toNat + 8 * n ≤ 2 ^ 64) : (wa p i - wa p j == 0) = decide (i = j) := by
  by_cases h : i = j
  · subst h; simp
  · have : (wa p i - wa p j == 0) = false := by
      rw [beq_eq_false_iff_ne]; simp only [wa]; bv_omega
    rw [this]; simp [h]

/-- Before row block `R`'s triangle: `t` with its words `16R + 1` to `16R + 7` taken from `r9` to `r15` is `Q R`,
and nothing is stored from word `8R + k` on. -/
structure PB (s₀ s : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (R : Nat) : Prop where
  frame : Frame s₀ s allRegs
  mem : MemOK s₀.vg.mem s.vg.mem k ap fp a
  hR : 8 * R + 8 ≤ k
  rsi : s.vg.gpr .rsi = wa ap (8 * R)
  rdi : s.vg.gpr .rdi = wa fp (16 * R + 7)
  rbp : s.vg.gpr .rbp = 0
  rdx : s.vg.gpr .rdx = a (8 * R)
  cf : s.vg.cf = some false
  of : s.vg.of = some false
  zero : ∀ q, 8 * R + k ≤ q → q < 2 * k + 2 → tw s.vg.mem fp q = 0
  sum : (val (tw s.vg.mem fp) (2 * k + 2) : ℤ) +
      2 ^ (64 * (16 * R + 1)) * ((hsum (regs7 s) : ℤ) - hsum (twl s.vg.mem fp (16 * R + 1) 7)) = Q a k R

/-- After row block `R`'s triangle: `t`, with `r9` to `r14` and the carry `rcx`'s mask holds from its word
`16R + 9`, is `Q R` and the row block's triangle; `zf` is whether it was the last. -/
structure OA (s₀ s : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (R : Nat) : Prop where
  frame : Frame s₀ s allRegs
  mem : MemOK s₀.vg.mem s.vg.mem k ap fp a
  hR : 8 * R + 8 ≤ k
  rsi : s.vg.gpr .rsi = wa ap (8 * R + 8)
  rdi : s.vg.gpr .rdi = wa fp (16 * R + 7)
  rbp : s.vg.gpr .rbp = 0
  zf : s.vg.zf = some (decide (8 * R + 8 = k))
  zero : ∀ q, 8 * R + k ≤ q → 16 * R + 9 ≤ q → q < 2 * k + 2 → tw s.vg.mem fp q = 0
  sum : ∃ mc : Bool, s.vg.gpr .rcx = 0 - (BitVec.ofBool mc).setWidth 64 ∧ (8 * R + 8 = k → mc = false) ∧
    val (tw s.vg.mem fp) (2 * k + 2) + (hsum (regs6 s) + mc.toNat) * 2 ^ (64 * (16 * R + 9)) =
      Q a k R + diag8 (fun i => a (8 * R + i)) * 2 ^ (64 * (16 * R))

set_option exponentiation.threshold 4096 in
set_option maxHeartbeats 4000000 in
/-- Row block `R`'s triangle. -/
theorem tri_step (s₀ : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (ar : Arr s₀ k ap np fp)
    (hrsp : s₀.vg.gpr .rsp = fp) (R : Nat) (s : S) (hP : PB s₀ s k ap np fp a R) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.tri s = some (s', triTrace ap fp R) ∧ OA s₀ s' k ap np fp a R := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := id ar
  have hF := hP.frame
  have arS := ar.frame hF
  have rsp := (hF.gpr .rsp (by decide)).trans hrsp
  have hR := hP.hR
  have e1 : (2 : ℤ) ^ (64 * (16 * R + 1)) = 2 ^ (64 * (16 * R)) * 2 ^ 64 := by rw [← pow_add]; ring_nf
  have e9 : (2 : ℤ) ^ (64 * (16 * R + 9)) = 2 ^ (64 * (16 * R)) * 2 ^ 576 := by rw [← pow_add]; ring_nf
  obtain ⟨s1, x1, w0, w1, w2, w3, w4, w5, w6, w7, mc, m1, si1, zf1, cx1, hmc, bp1, e, F1⟩ :=
    tri_ok s k R ap np fp (fun i => a (8 * R + i)) (s.vg.mem.readW (wa fp (16 * R + 15)) 64) (by omega) arS
      hP.rsi hP.rdi rsp (fun i hi => hP.mem.hA _ (by omega)) hP.rbp (by simp only [hP.rdx, Nat.add_zero]) hP.cf hP.of rfl
  have mw : s1.vg.mem = wrs s.vg.mem fp (16 * R + 1) [w0, w1, w2, w3, w4, w5, w6, w7] := by
    rw [m1]; simp only [wrs, Nat.add_assoc, Nat.reduceAdd]
  have mem1 : MemOK s₀.vg.mem s1.vg.mem k ap fp a := by
    rw [mw]; exact hP.mem.wrs hk hap hfp sepA _ _ (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨s1, x1, hF.trans (F1.mono (by decide)), mem1, hR, si1, ?_, bp1, ?_, ?_, ⟨mc, cx1, ?_, ?_⟩⟩
  · rw [F1.gpr .rdi (by decide)]; exact hP.rdi
  · rw [zf1, hP.mem.s2, wa_beq _ _ _ hR hk hap]
  · intro q h1 h2 h3
    have := hP.zero q h1 h3
    show s1.vg.mem.readW _ 64 = 0
    rw [mw]; rd_simp; exact this
  · intro hl; apply hmc
    have := hP.zero (16 * R + 8) (by omega) (by omega)
    simpa only [tw, Nat.add_assoc, Nat.reduceAdd] using this
  · have W1 := val_wrs s.vg.mem fp (16 * R + 1) (2 * k + 2) [w0, w1, w2, w3, w4, w5, w6, w7]
      (by simp only [List.length_cons, List.length_nil]; omega) (by omega)
    rw [← mw, show [w0, w1, w2, w3, w4, w5, w6, w7].length = 7 + 1 from rfl, hsum_twl_succ] at W1
    have hu : tw s.vg.mem fp (16 * R + 1 + 7) = s.vg.mem.readW (wa fp (16 * R + 15)) 64 := by
      simp only [tw, Nat.add_assoc, Nat.reduceAdd]
    rw [hu] at W1
    have hS := hP.sum
    simp only [hsum] at W1 hS ⊢
    zify at e ⊢
    push_cast at W1 hS e ⊢
    rw [e1] at W1 hS
    rw [e9]
    generalize (2 : ℤ) ^ (64 * (16 * R)) = P at *
    linear_combination W1 + hS + P * e

set_option exponentiation.threshold 4096 in
set_option maxHeartbeats 4000000 in
/-- Row block `R`'s first column block, `R + 1`: `pre`, the inner loop, and `innerEnd`. -/
theorem first_col (s₀ : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (ar : Arr s₀ k ap np fp)
    (hrsp : s₀.vg.gpr .rsp = fp) (R : Nat) (s : S) (hO : OA s₀ s k ap np fp a R) (hR : 8 * R + 16 ≤ k) :
    ∃ s1 s2 s3, execBlock I Rind.X86_64.Sqrx8x.pre s = some (s1, preTrace ap fp R) ∧
      Exec I (.loop (.block Rind.X86_64.Sqrx8x.inner) (Rind.X86_64.Cond.vg .ne)) s1
        (innerLoopTrace ap fp R (R + 1)) s2 ∧
      execBlock I Rind.X86_64.Sqrx8x.innerEnd s2 = some (s3, innerEndTrace fp) ∧
      CInv s₀ s3 k ap np fp a R (R + 2) := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := id ar
  have hF := hO.frame
  have arS := ar.frame hF
  have rsp := (hF.gpr .rsp (by decide)).trans hrsp
  have eP : (2 : ℤ) ^ (64 * (8 * R + 8 * (R + 2))) = 2 ^ (64 * (16 * R + 8)) * 2 ^ 512 := by
    rw [← pow_add]; ring_nf
  have e9 : (2 : ℤ) ^ (64 * (16 * R + 9)) = 2 ^ (64 * (16 * R + 8)) * 2 ^ 64 := by rw [← pow_add]; ring_nf
  have e8 : 8 * (R + 2 - R - 1) = 8 := by omega
  have eR : 8 * (R + 1) = 8 * R + 8 := by ring
  obtain ⟨mc, hcx, -, hS⟩ := hO.sum
  -- pre
  obtain ⟨s1, x1, c, m1, cx1, bp1, di1, dx1, -, r81, cf1, of1, e1, F1⟩ :=
    pre_ok s k R ap np fp a (fun p => s.vg.mem.readW (wa fp p) 64) mc hR arS hO.rsi hO.rdi rsp hO.rbp hcx
      hO.mem.hA (fun _ _ _ => rfl)
  have mem1 := (hO.mem.write hk hap hfp sepA 3 (by iomega) (0 - (BitVec.ofBool c).setWidth 64)).write hk hap hfp
    sepA 4 (by iomega) (wa fp (16 * R + 23))
  rw [← m1] at mem1
  -- the inner loop
  obtain ⟨s2, x2, B⟩ := innerLoop_ok s1 k R (R + 1) ap np fp a (by omega) (by omega) (arS.frame F1)
    (by rw [bp1, eR]) (by rw [di1, show 8 * R + 8 * (R + 1) + 15 = 16 * R + 23 by ring])
    ((F1.gpr .rsi (by decide)).trans hO.rsi) cx1 dx1 cf1 of1 mem1.hA
  obtain ⟨ws, hlen, m2, hW⟩ := B.sum
  rw [show 8 * R + 8 * (R + 1) = 16 * R + 8 by ring] at m2
  have mem2 := mem1.wrs hk hap hfp sepA (16 * R + 8) ws (by iomega)
  rw [← m2] at mem2
  -- innerEnd
  have rbp2 : s2.vg.gpr .rbp = wa ap (8 * (R + 1)) := (B.frame.gpr .rbp (by decide)).trans (by rw [bp1, eR])
  obtain ⟨s3, x3, m3, bp3, cx3, zf3, F3⟩ := innerEnd_ok s2 k (R + 1) ap np fp (by omega)
    ((arS.frame F1).frame B.frame) rbp2 ((B.frame.gpr .rsp (by decide)).trans ((F1.gpr .rsp (by decide)).trans rsp))
  have mem3 : MemOK s₀.vg.mem s3.vg.mem k ap fp a := by rw [m3]; exact mem2
  have g3 : ∀ r, r ∉ [Reg.rcx, .rbp] → s3.vg.gpr r = s2.vg.gpr r := F3.gpr
  have g2 : ∀ r, r ∉ innerRegs → s2.vg.gpr r = s1.vg.gpr r := B.frame.gpr
  refine ⟨s1, s2, s3, x1, x2, x3, ⟨?_, mem3, by omega, by omega, ?_, ?_, cx3, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact hF.trans ((F1.mono (by decide)).trans ((B.frame.mono (by decide)).trans (F3.mono (by decide))))
  · rw [g3 .rsi (by decide), g2 .rsi (by decide), F1.gpr .rsi (by decide)]; exact hO.rsi
  · rw [bp3, show 8 * (R + 1) + 8 = 8 * (R + 2) by ring]
  · rw [g3 .rdi (by decide), g2 .rdi (by decide), di1, show 8 * R + 8 * (R + 2) + 7 = 16 * R + 23 by ring]
  · rw [g3 .rbx (by decide)]; exact B.rbx (by omega)
  · rw [m3, m2, m1]; rd_simp
  · rw [zf3, mem2.s2, wa_beq _ _ _ (by omega) hk hap, show 8 * (R + 1) + 8 = 8 * (R + 2) by ring]
  · intro q h1 h2
    have := hO.zero q h1 (by omega) h2
    show s3.vg.mem.readW _ 64 = 0
    rw [m3, m2, m1]; rd_simp; exact this
  · refine ⟨c, by rw [m3, m2, m1]; rd_simp, ?_⟩
    have W1 := val_wrs s1.vg.mem fp (16 * R + 8) (2 * k + 2) ws (by iomega) (by iomega)
    rw [hlen, ← m2, m1, val_slot _ _ _ _ _ (by iomega) (by iomega), val_slot _ _ _ _ _ (by iomega) (by iomega),
      twl_slot _ _ _ _ _ _ (by iomega) (by iomega), twl_slot _ _ _ _ _ _ (by iomega) (by iomega), hsum_twl8] at W1
    simp only [Nat.add_assoc, Nat.reduceAdd] at W1
    rw [m3]
    have a3 : accR s3 = accR s2 := by
      simp only [accR, g3 .r8 (by decide), g3 .r9 (by decide), g3 .r10 (by decide), g3 .r11 (by decide),
        g3 .r12 (by decide), g3 .r13 (by decide), g3 .r14 (by decide), g3 .r15 (by decide)]
    rw [a3]
    have h1 : hsum (accR s1) = (s1.vg.gpr .r8).toNat + (s1.vg.gpr .r9).toNat * 2 ^ 64 +
        (s1.vg.gpr .r10).toNat * 2 ^ 128 + (s1.vg.gpr .r11).toNat * 2 ^ 192 + (s1.vg.gpr .r12).toNat * 2 ^ 256 +
        (s1.vg.gpr .r13).toNat * 2 ^ 320 + (s1.vg.gpr .r14).toNat * 2 ^ 384 + (s1.vg.gpr .r15).toNat * 2 ^ 448 := by
      simp only [accR, hsum]; ring
    have hc : hsum (blk8 a (8 * (R + 1))) = val (fun i => a (8 * R + 8 + i)) 8 := by
      rw [eR]; simp only [blk8, hsum, val, gsum, Nat.add_zero]; ring
    rw [hc, h1, r81] at hW
    rw [e8]
    simp only [rowV] at hW ⊢
    simp only [hsum] at hS
    zify at hS hW e1 ⊢
    push_cast at W1 hS hW e1 ⊢
    rw [eP]
    rw [e9] at hS
    generalize (2 : ℤ) ^ (64 * (16 * R + 8)) = P at *
    linear_combination W1 + P * hW + P * 2 ^ 64 * e1 + hS

/-- The column loop's trace: whether the row ended at its first column block, then the rest. -/
def colsTrace (ap fp : Addr) (R k : Nat) : List Leak :=
  if 8 * R + 16 = k then [.branch true] else .branch false :: loopTrace (colTrace ap fp R) 1 (R + 2) (k / 8 - R - 3)

/-- The column blocks past row block `R`'s first. -/
theorem cols_ok (s₀ : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (hk0 : k % 8 = 0)
    (ar : Arr s₀ k ap np fp) (hrsp : s₀.vg.gpr .rsp = fp) (R : Nat) (s : S) (hI : CInv s₀ s k ap np fp a R (R + 2)) :
    ∃ s', Exec I (.ite (Rind.X86_64.Cond.vg .e) (.block []) (.loop colBody (Rind.X86_64.Cond.vg .ne))) s
        (colsTrace ap fp R k) s' ∧ CInv s₀ s' k ap np fp a R (k / 8) := by
  have hJ := hI.hJ
  by_cases h : 8 * R + 16 = k
  · refine ⟨s, ?_, by rw [show k / 8 = R + 2 by omega]; exact hI⟩
    simp only [colsTrace, h, ↓reduceIte]
    exact Exec.iteT (by show s.vg.zf = _; rw [hI.zf]; simp; omega) (Exec.block rfl)
  · obtain ⟨s', hx, hI'⟩ := loop_ok (body := colBody) (c := Rind.X86_64.Cond.vg .ne)
      (fun j s => CInv s₀ s k ap np fp a R j) (fun j => 8 * j < k) (fun j => decide (8 * j + 8 < k))
      (colTrace ap fp R) 1 (fun j s hI hj => col_step s₀ k ap np fp a hk0 ar hrsp R j s hI hj)
      (k / 8 - R - 3) (R + 2) s hI (fun i hi => by omega) (fun i hi => by simp only [decide_eq_true_eq]; omega)
      (by simp only [decide_eq_false_iff_not]; omega)
    refine ⟨s', ?_, by rwa [show R + 2 + 1 * (k / 8 - R - 3 + 1) = k / 8 by omega] at hI'⟩
    simp only [colsTrace, h, ↓reduceIte]
    exact Exec.iteF (by show s.vg.zf = _; rw [hI.zf]; simp; omega) hx

theorem carry_zero (A B c : Nat) (cc : Bool) (h : B + cc.toNat * 2 ^ 512 = A + c) (hA : A + c < 2 ^ 512) :
    cc = false := by
  cases cc
  · rfl
  · simp only [Bool.toNat_true, Nat.one_mul] at h; omega

/-- The end of row block `R`'s pass: `brk`, and `spill` unless it was the last but one. -/
def tailTrace (fp : Addr) (R k : Nat) : List Leak :=
  if 8 * R + 16 = k then [.branch true] else .branch false :: spillTrace fp R k

set_option exponentiation.threshold 4096 in
set_option maxHeartbeats 4000000 in
/-- `brk` folds the last carry, which is zero as the pass's sum fits, and `spill` stores the accumulator unless the
next row block is the last, whose triangle takes it from the registers. -/
theorem tail_ok (s₀ : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (hk0 : k % 8 = 0)
    (ar : Arr s₀ k ap np fp) (hrsp : s₀.vg.gpr .rsp = fp) (h63 : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 63) (R : Nat)
    (s : S) (hI : CInv s₀ s k ap np fp a R (k / 8)) (hR : 8 * R + 16 ≤ k) :
    ∃ s1 s', execBlock I Rind.X86_64.Sqrx8x.brk s = some (s1, brkTrace ap fp R k) ∧
      Exec I (.ite (Rind.X86_64.Cond.vg .e) (.block []) (.block Rind.X86_64.Sqrx8x.spill)) s1 (tailTrace fp R k) s' ∧
      PB s₀ s' k ap np fp a (R + 1) := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := id ar
  have hF := hI.frame
  have arS := ar.frame hF
  have rsp := (hF.gpr .rsp (by decide)).trans hrsp
  have eJ : 8 * (k / 8) = k := by omega
  have eR : 8 * (R + 1) = 8 * R + 8 := by ring
  have eX : (2 : Nat) ^ (64 * (8 * (R + 1) + k)) = 2 ^ (64 * (8 * R + k)) * 2 ^ 512 := by rw [← pow_add]; ring_nf
  have eX1 : (2 : ℤ) ^ (64 * (8 * R + k + 1)) = 2 ^ (64 * (8 * R + k)) * 2 ^ 64 := by rw [← pow_add]; ring_nf
  have eL : 8 * (k / 8 - R - 1) = k - 8 * R - 8 := by omega
  have hQ := Q_lt a k (R + 1) (by omega)
  have hq : Q a k (R + 1) = Q a k R + diag8 (fun i => a (8 * R + i)) * 2 ^ (64 * (16 * R)) +
      rowV a R * val (fun i => a (8 * R + 8 + i)) (k - 8 * R - 8) * 2 ^ (64 * (16 * R + 8)) := rfl
  obtain ⟨c, hs3, hS⟩ := hI.sum
  rw [eJ, eL, ← hq] at hS
  have hrdi : s.vg.gpr .rdi = wa fp (8 * R + k + 7) := by rw [hI.rdi, eJ]
  obtain ⟨s1, x1, m1, bp1, cx1, dx1, cf1, of1, zf1, e1, F1⟩ :=
    brk_ok s k R ap np fp a c hR arS h63 hI.rsi hrdi rsp hI.rbx hs3 hI.s4 hI.mem.hA
  have hacc : hsum (accR s) = (s.vg.gpr .r8).toNat + (s.vg.gpr .r9).toNat * 2 ^ 64 +
      (s.vg.gpr .r10).toNat * 2 ^ 128 + (s.vg.gpr .r11).toNat * 2 ^ 192 + (s.vg.gpr .r12).toNat * 2 ^ 256 +
      (s.vg.gpr .r13).toNat * 2 ^ 320 + (s.vg.gpr .r14).toNat * 2 ^ 384 + (s.vg.gpr .r15).toNat * 2 ^ 448 := by
    simp only [accR, hsum]; ring
  -- the pass's sum fits, so `brk`'s carry is zero
  have hfit : hsum (accR s) + c.toNat < 2 ^ 512 := by
    have h1 : (hsum (accR s) + c.toNat) * 2 ^ (64 * (8 * R + k)) < 2 ^ 512 * 2 ^ (64 * (8 * R + k)) := by
      rw [Nat.mul_comm (2 ^ 512), ← eX]; omega
    exact Nat.lt_of_mul_lt_mul_right h1
  have hcz := carry_zero _ _ _ _ e1 (by rw [← hacc]; exact hfit)
  rw [hcz, Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at e1
  have zf1' : s1.vg.zf = some (decide (8 * R + 16 = k)) := by
    rw [zf1, wa_beq2 fp _ _ (2 * k + 9) (by omega) (by omega) (by omega) hfp]
    simp only [Option.some.injEq, decide_eq_decide]; constructor <;> intro <;> omega
  have mem1 : MemOK s₀.vg.mem s1.vg.mem k ap fp a := by
    rw [m1]; exact hI.mem.write hk hap hfp sepA (8 * R + k + 7) (by iomega) _
  have g1 : ∀ r, r ∉ [Reg.rbx, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] →
      s1.vg.gpr r = s.vg.gpr r := F1.gpr
  -- `t` after `brk`'s store
  have V1 := val_write s.vg.mem fp (8 * R + k) (2 * k + 2) (s1.vg.gpr .r8) (by omega) (by omega)
  rw [← m1, hI.zero _ (by omega) (by omega)] at V1
  have T1 : hsum (twl s1.vg.mem fp (8 * R + k + 1) 7) = 0 := by
    rw [m1, twl_write _ _ _ _ _ _ (by omega) (by omega)]
    exact hsum_twl_zero _ _ _ _ fun i hi => hI.zero _ (by omega) (by omega)
  by_cases h : 8 * R + 16 = k
  · refine ⟨s1, s1, x1, ?_, ⟨hF.trans (F1.mono (by decide)), mem1, by omega, ?_, ?_, bp1, by rw [dx1, eR], cf1, of1,
      ?_, ?_⟩⟩
    · simp only [tailTrace, h, ↓reduceIte]
      exact Exec.iteT (by show s1.vg.zf = _; rw [zf1']; simp [h]) (Exec.block rfl)
    · rw [g1 .rsi (by decide), hI.rsi, eR]
    · rw [g1 .rdi (by decide), hrdi, show 8 * R + k + 7 = 16 * (R + 1) + 7 by omega]
    · intro q h1 h2
      have := hI.zero q (by omega) h2
      show s1.vg.mem.readW _ 64 = 0
      rw [m1]; rd_simp; exact this
    · rw [show 16 * (R + 1) + 1 = 8 * R + k + 1 by omega, T1, eX1]
      simp only [hsum] at hS ⊢
      zify at hS e1
      push_cast at V1 hS e1 ⊢
      generalize (2 : ℤ) ^ (64 * (8 * R + k)) = X at *
      linear_combination V1 + hS + X * e1
  · obtain ⟨s2, x2, m2, di2, r92, r102, r112, r122, r132, r142, r152, cf2, of2, F2⟩ :=
      spill_ok s1 k R ap np fp (fun p => s1.vg.mem.readW (wa fp p) 64) (by omega) (arS.frame F1)
        (by rw [g1 .rdi (by decide), hrdi]) cx1 (fun _ _ _ => rfl)
    have mw : s2.vg.mem = wrs s1.vg.mem fp (8 * R + k + 1) (regs7 s1) := by
      rw [m2]; simp only [wrs, Nat.add_assoc, Nat.reduceAdd]
    have g2 : ∀ r, r ∉ [Reg.rdi, .r9, .r10, .r11, .r12, .r13, .r14, .r15] → s2.vg.gpr r = s1.vg.gpr r := F2.gpr
    refine ⟨s1, s2, x1, ?_, ⟨hF.trans ((F1.mono (by decide)).trans (F2.mono (by decide))), ?_, by omega, ?_, ?_, ?_,
      ?_, cf2.trans cf1, of2.trans of1, ?_, ?_⟩⟩
    · simp only [tailTrace, h, ↓reduceIte]
      exact Exec.iteF (by show s1.vg.zf = _; rw [zf1']; simp [h]) (Exec.block x2)
    · rw [mw]; exact mem1.wrs hk hap hfp sepA _ _ (by iomega)
    · rw [g2 .rsi (by decide), g1 .rsi (by decide), hI.rsi, eR]
    · rw [di2, show 16 * (R + 1) + 7 = 16 * R + 23 by ring]
    · rw [g2 .rbp (by decide), bp1]
    · rw [g2 .rdx (by decide), dx1, eR]
    · intro q h1 h2
      have := hI.zero q (by omega) h2
      show s2.vg.mem.readW _ 64 = 0
      rw [mw, m1]; rd_simp; exact this
    · have ht : twl s2.vg.mem fp (16 * (R + 1) + 1) 7 = regs7 s2 := by
        rw [show 16 * (R + 1) + 1 = 16 * R + 17 by ring]
        simp only [regs7, r92, r102, r112, r122, r132, r142, r152, twl, tw, Nat.add_assoc, Nat.reduceAdd]
        rw [mw]; rd_simp
      rw [ht, sub_self, mul_zero, add_zero]
      have W1 := val_wrs s1.vg.mem fp (8 * R + k + 1) (2 * k + 2) (regs7 s1) (by iomega) (by omega)
      rw [← mw, show (regs7 s1).length = 7 from rfl, T1] at W1
      rw [eX1] at W1
      simp only [hsum] at hS W1
      zify at hS e1
      push_cast at V1 W1 hS e1 ⊢
      generalize (2 : ℤ) ^ (64 * (8 * R + k)) = X at *
      linear_combination W1 + V1 + hS + X * e1

/-- Row block `R`'s pass: its first column block, the rest, `brk` and `spill`, and the next triangle. -/
def passTrace (ap fp : Addr) (k R : Nat) : List Leak :=
  preTrace ap fp R ++ (innerLoopTrace ap fp R (R + 1) ++ (innerEndTrace fp ++ (colsTrace ap fp R k ++
    (brkTrace ap fp R k ++ (tailTrace fp R k ++ triTrace ap fp (R + 1))))))

/-- Row block `R`'s pass, from its triangle to the next's. -/
theorem pass_ok (s₀ : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (hk0 : k % 8 = 0)
    (ar : Arr s₀ k ap np fp) (hrsp : s₀.vg.gpr .rsp = fp) (h63 : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 63) (R : Nat)
    (s : S) (hO : OA s₀ s k ap np fp a R) (hR : 8 * R + 16 ≤ k) :
    ∃ s', Exec I Rind.X86_64.Sqrx8x.outerPass s (passTrace ap fp k R) s' ∧
      I.eval (Rind.X86_64.Cond.vg .ne) s' = some (decide (8 * R + 16 < k)) ∧ OA s₀ s' k ap np fp a (R + 1) := by
  obtain ⟨s1, s2, s3, x1, x2, x3, hC⟩ := first_col s₀ k ap np fp a ar hrsp R s hO hR
  obtain ⟨s4, x4, hC'⟩ := cols_ok s₀ k ap np fp a hk0 ar hrsp R s3 hC
  obtain ⟨s5, s6, x5, x6, hP⟩ := tail_ok s₀ k ap np fp a hk0 ar hrsp h63 R s4 hC' hR
  obtain ⟨s7, x7, hO'⟩ := tri_step s₀ k ap np fp a ar hrsp (R + 1) s6 hP
  refine ⟨s7, Exec.seq (Exec.block x1) (Exec.seq x2 (Exec.seq (Exec.block x3) (Exec.seq x4
    (Exec.seq (Exec.block x5) (Exec.seq x6 (Exec.block x7)))))), ?_, hO'⟩
  have := hO'.hR
  rw [eval_ne hO'.zf]; simp only [Option.some.injEq]; cases h : decide (8 * R + 16 < k) <;> simp_all <;> omega

/-- The passes: none when `a` is one row block, else one for each row block but the last. -/
def outerTrace (ap fp : Addr) (k : Nat) : List Leak :=
  if 8 = k then [.branch true] else .branch false :: loopTrace (passTrace ap fp k) 1 0 (k / 8 - 2)

/-- The passes, from the first row block's triangle to the last's. -/
theorem outer_ok (s₀ : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (hk0 : k % 8 = 0)
    (ar : Arr s₀ k ap np fp) (hrsp : s₀.vg.gpr .rsp = fp) (h63 : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 63) (s : S)
    (hO : OA s₀ s k ap np fp a 0) :
    ∃ s', Exec I (.ite (Rind.X86_64.Cond.vg .e) (.block []) (.loop Rind.X86_64.Sqrx8x.outerPass
        (Rind.X86_64.Cond.vg .ne))) s (outerTrace ap fp k) s' ∧ OA s₀ s' k ap np fp a (k / 8 - 1) := by
  have := hO.hR
  by_cases h : 8 = k
  · refine ⟨s, ?_, by rw [show k / 8 - 1 = 0 by omega]; exact hO⟩
    simp only [outerTrace, h, ↓reduceIte]
    exact Exec.iteT (by show s.vg.zf = _; rw [hO.zf]; simp; omega) (Exec.block rfl)
  · obtain ⟨s', hx, hO'⟩ := loop_ok (body := Rind.X86_64.Sqrx8x.outerPass) (c := Rind.X86_64.Cond.vg .ne)
      (fun j s => OA s₀ s k ap np fp a j) (fun j => 8 * j + 16 ≤ k) (fun j => decide (8 * j + 16 < k))
      (passTrace ap fp k) 1 (fun j s hI hj => pass_ok s₀ k ap np fp a hk0 ar hrsp h63 j s hI hj)
      (k / 8 - 2) 0 s hO (fun i hi => by omega) (fun i hi => by simp only [decide_eq_true_eq]; omega)
      (by simp only [decide_eq_false_iff_not]; omega)
    refine ⟨s', ?_, by rwa [show 0 + 1 * (k / 8 - 2 + 1) = k / 8 - 1 by omega] at hO'⟩
    simp only [outerTrace, h, ↓reduceIte]
    exact Exec.iteF (by show s.vg.zf = _; rw [hO.zf]; simp; omega) hx

end rind.x86_64.sqrx8x
