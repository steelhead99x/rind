import Rind.X86_64.Sqrx8xVal

/-! # bn_sqrx8x_internal's outer pass

An outer pass from row block `R` adds the row block times every column block past it into `t`, then runs
the next row block's triangle. Its invariant, at the head of each column block `J`: `t`'s value, with the
accumulator at its word `8R + 8J` and the carry the mask in slot 3 holds, is `Q R`, row block `R`'s
triangle, and its products with the column blocks so far. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.sqrx8x

open Lean Meta Elab Tactic in
/-- Clears the hypotheses about words' values, sums of products that `omega` would otherwise take in, and give
up on, when it proves an index's bound. -/
elab "clear_words" : tactic => withMainContext do
  let mut g ← getMainGoal
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let big := (ty.find? fun e =>
      (e.isAppOfArity ``BitVec.toNat 2 && !e.appArg!.isFVar) || e.isConstOf ``hsum || e.isConstOf ``gsum ||
        e.isConstOf ``Q || e.isConstOf ``diag8).isSome
    if big then
      try g ← g.clear d.fvarId catch _ => pure ()
  replaceMainGoal [g]

/-- `omega` on indices, without the hypotheses about words' values. -/
macro "iomega" : tactic =>
  `(tactic| first
    | (clear_words; omega)
    | (simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]; clear_words; omega))

/-- Reads through stores to other words, their bounds by `omega`. -/
macro "rd_simp" : tactic => `(tactic|
  simp (disch := iomega) only [readW_wrs, readW_writeW_wa, readW_writeW_self])

/-- The general-purpose registers but `rsp`. -/
abbrev allRegs : List Reg :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- What the triangle phase keeps of memory: all but slots 1 to 4 and `t`, `a`'s words, and slots 1 and 2,
`8k` and `a`'s end, which the entry stores. -/
structure MemOK (M₀ M : Mem) (k : Nat) (ap fp : Addr) (a : Nat → BitVec 64) : Prop where
  keeps : Keeps M₀ M fp k
  hA : ∀ i < k, M.readW (wa ap i) 64 = a i
  s1 : M.readW (wa fp 1) 64 = BitVec.ofNat 64 (8 * k)
  s2 : M.readW (wa fp 2) 64 = wa ap k

theorem MemOK.write {M₀ M : Mem} {k : Nat} {ap fp : Addr} {a : Nat → BitVec 64} (h : MemOK M₀ M k ap fp a)
    (hk : k < 2 ^ 29) (hap : ap.toNat + 8 * k ≤ 2 ^ 64) (hfp : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 64)
    (sepA : ap.toNat + 8 * k ≤ fp.toNat ∨ fp.toNat + 8 * (2 * k + 9) ≤ ap.toNat)
    (x : Nat) (hx : x = 3 ∨ x = 4 ∨ (7 ≤ x ∧ x < 2 * k + 9)) (v : BitVec 64) :
    MemOK M₀ (M.writeW (wa fp x) v) k ap fp a where
  keeps := by
    intro y h1 h2
    have e : (M.writeW (wa fp x) v) y = M y := by
      unfold Mem.writeW; apply write_other; simp only [wa] at h1 h2 ⊢; rcases hx with rfl | rfl | hx <;> bv_omega
    rw [e]; exact h.keeps y h1 h2
  hA := fun i hi => by
    rw [readW_writeW_wa _ _ _ _ _ _ (by omega) (by omega) (by omega)]; exact h.hA i hi
  s1 := by rw [readW_writeW_wa _ _ _ _ _ _ (by omega) (by omega) (by omega)]; exact h.s1
  s2 := by rw [readW_writeW_wa _ _ _ _ _ _ (by omega) (by omega) (by omega)]; exact h.s2

theorem MemOK.wrs {M₀ M : Mem} {k : Nat} {ap fp : Addr} {a : Nat → BitVec 64} (h : MemOK M₀ M k ap fp a)
    (hk : k < 2 ^ 29) (hap : ap.toNat + 8 * k ≤ 2 ^ 64) (hfp : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 64)
    (sepA : ap.toNat + 8 * k ≤ fp.toNat ∨ fp.toNat + 8 * (2 * k + 9) ≤ ap.toNat)
    (p : Nat) (ws : List (BitVec 64)) (hp : p + ws.length ≤ 2 * k + 2) :
    MemOK M₀ (rind.x86_64.sqrx8x.wrs M fp p ws) k ap fp a := by
  induction ws generalizing M p with
  | nil => exact h
  | cons w ws ih =>
    simp only [List.length_cons] at hp
    exact ih (h.write hk hap hfp sepA (p + 7) (by omega) w) (p + 1) (by omega)

/-- A slot's store leaves `t`. -/
theorem tw_slot (M : Mem) (fp : Addr) (i q : Nat) (v : BitVec 64) (hi : i < 7)
    (hq : fp.toNat + 8 * (q + 8) ≤ 2 ^ 64) : tw (M.writeW (wa fp i) v) fp q = tw M fp q :=
  readW_writeW_wa _ _ _ _ _ _ (by omega) (by omega) (by omega)

theorem val_slot (M : Mem) (fp : Addr) (i N : Nat) (v : BitVec 64) (hi : i < 7)
    (hfp : fp.toNat + 8 * (N + 7) ≤ 2 ^ 64) : val (tw (M.writeW (wa fp i) v) fp) N = val (tw M fp) N :=
  gsum_congr fun m hm => by rw [tw_slot _ _ _ _ _ hi (by omega)]

theorem twl_slot (M : Mem) (fp : Addr) (i q n : Nat) (v : BitVec 64) (hi : i < 7)
    (hfp : fp.toNat + 8 * (q + n + 7) ≤ 2 ^ 64) : twl (M.writeW (wa fp i) v) fp q n = twl M fp q n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => simp only [twl]; rw [tw_slot _ _ _ _ _ hi (by omega), ih (q + 1) (by omega)]

/-- Two words of `a` are the same exactly when their indices are. -/
theorem wa_beq (ap : Addr) (i k : Nat) (hi : i ≤ k) (hk : k < 2 ^ 29) (hap : ap.toNat + 8 * k ≤ 2 ^ 64) :
    (wa ap i - wa ap k == 0) = decide (i = k) := by
  by_cases h : i = k
  · subst h; simp
  · have : (wa ap i - wa ap k == 0) = false := by
      rw [beq_eq_false_iff_ne]; simp only [wa]; bv_omega
    rw [this]; simp [h]

set_option exponentiation.threshold 4096 in
/-- `t`'s eight words from word `p` as a value, as the blocks read them. -/
theorem hsum_twl8 (M : Mem) (fp : Addr) (p : Nat) :
    hsum (twl M fp p 8) = (M.readW (wa fp (p + 7)) 64).toNat + (M.readW (wa fp (p + 8)) 64).toNat * 2 ^ 64 +
      (M.readW (wa fp (p + 9)) 64).toNat * 2 ^ 128 + (M.readW (wa fp (p + 10)) 64).toNat * 2 ^ 192 +
      (M.readW (wa fp (p + 11)) 64).toNat * 2 ^ 256 + (M.readW (wa fp (p + 12)) 64).toNat * 2 ^ 320 +
      (M.readW (wa fp (p + 13)) 64).toNat * 2 ^ 384 + (M.readW (wa fp (p + 14)) 64).toNat * 2 ^ 448 := by
  simp only [twl, hsum, tw, Nat.add_assoc, Nat.reduceAdd]; ring

/-- The column loop before column block `J`'s `reload`, in row block `R`'s pass. -/
structure CInv (s₀ s : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (R J : Nat) : Prop where
  frame : Frame s₀ s allRegs
  mem : MemOK s₀.vg.mem s.vg.mem k ap fp a
  hRJ : R + 2 ≤ J
  hJ : 8 * J ≤ k
  rsi : s.vg.gpr .rsi = wa ap (8 * R + 8)
  rbp : s.vg.gpr .rbp = wa ap (8 * J)
  rcx : s.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8)
  rdi : s.vg.gpr .rdi = wa fp (8 * R + 8 * J + 7)
  rbx : s.vg.gpr .rbx = 0
  s4 : s.vg.mem.readW (wa fp 4) 64 = wa fp (16 * R + 23)
  zf : s.vg.zf = some (decide (8 * J = k))
  zero : ∀ q, 8 * R + k ≤ q → q < 2 * k + 2 → tw s.vg.mem fp q = 0
  sum : ∃ c : Bool, s.vg.mem.readW (wa fp 3) 64 = 0 - (BitVec.ofBool c).setWidth 64 ∧
    val (tw s.vg.mem fp) (2 * k + 2) + (hsum (accR s) + c.toNat) * 2 ^ (64 * (8 * R + 8 * J)) =
      Q a k R + diag8 (fun i => a (8 * R + i)) * 2 ^ (64 * (16 * R)) +
        rowV a R * val (fun i => a (8 * R + 8 + i)) (8 * (J - R - 1)) * 2 ^ (64 * (16 * R + 8))

/-- One column block's trace: `reload`, the inner loop, and `innerEnd`. -/
def colTrace (ap fp : Addr) (R J : Nat) : List Leak :=
  reloadTrace ap fp R J ++ (innerLoopTrace ap fp R J ++ innerEndTrace fp)

/-- The column loop's body. -/
abbrev colBody : Prog I :=
  .seq (.block Rind.X86_64.Sqrx8x.reload)
    (.seq (.loop (.block Rind.X86_64.Sqrx8x.inner) (Rind.X86_64.Cond.vg .ne)) (.block Rind.X86_64.Sqrx8x.innerEnd))

set_option exponentiation.threshold 4096 in
set_option maxHeartbeats 4000000 in
/-- Column block `J`: `reload`, the inner loop, and `innerEnd`. -/
theorem col_step (s₀ : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (hk0 : k % 8 = 0) (ar : Arr s₀ k ap np fp)
    (hrsp : s₀.vg.gpr .rsp = fp) (R J : Nat) (s : S) (hI : CInv s₀ s k ap np fp a R J) (hJ : 8 * J < k) :
    ∃ s', Exec I colBody s (colTrace ap fp R J) s' ∧
      I.eval (Rind.X86_64.Cond.vg .ne) s' = some (decide (8 * J + 8 < k)) ∧
      CInv s₀ s' k ap np fp a R (J + 1) := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := id ar
  have hF := hI.frame
  have arS := ar.frame hF
  have rsp := (hF.gpr .rsp (by decide)).trans hrsp
  have hRJ := hI.hRJ
  -- the column arithmetic, before the context fills up
  have eJ : (fun i => a (8 * R + 8 + (8 * (J - R - 1) + i))) = fun i => a (8 * J + i) := by
    funext i; congr 1; omega
  have eJ1 : 8 * (J - R - 1) + 8 = 8 * (J + 1 - R - 1) := by omega
  have eX : (2 : Nat) ^ (64 * (8 * R + 8 * J)) = 2 ^ (64 * (16 * R + 8)) * 2 ^ (64 * (8 * (J - R - 1))) := by
    rw [← pow_add]; congr 1; omega
  have eX8 : (2 : Nat) ^ (64 * (8 * R + 8 * (J + 1))) = 2 ^ (64 * (8 * R + 8 * J)) * 2 ^ 512 := by
    rw [← pow_add]; ring_nf
  obtain ⟨c, hs3, hS⟩ := hI.sum
  -- reload
  obtain ⟨s1, x1, c', m1, di1, dx1, bx1, cf1, of1, e1, F1⟩ :=
    reload_ok s k R J ap np fp a (fun p => s.vg.mem.readW (wa fp p) 64) c (by iomega) (by iomega) arS hI.rsi hI.rdi
      rsp hI.rbx hs3 hI.mem.hA (fun _ _ _ => rfl)
  have mem1 := hI.mem.write hk hap hfp sepA 3 (by iomega) (0 - (BitVec.ofBool c').setWidth 64)
  rw [← m1] at mem1
  -- the inner loop
  obtain ⟨s2, x2, B⟩ := innerLoop_ok s1 k R J ap np fp a (by iomega) (by iomega) (arS.frame F1)
    ((F1.gpr .rbp (by decide)).trans hI.rbp) (by rw [di1])
    ((F1.gpr .rsi (by decide)).trans hI.rsi) ((F1.gpr .rcx (by decide)).trans hI.rcx) dx1 cf1 of1 mem1.hA
  obtain ⟨ws, hlen, m2, hW⟩ := B.sum
  have mem2 := mem1.wrs hk hap hfp sepA (8 * R + 8 * J) ws (by iomega)
  rw [← m2] at mem2
  -- innerEnd
  have rbp2 := (B.frame.gpr .rbp (by decide)).trans ((F1.gpr .rbp (by decide)).trans hI.rbp)
  obtain ⟨s3, x3, m3, bp3, cx3, zf3, F3⟩ := innerEnd_ok s2 k J ap np fp (by iomega) ((arS.frame F1).frame B.frame)
    rbp2 ((B.frame.gpr .rsp (by decide)).trans ((F1.gpr .rsp (by decide)).trans rsp))
  have mem3 : MemOK s₀.vg.mem s3.vg.mem k ap fp a := by rw [m3]; exact mem2
  have g3 : ∀ r, r ∉ [Reg.rcx, .rbp] → s3.vg.gpr r = s2.vg.gpr r := F3.gpr
  have g2 : ∀ r, r ∉ innerRegs → s2.vg.gpr r = s1.vg.gpr r := B.frame.gpr
  have g1 : ∀ r, r ∉ [Reg.rax, .rbx, .rdx, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] →
      s1.vg.gpr r = s.vg.gpr r := F1.gpr
  refine ⟨s3, Exec.seq (Exec.block x1) (Exec.seq x2 (Exec.block x3)), ?_, ⟨?_, mem3, by iomega, by iomega, ?_, bp3,
    cx3, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [eval_ne zf3, mem2.s2, wa_beq _ _ _ (by iomega) hk hap]
    clear_words
    by_cases h : 8 * J + 8 = k
    · simp [h]
    · simp only [h, decide_false, Bool.not_false, Option.some.injEq]; symm; simp only [decide_eq_true_eq]; omega
  · exact hF.trans ((F1.mono (by decide)).trans ((B.frame.mono (by decide)).trans (F3.mono (by decide))))
  · rw [g3 .rsi (by decide), g2 .rsi (by decide), g1 .rsi (by decide)]; exact hI.rsi
  · rw [g3 .rdi (by decide), g2 .rdi (by decide), di1]; congr 1
  · rw [g3 .rbx (by decide)]; exact B.rbx (by iomega)
  · rw [m3, m2, m1]; rd_simp; exact hI.s4
  · rw [zf3, mem2.s2, wa_beq _ _ _ (by iomega) hk hap]; congr 2
  · intro q h1 h2
    have := hI.zero q h1 h2
    simp only [tw] at this ⊢
    rw [m3, m2, m1]; rd_simp; exact this
  · refine ⟨c', ?_, ?_⟩
    · rw [m3, m2, m1]; rd_simp
    · -- `t`'s value after the inner loop's stores
      have W1 := val_wrs s1.vg.mem fp (8 * R + 8 * J) (2 * k + 2) ws (by iomega) (by iomega)
      rw [hlen, ← m2, m1, val_slot _ _ _ _ _ (by iomega) (by iomega), twl_slot _ _ _ _ _ _ (by iomega) (by iomega),
        hsum_twl8] at W1
      rw [m3]
      -- the accumulator
      have a3 : accR s3 = accR s2 := by
        simp only [accR, g3 .r8 (by decide), g3 .r9 (by decide), g3 .r10 (by decide), g3 .r11 (by decide),
          g3 .r12 (by decide), g3 .r13 (by decide), g3 .r14 (by decide), g3 .r15 (by decide)]
      rw [a3]
      have h1 : hsum (accR s1) = (s1.vg.gpr .r8).toNat + (s1.vg.gpr .r9).toNat * 2 ^ 64 +
          (s1.vg.gpr .r10).toNat * 2 ^ 128 + (s1.vg.gpr .r11).toNat * 2 ^ 192 + (s1.vg.gpr .r12).toNat * 2 ^ 256 +
          (s1.vg.gpr .r13).toNat * 2 ^ 320 + (s1.vg.gpr .r14).toNat * 2 ^ 384 + (s1.vg.gpr .r15).toNat * 2 ^ 448 := by
        simp only [accR, hsum]; ring
      have h0 : hsum (accR s) = (s.vg.gpr .r8).toNat + (s.vg.gpr .r9).toNat * 2 ^ 64 +
          (s.vg.gpr .r10).toNat * 2 ^ 128 + (s.vg.gpr .r11).toNat * 2 ^ 192 + (s.vg.gpr .r12).toNat * 2 ^ 256 +
          (s.vg.gpr .r13).toNat * 2 ^ 320 + (s.vg.gpr .r14).toNat * 2 ^ 384 + (s.vg.gpr .r15).toNat * 2 ^ 448 := by
        simp only [accR, hsum]; ring
      -- the row's columns so far, one block on
      have hc : hsum (blk8 a (8 * J)) = val (fun i => a (8 * R + 8 + (8 * (J - R - 1) + i))) 8 := by
        rw [eJ]; simp only [blk8, hsum, val, gsum, Nat.add_zero]; ring
      have hT := val_split (fun i => a (8 * R + 8 + i)) (8 * (J - R - 1)) 8
      rw [eJ1] at hT
      rw [hT, eX8]
      rw [hc, h1] at hW
      rw [h0] at hS
      simp only [rowV] at hS ⊢
      have eXz : (2 : ℤ) ^ (64 * (8 * R + 8 * J)) = 2 ^ (64 * (16 * R + 8)) * 2 ^ (64 * (8 * (J - R - 1))) := by
        exact_mod_cast eX
      zify at hS hW e1 ⊢
      rw [eXz] at hS W1 ⊢
      generalize (2 : ℤ) ^ (64 * (16 * R + 8)) = Y at *
      generalize (2 : ℤ) ^ (64 * (8 * (J - R - 1))) = Z at *
      push_cast at W1
      linear_combination W1 + hS + Y * Z * hW + Y * Z * e1

end rind.x86_64.sqrx8x
