import Rind.X86_64.Sqrx8xTriProof

/-! # bn_sqrx8x_internal's inner loop

Eight runs of `inner` add a row block's eight words of `a`, from word `8R`, times a column block's, from word
`8J`, into the accumulator `r8..r15`, storing its low word after each into `t`'s words `8R + 8J` on. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.sqrx8x

/-- `M` with the words `ws` stored at `t`'s word `p` on. -/
def wrs (M : Mem) (fp : Addr) (p : Nat) : List (BitVec 64) → Mem
  | [] => M
  | w :: ws => wrs (M.writeW (wa fp (p + 7)) w) fp (p + 1) ws

theorem wrs_append (M : Mem) (fp : Addr) (p : Nat) (ws : List (BitVec 64)) (w : BitVec 64) :
    wrs M fp p (ws ++ [w]) = (wrs M fp p ws).writeW (wa fp (p + ws.length + 7)) w := by
  induction ws generalizing M p with
  | nil => rfl
  | cons x ws ih => simp only [List.cons_append, wrs, ih, List.length_cons]; congr 3; omega

/-- A word apart from `t`'s words `p` to `p + |ws|` keeps its value. -/
theorem readW_wrs (M : Mem) (fp q : Addr) (p y : Nat) (ws : List (BitVec 64))
    (hp : fp.toNat + 8 * (p + ws.length + 7) ≤ 2 ^ 64) (hq : q.toNat + 8 * y + 8 ≤ 2 ^ 64)
    (h : fp.toNat + 8 * (p + ws.length + 7) ≤ q.toNat + 8 * y ∨ q.toNat + 8 * y + 8 ≤ fp.toNat + 8 * (p + 7)) :
    (wrs M fp p ws).readW (wa q y) 64 = M.readW (wa q y) 64 := by
  induction ws generalizing M p with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.length_cons] at hp h
    rw [wrs, ih _ _ (by omega) (by omega), readW_writeW_wa _ _ _ _ _ _ (by omega) hq (by omega)]

theorem eval_ne {s : S} {z : Bool} (h : s.vg.zf = some z) : I.eval (Rind.X86_64.Cond.vg .ne) s = some (!z) := by
  simp only [Rind.X86_64.isa, Rind.X86_64.eval, VG.X86_64.eval, h, Option.map_some]

/-- The accumulator's words. -/
abbrev accR (s : S) : List (BitVec 64) :=
  [s.vg.gpr .r8, s.vg.gpr .r9, s.vg.gpr .r10, s.vg.gpr .r11, s.vg.gpr .r12, s.vg.gpr .r13, s.vg.gpr .r14,
    s.vg.gpr .r15]

/-- Eight words of `a`, from word `c`. -/
abbrev blk8 (a : Nat → BitVec 64) (c : Nat) : List (BitVec 64) :=
  [a c, a (c + 1), a (c + 2), a (c + 3), a (c + 4), a (c + 5), a (c + 6), a (c + 7)]

/-- The registers the inner loop writes. -/
abbrev innerRegs : List Reg := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The inner loop before its run `j`: `t`'s words `8R + 8J` on, `ws`, stored; the accumulator and the stored
words are the accumulator at the start plus row words `8R` to `8R + j` times the column block. -/
structure BInv (s₁ s : S) (k R J : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (j : Nat) : Prop where
  j8 : j ≤ 8
  frame : Frame s₁ s innerRegs
  rcx : s.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8 + j)
  rdx : s.vg.gpr .rdx = a (8 * R + j)
  cf : s.vg.cf = some false
  of : s.vg.of = some false
  rbx : 0 < j → s.vg.gpr .rbx = 0
  sum : ∃ ws : List (BitVec 64), ws.length = j ∧ s.vg.mem = wrs s₁.vg.mem fp (8 * R + 8 * J) ws ∧
    hsum ws + 2 ^ (64 * j) * hsum (accR s) = hsum (accR s₁) + val (fun i => a (8 * R + i)) j * hsum (blk8 a (8 * J))

theorem wa_rcx (b : Addr) (q j : Nat) (h : 8 ≤ q + j) :
    wa b q + BitVec.ofNat 64 (2 ^ 64 - 8 + j) * 8#64 = wa b (q + j - 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [wa, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem rcx_inc (j : Nat) (h : j < 8) :
    BitVec.ofNat 64 (2 ^ 64 - 8 + j) + 1 = BitVec.ofNat 64 (2 ^ 64 - 8 + (j + 1)) := by
  interval_cases j <;> decide

theorem rcx_inc' (j : Nat) (h : j < 8) :
    BitVec.ofNat 64 (2 ^ 64 - 8 + j) + 1#64 = BitVec.ofNat 64 (2 ^ 64 - 8 + (j + 1)) := rcx_inc j h

theorem rcx_zf (j : Nat) (h : j < 8) : (BitVec.ofNat 64 (2 ^ 64 - 8 + j) + 1 == 0) = !decide (j + 1 < 8) := by
  interval_cases j <;> decide

/-- An inner run's carries out are zero: its accumulator and product fit in nine words. -/
theorem innerF_flags (x a0 a1 a2 a3 a4 a5 a6 a7 r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64) :
    let F := innerF x a0 a1 a2 a3 a4 a5 a6 a7 r8 r9 r10 r11 r12 r13 r14 r15 false false
    F.cf = false ∧ F.of = false ∧
    hsum [F.w, F.r8, F.r9, F.r10, F.r11, F.r12, F.r13, F.r14, F.r15] =
      hsum [r8, r9, r10, r11, r12, r13, r14, r15] + x.toNat * hsum [a0, a1, a2, a3, a4, a5, a6, a7] := by
  intro F
  have h := innerF_acct x a0 a1 a2 a3 a4 a5 a6 a7 r8 r9 r10 r11 r12 r13 r14 r15 false false
  simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at h
  have hr := hsum_lt [r8, r9, r10, r11, r12, r13, r14, r15]
  have ha := hsum_lt [a0, a1, a2, a3, a4, a5, a6, a7]
  have hx : x.toNat * hsum [a0, a1, a2, a3, a4, a5, a6, a7] ≤ (2 ^ 64 - 1) * (2 ^ 512 - 1) :=
    Nat.mul_le_mul (by have := x.isLt; omega) (by simp only [List.length_cons, List.length_nil] at ha; omega)
  simp only [List.length_cons, List.length_nil] at hr
  have hcf : F.cf = false := by
    cases hc : F.cf
    · rfl
    · rw [hc] at h; simp only [Bool.toNat_true] at h; omega
  have hof : F.of = false := by
    cases hc : F.of
    · rfl
    · rw [hc] at h; simp only [Bool.toNat_true] at h; omega
  rw [hcf, hof] at h
  simp only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at h
  exact ⟨hcf, hof, h⟩

set_option maxHeartbeats 4000000 in
theorem inner_step (s₁ : S) (k R J : Nat) (ap np fp : Addr) (a : Nat → BitVec 64)
    (hRJ : R < J) (hJ : 8 * J + 8 ≤ k) (ar : Arr s₁ k ap np fp)
    (hrbp : s₁.vg.gpr .rbp = wa ap (8 * J)) (hrdi : s₁.vg.gpr .rdi = wa fp (8 * R + 8 * J + 15))
    (hrsi : s₁.vg.gpr .rsi = wa ap (8 * R + 8))
    (hA : ∀ i < k, s₁.vg.mem.readW (wa ap i) 64 = a i)
    (j : Nat) (s : S) (hI : BInv s₁ s k R J ap np fp a j) (hj : j < 8) :
    ∃ s', Exec I (.block Rind.X86_64.Sqrx8x.inner) s (innerTrace ap fp (8 * J) (8 * R + 8 * J + j + 7)
        (8 * R + j + 1)) s' ∧
      I.eval (Rind.X86_64.Cond.vg .ne) s' = some (decide (j + 1 < 8)) ∧
      BInv s₁ s' k R J ap np fp a (j + 1) := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := id ar
  have hF := hI.frame
  have g : ∀ r, r ∉ innerRegs → s.vg.gpr r = s₁.vg.gpr r := hF.gpr
  obtain ⟨ws, hlen, hmem, hS⟩ := hI.sum
  have hA' : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i := by
    intro i hi
    rw [hmem, readW_wrs _ _ _ _ _ _ (by omega) (by omega) (by omega)]
    exact hA i hi
  obtain ⟨s', hx, ocx, odx, o8, o9, o10, o11, o12, o13, o14, o15, ocf, ozf, oof, omem, obx, oF⟩ :=
    inner_ok s k (8 * J) (8 * R + 8 * J + j + 7) (8 * R + j + 1) ap np fp (a (8 * R + j)) false false a
      (by omega) (by omega) (by omega) (ar.frame hF) ((g .rbp (by decide)).trans hrbp) hI.rdx
      (by rw [g .rdi (by decide), hrdi, hI.rcx, wa_rcx _ _ _ (by omega)]; congr 1; omega)
      (by rw [g .rsi (by decide), hrsi, hI.rcx, rcx_inc' j hj, wa_rcx _ _ _ (by omega)]; congr 1; omega)
      hI.cf hI.of hA'
  obtain ⟨fcf, fof, fsum⟩ := innerF_flags (a (8 * R + j)) (a (8 * J)) (a (8 * J + 1)) (a (8 * J + 2))
    (a (8 * J + 3)) (a (8 * J + 4)) (a (8 * J + 5)) (a (8 * J + 6)) (a (8 * J + 7)) (s.vg.gpr .r8) (s.vg.gpr .r9)
    (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12) (s.vg.gpr .r13) (s.vg.gpr .r14) (s.vg.gpr .r15)
  generalize innerF (a (8 * R + j)) (a (8 * J)) (a (8 * J + 1)) (a (8 * J + 2)) (a (8 * J + 3)) (a (8 * J + 4))
    (a (8 * J + 5)) (a (8 * J + 6)) (a (8 * J + 7)) (s.vg.gpr .r8) (s.vg.gpr .r9) (s.vg.gpr .r10)
    (s.vg.gpr .r11) (s.vg.gpr .r12) (s.vg.gpr .r13) (s.vg.gpr .r14) (s.vg.gpr .r15) false false = F
    at o8 o9 o10 o11 o12 o13 o14 o15 ocf omem fcf fof fsum
  refine ⟨s', Exec.block hx, ?_, by omega, hF.trans (oF.mono (by decide)), ?_, ?_, ?_, ?_, fun _ => obx,
    ⟨ws ++ [F.w], by simp [hlen], ?_, ?_⟩⟩
  · rw [eval_ne ozf, hI.rcx, rcx_zf j hj, Bool.not_not]
  · rw [ocx, hI.rcx, rcx_inc j hj]
  · rw [odx]; congr 1
  · rw [ocf, fcf]
  · rw [oof, hI.rcx, rcx_of j hj]
  · rw [omem, wrs_append, hlen, hmem]
  · rw [hsum_append, hlen]
    simp only [accR, o8, o9, o10, o11, o12, o13, o14, o15]
    have e1 : hsum [F.w, F.r8, F.r9, F.r10, F.r11, F.r12, F.r13, F.r14, F.r15] =
        F.w.toNat + 2 ^ 64 * hsum [F.r8, F.r9, F.r10, F.r11, F.r12, F.r13, F.r14, F.r15] := rfl
    have e2 : val (fun i => a (8 * R + i)) (j + 1) =
        val (fun i => a (8 * R + i)) j + (a (8 * R + j)).toNat * 2 ^ (64 * j) := rfl
    have e3 : (2 : Nat) ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
    rw [e2, e3]
    rw [e1] at fsum
    simp only [accR] at hS
    zify at hS fsum ⊢
    linear_combination hS + (2 : ℤ) ^ (64 * j) * fsum

/-- The inner loop's trace. -/
def innerLoopTrace (ap fp : Addr) (R J : Nat) : List Leak :=
  loopTrace (fun j => innerTrace ap fp (8 * J) (8 * R + 8 * J + j + 7) (8 * R + j + 1)) 1 0 7

/-- The inner loop: the accumulator plus the row block times the column block, eight words of it stored. -/
theorem innerLoop_ok (s₁ : S) (k R J : Nat) (ap np fp : Addr) (a : Nat → BitVec 64)
    (hRJ : R < J) (hJ : 8 * J + 8 ≤ k) (ar : Arr s₁ k ap np fp)
    (hrbp : s₁.vg.gpr .rbp = wa ap (8 * J)) (hrdi : s₁.vg.gpr .rdi = wa fp (8 * R + 8 * J + 15))
    (hrsi : s₁.vg.gpr .rsi = wa ap (8 * R + 8)) (hrcx : s₁.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8))
    (hrdx : s₁.vg.gpr .rdx = a (8 * R)) (hcf : s₁.vg.cf = some false) (hof : s₁.vg.of = some false)
    (hA : ∀ i < k, s₁.vg.mem.readW (wa ap i) 64 = a i) :
    ∃ s', Exec I (.loop (.block Rind.X86_64.Sqrx8x.inner) (Rind.X86_64.Cond.vg .ne)) s₁
        (innerLoopTrace ap fp R J) s' ∧
      BInv s₁ s' k R J ap np fp a 8 := by
  have h0 : BInv s₁ s₁ k R J ap np fp a 0 :=
    ⟨by omega, Frame.refl _ _, hrcx, by simpa using hrdx, hcf, hof, fun h => absurd h (by omega),
      ⟨[], rfl, rfl, by simp [hsum, val, gsum]⟩⟩
  obtain ⟨s', hx, hI'⟩ := loop_ok (body := .block Rind.X86_64.Sqrx8x.inner) (c := Rind.X86_64.Cond.vg .ne)
    (fun j s => BInv s₁ s k R J ap np fp a j) (fun j => j < 8) (fun j => decide (j + 1 < 8))
    (fun j => innerTrace ap fp (8 * J) (8 * R + 8 * J + j + 7) (8 * R + j + 1)) 1
    (fun j s hI hj => inner_step s₁ k R J ap np fp a hRJ hJ ar hrbp hrdi hrsi hA j s hI hj)
    7 0 s₁ h0 (fun i hi => by omega) (fun i hi => by simp; omega) (by simp)
  exact ⟨s', hx, hI'⟩

end rind.x86_64.sqrx8x
