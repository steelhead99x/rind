import Rind.X86_64.Sqrx8xOuter
import Rind.X86_64.Sqrx8xShiftBlocks

/-! # bn_sqrx8x_internal's shift and add

After the last row block's triangle, `t` is `Q`, the products `a_i·a_j`, `i < j`; `outerBreak` stores its last
words, and the shift loop doubles `t` and adds the squares, four of `a`'s words a run, which makes `a²`. Each run's
last two words wait for the next's first instructions, and its doubled words run two ahead of its stores. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.sqrx8x

/-- The squares of `a`'s first `n` words, at their weights. -/
def sqs (a : Nat → BitVec 64) : Nat → Nat
  | 0 => 0
  | n + 1 => sqs a n + (a n).toNat * (a n).toNat * 2 ^ (128 * n)

set_option exponentiation.threshold 4096 in
theorem sqs_four (a : Nat → BitVec 64) (i : Nat) :
    sqs a (4 * i + 4) = sqs a (4 * i) + 2 ^ (64 * (8 * i)) * ((a (4 * i)).toNat * (a (4 * i)).toNat +
      (a (4 * i + 1)).toNat * (a (4 * i + 1)).toNat * 2 ^ 128 +
      (a (4 * i + 2)).toNat * (a (4 * i + 2)).toNat * 2 ^ 256 +
      (a (4 * i + 3)).toNat * (a (4 * i + 3)).toNat * 2 ^ 384) := by
  have e : ∀ c, (2 : Nat) ^ (128 * (4 * i + c)) = 2 ^ (64 * (8 * i)) * 2 ^ (128 * c) := by
    intro c; rw [← pow_add]; ring_nf
  simp only [sqs, e]; ring

set_option exponentiation.threshold 4096 in
theorem SQ_sqs (a : Nat → BitVec 64) (R : Nat) : SQ a R = sqs a (8 * R) := by
  induction R with
  | zero => rfl
  | succ R ih =>
    have h1 := sqs_four a (2 * R)
    have h2 := sqs_four a (2 * R + 1)
    rw [show 4 * (2 * R + 1) = 4 * (2 * R) + 4 by ring] at h2
    rw [show 8 * (R + 1) = 4 * (2 * R + 1) + 4 by ring, show 4 * (2 * R + 1) = 4 * (2 * R) + 4 by ring, h2, h1,
      show 4 * (2 * R) = 8 * R by ring, SQ, ih, sqb]
    have e : (2 : Nat) ^ (64 * (8 * (2 * R + 1))) = 2 ^ (64 * (16 * R)) * 2 ^ 512 := by rw [← pow_add]; ring_nf
    rw [e, show 8 * (2 * R) = 16 * R by ring]
    ring

theorem diag8_dvd (b : Nat → BitVec 64) : 2 ^ 64 ∣ diag8 b :=
  Nat.dvd_of_mod_eq_zero (by simp only [diag8]; omega)

theorem Q_dvd (a : Nat → BitVec 64) (k R : Nat) : 2 ^ 64 ∣ Q a k R := by
  induction R with
  | zero => simp [Q]
  | succ R ih =>
    simp only [Q]
    exact Nat.dvd_add (Nat.dvd_add ih (Dvd.dvd.mul_right (diag8_dvd _) _))
      (Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _)

set_option exponentiation.threshold 4096 in
/-- The last row block's products are its triangle's alone. -/
theorem Q_last (a : Nat → BitVec 64) (k R : Nat) (h : 8 * R + 8 = k) :
    Q a k (R + 1) = Q a k R + diag8 (fun i => a (8 * R + i)) * 2 ^ (64 * (16 * R)) := by
  rw [Q, show k - 8 * R - 8 = 0 by omega]; simp [val, gsum]

theorem hsum_twl_val (M : Mem) (fp : Addr) (q n : Nat) :
    hsum (twl M fp q n) = val (fun j => tw M fp (q + j)) n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [twl, hsum, ih, Nat.add_comm n 1, val_split _ 1 n]
    simp only [val, gsum, Nat.add_zero, Nat.zero_add, Nat.mul_zero, pow_zero, Nat.mul_one, Nat.add_assoc]

/-- `t`'s words to the end of stores `ws` from word `q`: those below `q`, then `ws`. -/
theorem val_wrs_top (M : Mem) (fp : Addr) (q : Nat) (ws : List (BitVec 64))
    (hfp : fp.toNat + 8 * (q + ws.length + 7) ≤ 2 ^ 64) :
    val (tw (wrs M fp q ws) fp) (q + ws.length) = val (tw M fp) q + 2 ^ (64 * q) * hsum ws := by
  have h := val_wrs M fp q (q + ws.length) ws le_rfl hfp
  have h2 := val_split (tw M fp) q ws.length
  rw [hsum_twl_val] at h
  zify at h2 ⊢
  linear_combination h + h2

set_option exponentiation.threshold 4096 in
theorem val_add9 (f : Nat → BitVec 64) (q : Nat) :
    val f (q + 9) = val f (q + 2) + 2 ^ (64 * q) * ((f (q + 2)).toNat * 2 ^ 128 + (f (q + 3)).toNat * 2 ^ 192 +
      (f (q + 4)).toNat * 2 ^ 256 + (f (q + 5)).toNat * 2 ^ 320 + (f (q + 6)).toNat * 2 ^ 384 +
      (f (q + 7)).toNat * 2 ^ 448 + (f (q + 8)).toNat * 2 ^ 512) := by
  simp only [val, gsum, Nat.mul_add, pow_add]; ring

set_option exponentiation.threshold 4096 in
theorem val_add10 (f : Nat → BitVec 64) (q : Nat) :
    val f (q + 10) = val f (q + 2) + 2 ^ (64 * q) * ((f (q + 2)).toNat * 2 ^ 128 + (f (q + 3)).toNat * 2 ^ 192 +
      (f (q + 4)).toNat * 2 ^ 256 + (f (q + 5)).toNat * 2 ^ 320 + (f (q + 6)).toNat * 2 ^ 384 +
      (f (q + 7)).toNat * 2 ^ 448 + (f (q + 8)).toNat * 2 ^ 512 + (f (q + 9)).toNat * 2 ^ 576) := by
  simp only [val, gsum, Nat.mul_add, pow_add]; ring

/-- `a`'s word `4j` as `shift` reads it, at `rsi + rcx`. -/
theorem ap_rcx (ap : Addr) (k j : Nat) (hk : k < 2 ^ 29) :
    wa ap k + BitVec.ofNat 64 (2 ^ 64 - 8 * k + 32 * j) * 1#64 = wa ap (4 * j) := by
  simp only [wa]; bv_omega

theorem rcx_step (k j : Nat) :
    BitVec.ofNat 64 (2 ^ 64 - 8 * k + 32 * j) + 32#64 = BitVec.ofNat 64 (2 ^ 64 - 8 * k + 32 * (j + 1)) := by
  rw [BitVec.ofNat_add_ofNat]; congr 1

theorem toNat_zero64 : (0 : BitVec 64).toNat = 0 := rfl

theorem rcx_zero (k j : Nat) (hj : 4 * j ≤ k) (hk : k < 2 ^ 29) :
    (BitVec.ofNat 64 (2 ^ 64 - 8 * k + 32 * j) == 0) = decide (4 * j = k) := by
  by_cases h : 4 * j = k
  · subst h; simp only [decide_true, beq_iff_eq]; apply BitVec.eq_of_toNat_eq; simp; omega
  · have h4 : 4 * j < k := by omega
    rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, toNat_zero64, Nat.mod_eq_of_lt (by omega)] at this
    omega

/-- The shift loop before its run `i`, against `t` as `outerBreak` left it, `MB`: `t`'s words from `8i` are
still `MB`'s, `r10` and `r11` its words `8i` and `8i + 1` doubled, the carries `cf` into the first and `of` into the
third, and `r12` and `r13` its next two; what is stored below, with them, is `MB`'s first `8i + 2` doubled plus
the squares of `a`'s first `4i` words. -/
structure SInv (s₀ s : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (MB : Mem) (i : Nat) : Prop where
  frame : Frame s₀ s allRegs
  mem : MemOK s₀.vg.mem s.vg.mem k ap fp a
  hi : 4 * i + 4 ≤ k
  rsi : s.vg.gpr .rsi = wa ap k
  rcx : s.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8 * k + 32 * i)
  rdi : s.vg.gpr .rdi = wa fp (8 * i + 7)
  rdx : s.vg.gpr .rdx = a (4 * i)
  r9 : s.vg.gpr .r9 = BitVec.ofNat 64 (8 * k)
  r12 : s.vg.gpr .r12 = tw MB fp (8 * i + 2)
  r13 : s.vg.gpr .r13 = tw MB fp (8 * i + 3)
  rest : ∀ q, 8 * i ≤ q → q < 2 * k + 2 → tw s.vg.mem fp q = tw MB fp q
  sum : ∃ c o : Bool, s.vg.cf = some c ∧ s.vg.of = some o ∧
    val (tw s.vg.mem fp) (8 * i) + 2 ^ (64 * (8 * i)) * ((s.vg.gpr .r10).toNat + c.toNat +
      (s.vg.gpr .r11).toNat * 2 ^ 64 + o.toNat * 2 ^ 128) = 2 * val (tw MB fp) (8 * i + 2) + sqs a (4 * i)

/-- After the last run, `i`, without `shiftNext`: its seventh word in `rax`, the eighth's addends in `rbx`, `r13`
and `cf`, and the ninth, `t`'s word `2k`, doubled in `r10`, its carry in `of`. -/
structure SLast (s₀ s : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (MB : Mem) (i : Nat) : Prop where
  frame : Frame s₀ s allRegs
  mem : MemOK s₀.vg.mem s.vg.mem k ap fp a
  hi : 8 * i + 8 = 2 * k
  rdi : s.vg.gpr .rdi = wa fp (8 * i + 7)
  r9 : s.vg.gpr .r9 = BitVec.ofNat 64 (8 * k)
  top : ∀ q, 8 * i + 6 ≤ q → q < 2 * k + 2 → tw s.vg.mem fp q = tw MB fp q
  sum : ∃ c o : Bool, s.vg.cf = some c ∧
    val (tw s.vg.mem fp) (8 * i + 6) + 2 ^ (64 * (8 * i + 6)) * ((s.vg.gpr .rax).toNat +
      ((s.vg.gpr .rbx).toNat + (s.vg.gpr .r13).toNat + c.toNat) * 2 ^ 64 +
      ((s.vg.gpr .r10).toNat + o.toNat * 2 ^ 64) * 2 ^ 128) = 2 * val (tw MB fp) (8 * i + 9) + sqs a (4 * i + 4)

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `outerBreak`, after the last row block's triangle: `t`, as it leaves it, doubled plus the squares is `a²`, its
top three words are zero, and the shift loop's invariant holds before its first run. -/
theorem break_ok (s₀ : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (hk0 : k % 8 = 0)
    (ar : Arr s₀ k ap np fp) (hrsp : s₀.vg.gpr .rsp = fp)
    (hx3 : xlo s₀ .xmm3 = BitVec.ofNat 64 (2 ^ 64 - 8 * k)) (s : S) (hO : OA s₀ s k ap np fp a (k / 8 - 1)) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.outerBreak s = some (s', outerBreakTrace ap fp (k / 8 - 1)) ∧
      SInv s₀ s' k ap np fp a s'.vg.mem 0 ∧
      2 * val (tw s'.vg.mem fp) (2 * k + 1) + sqs a k = val a k * val a k ∧
      ∀ q, 2 * k - 1 ≤ q → q < 2 * k + 2 → tw s'.vg.mem fp q = 0 := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := id ar
  have hF := hO.frame
  have arS := ar.frame hF
  have rsp := (hF.gpr .rsp (by decide)).trans hrsp
  have hR := hO.hR
  obtain ⟨R, hRk, hRe⟩ : ∃ R, 8 * R + 8 = k ∧ k / 8 - 1 = R := ⟨k / 8 - 1, by omega, rfl⟩
  rw [hRe] at hO ⊢
  obtain ⟨mc, -, hlast, hS⟩ := hO.sum
  rw [hlast hRk, Bool.toNat_false, Nat.add_zero] at hS
  have hrc : s.vg.gpr .rsi + (s.vg.xmm .xmm3).setWidth 64 * 1#64 = wa ap 0 := by
    rw [hO.rsi, hRk, hF.xmm, show (s₀.vg.xmm .xmm3).setWidth 64 = _ from hx3]
    have := ap_rcx ap k 0 hk; simp only [Nat.mul_zero, Nat.add_zero] at this
    exact this
  obtain ⟨s1, x1, o1, m1, of1, cf1, cx1, di1, dx1, r101, r91, r121, r131, e1, F1⟩ :=
    outerBreak_ok s k R ap np fp a hRk arS hO.rdi rsp hrc hO.mem.hA
  have mw : s1.vg.mem = wrs s.vg.mem fp (16 * R + 9) (regs6 s) := by
    rw [m1]; simp only [wrs, Nat.add_assoc, Nat.reduceAdd]
  have mem1 : MemOK s₀.vg.mem s1.vg.mem k ap fp a := by
    rw [mw]; exact hO.mem.wrs hk hap hfp sepA _ _ (by simp only [List.length_cons, List.length_nil]; omega)
  -- `t` as `outerBreak` leaves it is `Q` of all the row blocks
  have hz : ∀ q, 2 * k - 1 ≤ q → q < 2 * k + 2 → tw s1.vg.mem fp q = 0 := by
    intro q h1 h2
    have := hO.zero q (by omega) (by omega) h2
    show s1.vg.mem.readW _ 64 = 0
    rw [mw]; rd_simp; exact this
  have hV : val (tw s1.vg.mem fp) (2 * k + 2) = Q a k (R + 1) := by
    have W1 := val_wrs s.vg.mem fp (16 * R + 9) (2 * k + 2) (regs6 s)
      (by simp only [List.length_cons, List.length_nil]; omega) (by omega)
    rw [← mw, show (regs6 s).length = 6 from rfl,
      hsum_twl_zero _ _ _ _ fun j hj => hO.zero _ (by omega) (by omega) (by omega)] at W1
    have hq := Q_last a k R hRk
    rw [hq, ← hS]
    zify; push_cast at W1 ⊢
    linear_combination W1
  have hV1 : val (tw s1.vg.mem fp) (2 * k + 1) = val (tw s1.vg.mem fp) (2 * k + 2) := by
    show gsum _ _ = gsum _ _
    simp only [gsum, hz (2 * k + 1) (by omega) (by omega), toNat_zero64, Nat.zero_mul, Nat.add_zero]
  have ht0 : tw s1.vg.mem fp 0 = 0 := by
    have hd := Q_dvd a k (R + 1)
    rw [← hV, show 2 * k + 2 = 1 + (2 * k + 1) by ring, val_split] at hd
    have h1 : val (tw s1.vg.mem fp) 1 = (tw s1.vg.mem fp 0).toNat := by simp [val, gsum]
    rw [h1, show 64 * 1 = 64 from rfl] at hd
    have h2 := (Nat.dvd_add_left (Dvd.intro _ rfl)).mp hd
    apply BitVec.eq_of_toNat_eq
    rw [toNat_zero64]
    exact Nat.eq_zero_of_dvd_of_lt h2 (tw s1.vg.mem fp 0).isLt
  refine ⟨s1, x1, ⟨hF.trans (F1.mono (by decide)), mem1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q _ _ => rfl, ?_⟩,
    ?_, hz⟩
  · rw [F1.gpr .rsi (by decide), hO.rsi, hRk]
  · rw [cx1, hF.xmm]; simpa using hx3
  · simp only [Nat.mul_zero, Nat.zero_add]; exact di1
  · simp only [Nat.mul_zero]; exact dx1
  · rw [r91, hO.mem.s1]
  · rw [r121]; show _ = s1.vg.mem.readW _ 64; rw [mw]; rd_simp
  · rw [r131]; show _ = s1.vg.mem.readW _ 64; rw [mw]; rd_simp
  · refine ⟨false, o1, cf1, of1, ?_⟩
    have h8 : (s.vg.mem.readW (wa fp 8) 64) = tw s1.vg.mem fp 1 := by
      show _ = s1.vg.mem.readW _ 64; rw [mw]; rd_simp
    rw [h8] at e1
    have v0 : val (tw s1.vg.mem fp) (8 * 0) = 0 := by simp only [Nat.mul_zero]; rfl
    have v2 : val (tw s1.vg.mem fp) (8 * 0 + 2) = (tw s1.vg.mem fp 1).toNat * 2 ^ 64 := by
      simp only [Nat.mul_zero, Nat.zero_add]
      show gsum _ (0 + 1 + 1) = _
      simp only [gsum, ht0, toNat_zero64, Nat.zero_mul, Nat.zero_add, Nat.mul_one]
    have q0 : sqs a (4 * 0) = 0 := by simp only [Nat.mul_zero]; rfl
    rw [v0, v2, q0, r101, toNat_zero64, Nat.mul_zero, pow_zero, Nat.one_mul, Bool.toNat_false, Nat.add_zero,
      Nat.zero_add, Nat.add_zero]
    zify at e1 ⊢
    linear_combination (2 : ℤ) ^ 64 * e1
  · have hI := Q_ident a k (R + 1) (by omega)
    have hs : sqs a k = SQ a (R + 1) := by rw [SQ_sqs, show 8 * (R + 1) = k by omega]
    have hv : val a (8 * (R + 1)) = val a k := by rw [show 8 * (R + 1) = k by omega]
    rw [hv] at hI
    rw [hV1, hV, hs]
    linarith

/-- A run of the shift loop: `shift`, then `shiftNext` unless `rcx` reached zero. -/
abbrev shiftBody : Prog I :=
  .seq (.block [.align 32]) (.seq (.block Rind.X86_64.Sqrx8x.shift)
    (.ite .rcxz (.block []) (.block Rind.X86_64.Sqrx8x.shiftNext)))

/-- Run `i`'s trace. -/
def runTrace (ap fp : Addr) (k i : Nat) : List Leak :=
  [] ++ (shiftTrace ap fp i ++ if 4 * i + 4 = k then [.branch true] else .branch false :: shiftNextTrace ap fp i)

/-- The shift loop's invariant before run `j`, or after the last. -/
def SAt (s₀ s : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (MB : Mem) (j : Nat) : Prop :=
  if 4 * j < k then SInv s₀ s k ap np fp a MB j else SLast s₀ s k ap np fp a MB (j - 1)

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Run `i` of the shift loop. -/
theorem step_ok (s₀ : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (hk0 : k % 8 = 0)
    (ar : Arr s₀ k ap np fp) (MB : Mem) (i : Nat) (s : S) (hI : SInv s₀ s k ap np fp a MB i) :
    ∃ s', Exec I shiftBody s (runTrace ap fp k i) s' ∧ I.eval .rcxnz s' = some (decide (4 * i + 4 < k)) ∧
      SAt s₀ s' k ap np fp a MB (i + 1) := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := id ar
  have hF := hI.frame
  have arS := ar.frame hF
  have hi := hI.hi
  have eP6 : (2 : ℤ) ^ (64 * (8 * i + 6)) = 2 ^ (64 * (8 * i)) * 2 ^ 384 := by rw [← pow_add]; ring_nf
  have eP8 : (2 : ℤ) ^ (64 * (8 * (i + 1))) = 2 ^ (64 * (8 * i)) * 2 ^ 512 := by rw [← pow_add]; ring_nf
  have hrest : ∀ j, 4 ≤ j → j ≤ 9 → s.vg.mem.readW (wa fp (8 * i + j + 7)) 64 = tw MB fp (8 * i + j) :=
    fun j h1 h2 => hI.rest _ (by omega) (by omega)
  have h11 : s.vg.mem.readW (wa fp (8 * i + 11)) 64 = tw MB fp (8 * i + 4) := by
    rw [show 8 * i + 11 = 8 * i + 4 + 7 by ring]; exact hrest 4 (by omega) (by omega)
  have h12 : s.vg.mem.readW (wa fp (8 * i + 12)) 64 = tw MB fp (8 * i + 5) := by
    rw [show 8 * i + 12 = 8 * i + 5 + 7 by ring]; exact hrest 5 (by omega) (by omega)
  have h13 : s.vg.mem.readW (wa fp (8 * i + 13)) 64 = tw MB fp (8 * i + 6) := by
    rw [show 8 * i + 13 = 8 * i + 6 + 7 by ring]; exact hrest 6 (by omega) (by omega)
  have h14 : s.vg.mem.readW (wa fp (8 * i + 14)) 64 = tw MB fp (8 * i + 7) := by
    rw [show 8 * i + 14 = 8 * i + 7 + 7 by ring]; exact hrest 7 (by omega) (by omega)
  have h15 : s.vg.mem.readW (wa fp (8 * i + 15)) 64 = tw MB fp (8 * i + 8) := by
    rw [show 8 * i + 15 = 8 * i + 8 + 7 by ring]; exact hrest 8 (by omega) (by omega)
  have h16 : s.vg.mem.readW (wa fp (8 * i + 16)) 64 = tw MB fp (8 * i + 9) := by
    rw [show 8 * i + 16 = 8 * i + 9 + 7 by ring]; exact hrest 9 (by omega) (by omega)
  obtain ⟨c, o, hc, ho, hS⟩ := hI.sum
  have hrc : s.vg.gpr .rsi + s.vg.gpr .rcx * 1#64 = wa ap (4 * i) := by
    rw [hI.rsi, hI.rcx]; exact ap_rcx ap k i hk
  obtain ⟨s1, x1, w0, w1, w2, w3, w4, w5, c1, o1, m1, cf1, of1, cx1, dx1, r111, e1, F1⟩ :=
    shift_ok s k i ap np fp a c o hi arS hrc hI.rdi hI.rdx hc ho hI.mem.hA
  rw [h11, h12, h13, h14, h15, hI.r12, hI.r13] at e1
  rw [h16] at r111
  have mw1 : s1.vg.mem = wrs s.vg.mem fp (8 * i) [w0, w1, w2, w3, w4, w5] := by
    rw [m1]; simp only [wrs, Nat.add_assoc, Nat.reduceAdd]
  have mem1 : MemOK s₀.vg.mem s1.vg.mem k ap fp a := by
    rw [mw1]; exact hI.mem.wrs hk hap hfp sepA _ _ (by simp only [List.length_cons, List.length_nil]; omega)
  have cx1' : s1.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8 * k + 32 * (i + 1)) := by rw [cx1, hI.rcx, rcx_step]
  have zf : (s1.vg.gpr .rcx == 0) = decide (4 * (i + 1) = k) := by rw [cx1', rcx_zero k (i + 1) (by omega) hk]
  have g1 : ∀ r, r ∉ [Reg.rax, .rbx, .rcx, .rdx, .r10, .r11, .r12, .r13] → s1.vg.gpr r = s.vg.gpr r := F1.gpr
  have hal : Exec I (.block [.align 32]) s [] s := Exec.block (M := I) (is := [.align 32]) (s := s) (s' := s) (t := []) rfl
  by_cases hl : 4 * i + 4 = k
  · refine ⟨s1, ?_, ?_, ?_⟩
    · rw [show runTrace ap fp k i = [] ++ (shiftTrace ap fp i ++ [.branch true]) by simp [runTrace, hl]]
      exact Exec.seq hal (Exec.seq (Exec.block x1)
        (Exec.iteT (by show some (s1.vg.gpr .rcx == 0) = some true; rw [zf]; simp; omega) (Exec.block rfl)))
    · show some (s1.vg.gpr .rcx != 0) = _
      rw [bne, zf, decide_eq_true (show 4 * (i + 1) = k by omega), decide_eq_false (show ¬4 * i + 4 < k by omega)]
      rfl
    · simp only [SAt, show ¬4 * (i + 1) < k by omega, ↓reduceIte, show i + 1 - 1 = i by omega]
      refine ⟨hF.trans (F1.mono (by decide)), mem1, by omega, ?_, ?_, ?_, ⟨c1, o1, cf1, ?_⟩⟩
      · rw [g1 .rdi (by decide)]; exact hI.rdi
      · rw [g1 .r9 (by decide)]; exact hI.r9
      · intro q h1 h2
        rw [← hI.rest q (by omega) h2]
        show s1.vg.mem.readW _ 64 = s.vg.mem.readW _ 64
        rw [mw1]; rd_simp
      · have V1 := val_wrs_top s.vg.mem fp (8 * i) [w0, w1, w2, w3, w4, w5]
          (by simp only [List.length_cons, List.length_nil]; omega)
        rw [← mw1, show [w0, w1, w2, w3, w4, w5].length = 6 from rfl] at V1
        rw [V1, val_add9, sqs_four]
        simp only [hsum] at e1 ⊢
        zify at e1 hS ⊢
        push_cast at e1 hS ⊢
        rw [eP6]
        generalize (2 : ℤ) ^ (64 * (8 * i)) = P at *
        linear_combination P * e1 + hS
  · have hi2 : 4 * i + 8 ≤ k := by omega
    have hrc2 : s1.vg.gpr .rsi + s1.vg.gpr .rcx * 1#64 = wa ap (4 * i + 4) := by
      rw [g1 .rsi (by decide), hI.rsi, cx1', ap_rcx ap k (i + 1) hk, show 4 * (i + 1) = 4 * i + 4 by ring]
    obtain ⟨s2, x2, c2, o2, m2, cf2, of2, dx2, r122, r132, di2, eb, eo, F2⟩ :=
      shiftNext_ok s1 k i ap np fp a c1 o1 hi2 (arS.frame F1) hrc2 ((g1 .rdi (by decide)).trans hI.rdi) cf1 of1
        mem1.hA
    have g2 : ∀ r, r ∉ [Reg.rbx, .rdx, .rdi, .r11, .r12, .r13] → s2.vg.gpr r = s1.vg.gpr r := F2.gpr
    have mw2 : s2.vg.mem = wrs s.vg.mem fp (8 * i) [w0, w1, w2, w3, w4, w5, s1.vg.gpr .rax, s2.vg.gpr .rbx] := by
      rw [m2, mw1]; simp only [wrs, Nat.add_assoc, Nat.reduceAdd]
    have mem2 : MemOK s₀.vg.mem s2.vg.mem k ap fp a := by
      rw [mw2]; exact hI.mem.wrs hk hap hfp sepA _ _ (by simp only [List.length_cons, List.length_nil]; omega)
    refine ⟨s2, ?_, ?_, ?_⟩
    · rw [show runTrace ap fp k i = [] ++ (shiftTrace ap fp i ++ (.branch false :: shiftNextTrace ap fp i)) by
        simp [runTrace, hl]]
      exact Exec.seq hal (Exec.seq (Exec.block x1)
        (Exec.iteF (by show some (s1.vg.gpr .rcx == 0) = some false; rw [zf]; simp; omega) (Exec.block x2)))
    · show some (s2.vg.gpr .rcx != 0) = _
      rw [g2 .rcx (by decide), bne, zf, decide_eq_false (show ¬4 * (i + 1) = k by omega),
        decide_eq_true (show 4 * i + 4 < k by omega)]
      rfl
    · simp only [SAt, show 4 * (i + 1) < k by omega, ↓reduceIte]
      refine ⟨hF.trans ((F1.mono (by decide)).trans (F2.mono (by decide))), mem2, by omega, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ⟨c2, o2, cf2, of2, ?_⟩⟩
      · rw [g2 .rsi (by decide), g1 .rsi (by decide)]; exact hI.rsi
      · rw [g2 .rcx (by decide)]; exact cx1'
      · rw [di2, show 8 * (i + 1) + 7 = 8 * i + 15 by ring]
      · rw [dx2, show 4 * (i + 1) = 4 * i + 4 by ring]
      · rw [g2 .r9 (by decide), g1 .r9 (by decide)]; exact hI.r9
      · rw [r122, show 8 * (i + 1) + 2 = 8 * i + 10 by ring, ← hI.rest (8 * i + 10) (by omega) (by omega)]
        show _ = s.vg.mem.readW _ 64
        rw [mw1]; rd_simp
      · rw [r132, show 8 * (i + 1) + 3 = 8 * i + 11 by ring, ← hI.rest (8 * i + 11) (by omega) (by omega)]
        show _ = s.vg.mem.readW _ 64
        rw [mw1]; rd_simp
      · intro q h1 h2
        rw [← hI.rest q (by omega) h2]
        show s2.vg.mem.readW _ 64 = s.vg.mem.readW _ 64
        rw [mw2]; rd_simp
      · have V2 := val_wrs_top s.vg.mem fp (8 * i) [w0, w1, w2, w3, w4, w5, s1.vg.gpr .rax, s2.vg.gpr .rbx]
          (by simp only [List.length_cons, List.length_nil]; omega)
        rw [← mw2, show [w0, w1, w2, w3, w4, w5, s1.vg.gpr .rax, s2.vg.gpr .rbx].length = 8 from rfl,
          show 8 * i + 8 = 8 * (i + 1) by ring] at V2
        rw [V2, show 8 * (i + 1) + 2 = 8 * i + 10 by ring, val_add10, show 4 * (i + 1) = 4 * i + 4 by ring,
          sqs_four, g2 .r10 (by decide)]
        rw [r111] at eo
        simp only [hsum] at e1 ⊢
        zify at e1 hS eb eo ⊢
        push_cast at e1 hS eb eo ⊢
        rw [eP8]
        generalize (2 : ℤ) ^ (64 * (8 * i)) = P at *
        linear_combination P * e1 + hS + P * 2 ^ 448 * eb + P * 2 ^ 576 * eo

/-- The shift loop's trace: its runs. -/
def shiftLoopTrace (ap fp : Addr) (k : Nat) : List Leak := loopTrace (runTrace ap fp k) 1 0 (k / 4 - 1)

/-- The shift loop, from its first run to after its last. -/
theorem shift_loop (s₀ : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (hk0 : k % 8 = 0)
    (ar : Arr s₀ k ap np fp) (MB : Mem) (s : S) (hI : SInv s₀ s k ap np fp a MB 0) :
    ∃ s', Exec I (.loop shiftBody .rcxnz) s (shiftLoopTrace ap fp k) s' ∧ SLast s₀ s' k ap np fp a MB (k / 4 - 1) := by
  have hi := hI.hi
  have h0 : SAt s₀ s k ap np fp a MB 0 := by simp only [SAt, show 4 * 0 < k by omega, ↓reduceIte]; exact hI
  obtain ⟨s', hx, hI'⟩ := loop_ok (body := shiftBody) (c := .rcxnz) (fun j s => SAt s₀ s k ap np fp a MB j)
    (fun j => 4 * j < k) (fun j => decide (4 * j + 4 < k)) (runTrace ap fp k) 1
    (fun j s hI hj => by
      simp only [SAt, hj, ↓reduceIte] at hI
      exact step_ok s₀ k ap np fp a hk0 ar MB j s hI)
    (k / 4 - 1) 0 s h0 (fun i hi => by omega) (fun i hi => by simp only [decide_eq_true_eq]; omega)
    (by simp only [decide_eq_false_iff_not]; omega)
  refine ⟨s', hx, ?_⟩
  rw [show 0 + 1 * (k / 4 - 1 + 1) = k / 4 by omega] at hI'
  simp only [SAt, show ¬4 * (k / 4) < k by omega, ↓reduceIte] at hI'
  exact hI'

theorem read_congr (M M' : Mem) (a : Addr) (n : Nat) (h : ∀ j < n, M' (a + BitVec.ofNat 64 j) = M (a + BitVec.ofNat 64 j)) :
    M'.read a n = M.read a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.read]
    rw [ih (a + 1) (fun j hj => by
      have := h (j + 1) (by omega)
      rwa [show a + BitVec.ofNat 64 (j + 1) = a + 1 + BitVec.ofNat 64 j by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega] at this)]
    have := h 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this]

/-- A word outside slots 1 to 4 and `t` reads as it did. -/
theorem keeps_readW {M M' : Mem} {fp : Addr} {k : Nat} (h : Keeps M M' fp k) (y : Addr)
    (hy : ∀ j < 8, 32 ≤ (y + BitVec.ofNat 64 j - wa fp 1).toNat ∧
      8 * (2 * k + 2) ≤ (y + BitVec.ofNat 64 j - wa fp 7).toNat) :
    M'.readW y 64 = M.readW y 64 := by
  unfold Mem.readW
  rw [read_congr M M' y (64 / 8) (fun j hj => h _ (hy j hj).1 (hy j hj).2)]

/-- `Ctx` holds on through the routine's phases. -/
theorem Ctx.keep {s₀ s : S} {k : Nat} {ap np fp : Addr} {a n : Nat → BitVec 64} {n0 : BitVec 64}
    (hC : Ctx s₀ k ap np fp a n n0) (hF : Frame s₀ s allRegs) (hK : Keeps s₀.vg.mem s.vg.mem fp k)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) : Ctx s k ap np fp a n n0 := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := hC.ar
  refine ⟨hC.k8, hC.k0, hC.ar.frame hF, hC.al, hA, fun i hi => ?_, ?_, hC.n0, ?_, ?_⟩
  · rw [keeps_readW hK _ (fun j hj => by constructor <;> (simp only [wa]; bv_omega))]; exact hC.hN i hi
  · rw [keeps_readW hK _ (fun j hj => by constructor <;> (simp only [wa]; bv_omega))]; exact hC.s5
  · simp only [xlo, hF.xmm]; exact hC.x2
  · simp only [xlo, hF.xmm]; exact hC.x3

/-- A store to slots 1 to 4 or `t` keeps `Keeps` and `a`'s words. -/
theorem keeps_write {M₀ M : Mem} {k : Nat} {ap fp : Addr} {a : Nat → BitVec 64} (hK : Keeps M₀ M fp k)
    (hA : ∀ i < k, M.readW (wa ap i) 64 = a i)
    (hk : k < 2 ^ 29) (hap : ap.toNat + 8 * k ≤ 2 ^ 64) (hfp : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 64)
    (sepA : ap.toNat + 8 * k ≤ fp.toNat ∨ fp.toNat + 8 * (2 * k + 9) ≤ ap.toNat)
    (x : Nat) (hx : (1 ≤ x ∧ x ≤ 4) ∨ (7 ≤ x ∧ x < 2 * k + 9)) (v : BitVec 64) :
    Keeps M₀ (M.writeW (wa fp x) v) fp k ∧ ∀ i < k, (M.writeW (wa fp x) v).readW (wa ap i) 64 = a i := by
  refine ⟨fun y h1 h2 => ?_, fun i hi => ?_⟩
  · have e : (M.writeW (wa fp x) v) y = M y := by
      unfold Mem.writeW; apply write_other; simp only [wa] at h1 h2 ⊢; rcases hx with hx | hx <;> bv_omega
    rw [e]; exact hK y h1 h2
  · rw [readW_writeW_wa _ _ _ _ _ _ (by omega) (by omega) (by omega)]; exact hA i hi

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `shiftEnd`, after the last run: `t`'s `2k` words are `a²`, the carries out of its top word zero as `a²` fits,
and the reduction's entry holds. -/
theorem end_ok (s₀ : S) (k : Nat) (ap np fp : Addr) (a n : Nat → BitVec 64) (n0 : BitVec 64)
    (hC : Ctx s₀ k ap np fp a n n0) (hrsp : s₀.vg.gpr .rsp = fp) (MB : Mem)
    (hB : 2 * val (tw MB fp) (2 * k + 1) + sqs a k = val a k * val a k)
    (hz : ∀ q, 2 * k - 1 ≤ q → q < 2 * k + 2 → tw MB fp q = 0) (i : Nat) (s : S)
    (hL : SLast s₀ s k ap np fp a MB i) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.shiftEnd s = some (s', shiftEndTrace fp i) ∧
      RedPre s' k ap np fp a n n0 (val a k * val a k) ∧ Frame s₀ s' allRegs ∧
      Keeps s₀.vg.mem s'.vg.mem fp k := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := id hC.ar
  have hF := hL.frame
  have arS := hC.ar.frame hF
  have rsp := (hF.gpr .rsp (by decide)).trans hrsp
  have hi := hL.hi
  have hk8 := hC.k8
  obtain ⟨c, o, hc, hS⟩ := hL.sum
  have hx2 : (s.vg.xmm .xmm2).setWidth 64 = np := by rw [hF.xmm]; exact hC.x2
  obtain ⟨s1, x1, w, m1, ew, bp1, ax1, cf1, of1, bx1, dx1, di1, F1⟩ :=
    shiftEnd_ok s k i ap np fp c hk8 hi arS hL.rdi rsp hc hx2 hL.r9
  have mt : s1.vg.mem = ((wrs s.vg.mem fp (8 * i + 6) [s.vg.gpr .rax, w]).writeW (wa fp 1) (wa np (k - 8))).writeW
      (wa fp 2) (wa fp (8 * i + 15)) := by
    rw [m1]; simp only [wrs, Nat.add_assoc, Nat.reduceAdd]
  have memT := hL.mem.wrs hk hap hfp sepA (8 * i + 6) [s.vg.gpr .rax, w]
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨K1, A1⟩ := keeps_write memT.keeps memT.hA hk hap hfp sepA 1 (by omega) (wa np (k - 8))
  obtain ⟨K2, A2⟩ := keeps_write K1 A1 hk hap hfp sepA 2 (by omega) (wa fp (8 * i + 15))
  rw [← mt] at K2 A2
  have hF1 : Frame s₀ s1 allRegs := hF.trans (F1.mono (by decide))
  have ht : ∀ q, 8 * i + 8 ≤ q → q < 2 * k + 2 → tw s1.vg.mem fp q = 0 := by
    intro q h1 h2
    rw [← hz q (by omega) h2, ← hL.top q (by omega) h2]
    show s1.vg.mem.readW _ 64 = s.vg.mem.readW _ 64
    rw [mt]; rd_simp
  refine ⟨s1, x1, ⟨Ctx.keep hC hF1 K2 A2, (hF1.gpr .rsp (by decide)).trans hrsp, di1, bp1, ?_, ?_, ax1, cf1, of1,
    ?_, ?_, ?_, ht (2 * k) (by omega) (by omega), ht (2 * k + 1) (by omega) (by omega)⟩, hF1, K2⟩
  · rw [bx1, keeps_readW hL.mem.keeps _ (fun j hj => by constructor <;> (simp only [wa]; bv_omega))]; exact hC.s5
  · rw [dx1]; show _ = s1.vg.mem.readW (wa fp (0 + 7)) 64
    rw [Nat.zero_add, mt]; rd_simp
  · rw [mt]; rd_simp
  · rw [mt, readW_writeW_self, show 8 * i + 15 = 2 * k + 7 by omega]
  · -- `t`'s value
    have V := val_wrs_top s.vg.mem fp (8 * i + 6) [s.vg.gpr .rax, w]
      (by simp only [List.length_cons, List.length_nil]; omega)
    rw [show [s.vg.gpr .rax, w].length = 2 from rfl, show 8 * i + 6 + 2 = 2 * k by omega] at V
    have V1 : val (tw s1.vg.mem fp) (2 * k) = val (tw (wrs s.vg.mem fp (8 * i + 6) [s.vg.gpr .rax, w]) fp) (2 * k) := by
      rw [mt, val_slot _ _ _ _ _ (by omega) (by omega), val_slot _ _ _ _ _ (by omega) (by omega)]
    rw [show 8 * i + 9 = 2 * k + 1 by omega, show 4 * i + 4 = k by omega, hB] at hS
    have hlt : val a k * val a k < 2 ^ (64 * (2 * k)) := by
      have h := val_lt a k
      calc val a k * val a k < 2 ^ (64 * k) * 2 ^ (64 * k) := Nat.mul_lt_mul'' h h
        _ = 2 ^ (64 * (2 * k)) := by rw [← pow_add]; ring_nf
    have e6 : (2 : Nat) ^ (64 * (2 * k)) = 2 ^ (64 * (8 * i + 6)) * 2 ^ 128 := by
      rw [← pow_add]; congr 1; omega
    have key : val (tw s1.vg.mem fp) (2 * k) + 2 ^ (64 * (2 * k)) *
        ((adcC (s.vg.gpr .rbx) (s.vg.gpr .r13) c).toNat + (s.vg.gpr .r10).toNat + o.toNat * 2 ^ 64) =
        val a k * val a k := by
      rw [V1, V, e6, ← hS]
      simp only [hsum]
      zify at ew ⊢
      linear_combination 2 ^ (64 * (8 * i + 6)) * 2 ^ 64 * ew
    rcases Nat.eq_zero_or_pos ((adcC (s.vg.gpr .rbx) (s.vg.gpr .r13) c).toNat + (s.vg.gpr .r10).toNat +
      o.toNat * 2 ^ 64) with h0 | h0
    · rw [h0, Nat.mul_zero, Nat.add_zero] at key; exact key
    · exfalso
      have := Nat.le_mul_of_pos_right (2 ^ (64 * (2 * k))) h0
      omega

/-- The shift and add's trace: `outerBreak`, the loop, and `shiftEnd`. -/
def shiftPhaseTrace (ap fp : Addr) (k : Nat) : List Leak :=
  outerBreakTrace ap fp (k / 8 - 1) ++ (shiftLoopTrace ap fp k ++ shiftEndTrace fp (k / 4 - 1))

/-- From the last row block's triangle to the reduction's entry, with `t` `a²`. -/
theorem shiftPhase_ok (s₀ : S) (k : Nat) (ap np fp : Addr) (a n : Nat → BitVec 64) (n0 : BitVec 64)
    (hC : Ctx s₀ k ap np fp a n n0) (hrsp : s₀.vg.gpr .rsp = fp) (s : S) (hO : OA s₀ s k ap np fp a (k / 8 - 1)) :
    ∃ s', Exec I (.seq (.block Rind.X86_64.Sqrx8x.outerBreak) (.seq (.loop shiftBody .rcxnz)
        (.block Rind.X86_64.Sqrx8x.shiftEnd))) s (shiftPhaseTrace ap fp k) s' ∧
      RedPre s' k ap np fp a n n0 (val a k * val a k) ∧ Frame s₀ s' allRegs ∧ Keeps s₀.vg.mem s'.vg.mem fp k := by
  obtain ⟨s1, x1, hI, hB, hz⟩ := break_ok s₀ k ap np fp a hC.k0 hC.ar hrsp hC.x3 s hO
  obtain ⟨s2, x2, hL⟩ := shift_loop s₀ k ap np fp a hC.k0 hC.ar s1.vg.mem s1 hI
  obtain ⟨s3, x3, hR, hF, hK⟩ := end_ok s₀ k ap np fp a n n0 hC hrsp s1.vg.mem hB hz (k / 4 - 1) s2 hL
  exact ⟨s3, Exec.seq (Exec.block x1) (Exec.seq x2 (Exec.block x3)), hR, hF, hK⟩

end rind.x86_64.sqrx8x
