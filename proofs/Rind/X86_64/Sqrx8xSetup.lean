import Rind.X86_64.Sqrx8xOuter

/-! # bn_sqrx8x_internal's setup

`entry` points `rdi` at `t` and stores `8k` and `a`'s end in slots 1 and 2, the zeroing loop clears `t`'s first
`2k` words sixteen at a time, and `init` loads `a`'s first word and clears the carries: `PB 0`, `t` all zero. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.sqrx8x

theorem wa_end (p : Addr) (k : Nat) : p + BitVec.ofNat 64 (8 * k) * 1#64 = wa p k := by
  apply BitVec.eq_of_toNat_eq; simp only [wa, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

def entryTrace (fp : Addr) : List Leak := [.addr (wa fp 1), .addr (wa fp 2)]

set_option maxHeartbeats 4000000 in
/-- `entry`: `rdi` at `t`, `rbp` at `a`'s end, and slots 1 and 2 `8k` and `a`'s end. -/
theorem entry_ok (s : S) (k : Nat) (ap np fp : Addr) (ar : Arr s k ap np fp)
    (hrsp : s.vg.gpr .rsp = fp) (hrsi : s.vg.gpr .rsi = ap) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 (8 * k)) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.entry s = some (s', entryTrace fp) ∧
      s'.vg.mem = (s.vg.mem.writeW (wa fp 1) (BitVec.ofNat 64 (8 * k))).writeW (wa fp 2) (wa ap k) ∧
      s'.vg.gpr .rdi = wa fp 7 ∧ s'.vg.gpr .rbp = wa ap k ∧ Frame s s' [.rdi, .rbp] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  sqrx_blockx [Rind.X86_64.Sqrx8x.entry, hrsp, hrsi, hr9, wa_end, ↓BitVec.ofNat_add_ofNat, ofNat_idx]

/-- A 16-byte zero store is two 8-byte ones. -/
theorem writeW128_zero (M : Mem) (a : Addr) :
    M.writeW a (0 : BitVec 128) = (M.writeW a (0 : BitVec 64)).writeW (a + 8#64) (0 : BitVec 64) := by
  funext x
  simp only [Mem.writeW, Mem.write]
  split_ifs <;> first | rfl | (exfalso; bv_omega) | simp

/-- `t`'s even words are 16-byte aligned: they are the frame's odd words. -/
theorem wa_al (fp : Addr) (q : Nat) (al : (fp.toNat + 56) % 16 = 0)
    (h2 : q % 2 = 1) : (wa fp q).toNat % 16 = 0 := by
  simp only [wa, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

def zeroTrace (fp : Addr) (j : Nat) : List Leak :=
  [.addr (wa fp (16 * j + 7)), .addr (wa fp (16 * j + 9)), .addr (wa fp (16 * j + 11)), .addr (wa fp (16 * j + 13)),
   .addr (wa fp (16 * j + 15)), .addr (wa fp (16 * j + 17)), .addr (wa fp (16 * j + 19)),
   .addr (wa fp (16 * j + 21))]

theorem signExtend_64 : BitVec.signExtend 64 (64 : BitVec 32) = 64#64 := by decide

theorem wa_add8 (p : Addr) (q : Nat) : p + BitVec.ofNat 64 q * 8#64 + 8#64 = p + BitVec.ofNat 64 (q + 1) * 8#64 := by
  bv_omega

/-- `r9` down a step of the zeroing loop, and whether it reached zero. -/
theorem r9_step (k j : Nat) (hj : 8 * j + 8 ≤ k) :
    BitVec.ofNat 64 (8 * k - 64 * j) - 64#64 = BitVec.ofNat 64 (8 * k - 64 * (j + 1)) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

theorem r9_zf (k j : Nat) (hj : 8 * j + 8 ≤ k) (hk : k < 2 ^ 29) :
    (BitVec.ofNat 64 (8 * k - 64 * (j + 1)) == 0) = decide (8 * (j + 1) = k) := by
  by_cases h : 8 * (j + 1) = k
  · rw [show 8 * k - 64 * (j + 1) = 0 by omega]; simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h0
    have h1 : (8 * k - 64 * (j + 1)) % 2 ^ 64 = 0 := by simpa using congrArg BitVec.toNat h0
    omega

set_option maxHeartbeats 4000000 in
/-- `zero`: sixteen zero words of `t` from word `16j`, and `r9` down by 64. -/
theorem zero_ok (s : S) (k j : Nat) (ap np fp : Addr) (ar : Arr s k ap np fp) (hj : 8 * j + 8 ≤ k)
    (al : (fp.toNat + 56) % 16 = 0) (hrdi : s.vg.gpr .rdi = wa fp (16 * j + 7))
    (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 (8 * k - 64 * j)) (hx0 : s.vg.xmm .xmm0 = 0) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.zero s = some (s', zeroTrace fp j) ∧
      s'.vg.mem = wrs s.vg.mem fp (16 * j) (List.replicate 16 0) ∧
      s'.vg.gpr .rdi = wa fp (16 * j + 23) ∧ s'.vg.gpr .r9 = BitVec.ofNat 64 (8 * k - 64 * (j + 1)) ∧
      s'.vg.zf = some (decide (8 * (j + 1) = k)) ∧ Frame s s' [.rdi, .r9] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  have A : ∀ q, q % 2 = 1 → q < 2 * k + 9 → (wa fp q).toNat % 16 = 0 :=
    fun q h1 _ => wa_al fp q al h1
  clear al
  have z9 := r9_zf k j hj hk
  sqrx_blockx [Rind.X86_64.Sqrx8x.zero, hrdi, hr9, hx0, A, store128_of, xmm_setMem, signExtend_64,
    r9_step k j hj, r9_zf k j hj hk, ↓BitVec.ofNat_add_ofNat, ofNat_idx]
  simp only [writeW128_zero, wa_add8, wrs, List.replicate_succ, List.replicate_zero, Nat.add_assoc, Nat.reduceAdd]

def initTrace (ap : Addr) : List Leak := [.addr ap]

set_option maxHeartbeats 4000000 in
/-- `init`: `a`'s first word in `rdx`, `r10` to `r15` and `rbp` zero, `rdi` at `t`, and the carries clear. -/
theorem init_ok (s : S) (k : Nat) (ap np fp : Addr) (a0 : BitVec 64) (ar : Arr s k ap np fp) (hk8 : 8 ≤ k)
    (hrsi : s.vg.gpr .rsi = ap) (hrsp : s.vg.gpr .rsp = fp) (hA : s.vg.mem.readW ap 64 = a0) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.init s = some (s', initTrace ap) ∧ s'.vg.mem = s.vg.mem ∧
      s'.vg.gpr .rdx = a0 ∧ s'.vg.gpr .r10 = 0 ∧ s'.vg.gpr .r11 = 0 ∧ s'.vg.gpr .r12 = 0 ∧
      s'.vg.gpr .r13 = 0 ∧ s'.vg.gpr .r14 = 0 ∧ s'.vg.gpr .r15 = 0 ∧ s'.vg.gpr .rdi = wa fp 7 ∧
      s'.vg.gpr .rbp = 0 ∧ s'.vg.cf = some false ∧ s'.vg.of = some false ∧
      Frame s s' [.rdx, .rdi, .rbp, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  sqrx_blockx [Rind.X86_64.Sqrx8x.init, hrsi, hrsp, hA, BitVec.xor_self, ↓BitVec.ofNat_add_ofNat, ofNat_idx]

/-- A run of zero words from word `p` reads zero within it. -/
theorem tw_wrs_zero (M : Mem) (fp : Addr) (p n q : Nat) (h1 : p ≤ q) (h2 : q < p + n)
    (hfp : fp.toNat + 8 * (p + n + 7) ≤ 2 ^ 64) : tw (wrs M fp p (List.replicate n 0)) fp q = 0 := by
  induction n generalizing M p with
  | zero => omega
  | succ n ih =>
    rw [List.replicate_succ, wrs]
    by_cases h : q = p
    · subst h
      show (wrs _ fp (q + 1) _).readW (wa fp (q + 7)) 64 = 0
      rw [readW_wrs _ _ _ _ _ _ (by simp only [List.length_replicate]; omega) (by omega)
        (by simp only [List.length_replicate]; omega), readW_writeW_self]
    · exact ih _ (p + 1) (by omega) (by omega) (by omega)

theorem val_zero (f : Nat → BitVec 64) (N : Nat) (h : ∀ i < N, f i = 0) : val f N = 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    show gsum (fun i => (f i).toNat) N + (f N).toNat * 2 ^ (64 * N) = 0
    rw [show gsum (fun i => (f i).toNat) N = 0 from ih fun i hi => h i (by omega), h N (by omega)]; simp

theorem wa_zero (p : Addr) : wa p 0 = p := by simp [wa]

/-- `entry`'s stores keep what the triangle phase keeps of memory. -/
theorem mem_entry (M : Mem) (k : Nat) (ap fp : Addr) (a : Nat → BitVec 64) (hap : ap.toNat + 8 * k ≤ 2 ^ 64)
    (hfp : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 64)
    (sepA : ap.toNat + 8 * k ≤ fp.toNat ∨ fp.toNat + 8 * (2 * k + 9) ≤ ap.toNat)
    (hA : ∀ i < k, M.readW (wa ap i) 64 = a i) :
    MemOK M ((M.writeW (wa fp 1) (BitVec.ofNat 64 (8 * k))).writeW (wa fp 2) (wa ap k)) k ap fp a where
  keeps := by
    intro y h1 h2
    have e : ∀ (M' : Mem) (x : Nat) (v : BitVec 64), (x = 1 ∨ x = 2) → (M'.writeW (wa fp x) v) y = M' y := by
      intro M' x v hx; unfold Mem.writeW; apply write_other; simp only [wa] at h1 h2 ⊢
      rcases hx with rfl | rfl <;> bv_omega
    rw [e _ 2 _ (by omega), e _ 1 _ (by omega)]
  hA := fun i hi => by
    rw [readW_writeW_wa _ _ _ _ _ _ (by omega) (by omega) (by omega),
      readW_writeW_wa _ _ _ _ _ _ (by omega) (by omega) (by omega)]
    exact hA i hi
  s1 := by rw [readW_writeW_wa _ _ _ _ _ _ (by omega) (by omega) (by omega), readW_writeW_self]
  s2 := readW_writeW_self _ _ _

/-- `rd_simp` through runs of zero words. -/
macro "rz_simp" : tactic => `(tactic|
  simp (disch := ((try simp only [List.length_replicate]); iomega)) only [readW_wrs, readW_writeW_wa,
    readW_writeW_self])

/-- The zeroing loop at its iteration `j`: `t`'s words below `16j` zero, and its last two still. -/
structure ZInv (s₀ s : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (j : Nat) : Prop where
  frame : Frame s₀ s [.rdi, .rbp, .r9]
  mem : MemOK s₀.vg.mem s.vg.mem k ap fp a
  hj : 8 * j ≤ k
  rdi : s.vg.gpr .rdi = wa fp (16 * j + 7)
  r9 : s.vg.gpr .r9 = BitVec.ofNat 64 (8 * k - 64 * j)
  zero : ∀ q < 16 * j, tw s.vg.mem fp q = 0
  top : tw s.vg.mem fp (2 * k) = 0 ∧ tw s.vg.mem fp (2 * k + 1) = 0

/-- The zeroing loop's body. -/
abbrev zeroBody : Prog I := .seq (.block [.align 32]) (.block Rind.X86_64.Sqrx8x.zero)

/-- The zeroing loop: `k / 8` iterations, sixteen words of `t` each. -/
theorem zero_loop (s₀ s : S) (k : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (hk0 : k % 8 = 0) (hk8 : 8 ≤ k)
    (ar : Arr s₀ k ap np fp) (al : (fp.toNat + 56) % 16 = 0) (hx0 : s₀.vg.xmm .xmm0 = 0)
    (hZ : ZInv s₀ s k ap np fp a 0) :
    ∃ s', Exec I (.loop zeroBody (Rind.X86_64.Cond.vg .ne)) s (loopTrace (zeroTrace fp) 1 0 (k / 8 - 1)) s' ∧
      ZInv s₀ s' k ap np fp a (k / 8) := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := id ar
  obtain ⟨s', hx, hZ'⟩ := loop_ok (body := zeroBody) (c := Rind.X86_64.Cond.vg .ne)
    (fun j s => ZInv s₀ s k ap np fp a j) (fun j => 8 * j + 8 ≤ k) (fun j => decide (8 * j + 8 < k))
    (zeroTrace fp) 1 (fun j s hI hj => by
      obtain ⟨s1, x1, m1, di1, r91, zf1, F1⟩ := zero_ok s k j ap np fp (ar.frame hI.frame) hj al hI.rdi hI.r9
        (by rw [hI.frame.xmm]; exact hx0)
      have hb : execBlock I [Rind.X86_64.Instr.align 32] s = some (s, []) := rfl
      have hx : Exec I zeroBody s ([] ++ zeroTrace fp j) s1 := Exec.seq (Exec.block hb) (Exec.block x1)
      rw [List.nil_append] at hx
      refine ⟨s1, hx, ?_, ⟨hI.frame.trans (F1.mono (by decide)), ?_,
        by omega, by rw [di1, show 16 * (j + 1) + 7 = 16 * j + 23 by ring], r91, ?_, ?_⟩⟩
      · rw [eval_ne zf1]; simp only [Option.some.injEq]
        cases h : decide (8 * j + 8 < k) <;> simp_all <;> omega
      · rw [m1]; exact hI.mem.wrs hk hap hfp sepA (16 * j) _ (by simp only [List.length_replicate]; omega)
      · intro q hq
        by_cases h : q < 16 * j
        · have := hI.zero q h
          show s1.vg.mem.readW _ 64 = 0
          rw [m1]; rz_simp; exact this
        · rw [m1]; exact tw_wrs_zero _ _ _ _ _ (by omega) (by omega) (by omega)
      · have := hI.top
        constructor
        · show s1.vg.mem.readW _ 64 = 0
          rw [m1]; rz_simp; exact this.1
        · show s1.vg.mem.readW _ 64 = 0
          rw [m1]; rz_simp; exact this.2)
    (k / 8 - 1) 0 s hZ (fun i hi => by omega) (fun i hi => by simp only [decide_eq_true_eq]; omega)
    (by simp only [decide_eq_false_iff_not]; omega)
  exact ⟨s', hx, by rwa [show 0 + 1 * (k / 8 - 1 + 1) = k / 8 by omega] at hZ'⟩

/-- The setup's trace: `entry`, the zeroing loop, and `init`. -/
def setupTrace (ap fp : Addr) (k : Nat) : List Leak :=
  entryTrace fp ++ (loopTrace (zeroTrace fp) 1 0 (k / 8 - 1) ++ initTrace ap)

/-- The setup, from the routine's entry to the first row block's triangle: `t` all zero. -/
theorem setup_ok (s₀ : S) (k : Nat) (ap np fp : Addr) (a n : Nat → BitVec 64) (n0 : BitVec 64)
    (hI : InPre s₀ k ap np fp a n n0) :
    ∃ s', Exec I (.seq (.block Rind.X86_64.Sqrx8x.entry) (.seq (.loop zeroBody (Rind.X86_64.Cond.vg .ne))
        (.block Rind.X86_64.Sqrx8x.init))) s₀ (setupTrace ap fp k) s' ∧ PB s₀ s' k ap np fp a 0 := by
  have c := hI.ctx
  have hk0 := c.k0
  have hk8 := c.k8
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := id c.ar
  obtain ⟨s1, x1, m1, di1, -, F1⟩ := entry_ok s₀ k ap np fp c.ar hI.rsp hI.rsi hI.r9
  have hZ : ZInv s₀ s1 k ap np fp a 0 := by
    refine ⟨F1.mono (by decide), by rw [m1]; exact mem_entry _ k ap fp a hap hfp sepA c.hA, by omega,
      by simp only [di1, Nat.mul_zero, Nat.zero_add],
      by rw [F1.gpr .r9 (by decide), hI.r9, Nat.mul_zero, Nat.sub_zero], fun q hq => by omega, ?_, ?_⟩
    · show s1.vg.mem.readW _ 64 = 0
      rw [m1]; rd_simp; exact hI.t2k
    · show s1.vg.mem.readW _ 64 = 0
      rw [m1]; rd_simp; exact hI.t2k1
  obtain ⟨s2, x2, hZ'⟩ := zero_loop s₀ s1 k ap np fp a hk0 hk8 c.ar c.al hI.x0 hZ
  have rsi2 : s2.vg.gpr .rsi = ap := (hZ'.frame.gpr .rsi (by decide)).trans hI.rsi
  have h0 := hZ'.mem.hA 0 (by omega)
  rw [wa_zero] at h0
  obtain ⟨s3, x3, m3, dx3, r103, r113, r123, r133, r143, r153, di3, bp3, cf3, of3, F3⟩ :=
    init_ok s2 k ap np fp (a 0) (c.ar.frame hZ'.frame) hk8 rsi2 ((hZ'.frame.gpr .rsp (by decide)).trans hI.rsp) h0
  have g3 : ∀ r, r ∉ [Reg.rdx, .rdi, .rbp, .r10, .r11, .r12, .r13, .r14, .r15] → s3.vg.gpr r = s2.vg.gpr r := F3.gpr
  -- `t` is all zero
  have tz : ∀ q < 2 * k + 2, tw s3.vg.mem fp q = 0 := by
    intro q hq
    rw [m3]
    rcases (by omega : q < 16 * (k / 8) ∨ q = 2 * k ∨ q = 2 * k + 1) with h | rfl | rfl
    · exact hZ'.zero q h
    · exact hZ'.top.1
    · exact hZ'.top.2
  have r93 : s3.vg.gpr .r9 = 0 := by
    rw [g3 .r9 (by decide), hZ'.r9, show 8 * k - 64 * (k / 8) = 0 by omega]; rfl
  refine ⟨s3, Exec.seq (Exec.block x1) (Exec.seq x2 (Exec.block x3)),
    ⟨(hZ'.frame.mono (by decide)).trans (F3.mono (by decide)), by rw [m3]; exact hZ'.mem, by omega,
      by rw [g3 .rsi (by decide), rsi2, Nat.mul_zero, wa_zero], by simp only [di3, Nat.mul_zero, Nat.zero_add], bp3,
      by simp only [dx3, Nat.mul_zero], cf3, of3, fun q _ h2 => tz q h2, ?_⟩⟩
  have hv : val (tw s3.vg.mem fp) (2 * k + 2) = 0 := val_zero _ _ tz
  have ht : hsum (twl s3.vg.mem fp (16 * 0 + 1) 7) = 0 :=
    hsum_twl_zero _ _ _ _ fun i hi => tz _ (by omega)
  have hr : hsum (regs7 s3) = 0 := by
    simp only [regs7, hsum, r93, r103, r113, r123, r133, r143, r153]; rfl
  rw [hv, ht, hr]
  simp [Q]

end rind.x86_64.sqrx8x
