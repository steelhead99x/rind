import Rind.X86_64.Mul4xAsm

/-! # bn_mul4x_mont's loops

The facts that carry a pass's memory from block to block, and the first pass, `body0`, its loop
of `first`, and `firstTail`. -/

open VG VG.X86_64 Rind.X86_64.Mul4x rind.x86_64.asm

set_option linter.unusedSimpArgs false

namespace rind.x86_64.mul4x

theorem Arrays.frame {s s' : S} {k : Nat} {ap bp np n0p tp : Addr} {gs : List Reg}
    (ar : Arrays s k ap bp np n0p tp) (h : Frame s s' gs) : Arrays s' k ap bp np n0p tp := by
  obtain ⟨hk, hap, hbp, hnp, hn0p, htp, sepA, sepB, sepN, sepN0, rA, rB, rN, rN0, LT, hLT, rT⟩ := ar
  rw [← h.rd, ← h.wr] at rA rB rN rN0
  rw [← h.wr] at rT
  exact ⟨hk, hap, hbp, hnp, hn0p, htp, sepA, sepB, sepN, sepN0, rA, rB, rN, rN0, LT, hLT, rT⟩

/-! ## Memory -/

/-- `M` matches `M0` from word `j` of `tp` on, round through every byte outside `tp`'s words. -/
def Agree (M0 M : Mem) (tp : Addr) (j : Nat) : Prop := ∀ y, 8 * j ≤ (y - tp).toNat → M y = M0 y

theorem Agree.refl (M : Mem) (tp : Addr) (j : Nat) : Agree M M tp j := fun _ _ => rfl

theorem Agree.trans {M₀ M₁ M₂ : Mem} {tp : Addr} {j j' : Nat} (h₁ : Agree M₀ M₁ tp j)
    (h₂ : Agree M₁ M₂ tp j') (hj : j ≤ j') : Agree M₀ M₂ tp j' :=
  fun y hy => (h₂ y hy).trans (h₁ y (by omega))

theorem Agree.mono {M₀ M : Mem} {tp : Addr} {j j' : Nat} (h : Agree M₀ M tp j) (hj : j ≤ j') :
    Agree M₀ M tp j' :=
  fun y hy => h y (by omega)

theorem wa_toNat {p : Addr} {k i : Nat} (hp : p.toNat + 8 * k ≤ 2 ^ 64) (hi : i < k) :
    (wa p i).toNat = p.toNat + 8 * i := by
  simp only [wa]; bv_omega

theorem Agree.writeW {M₀ M : Mem} {tp : Addr} {j : Nat} (v : BitVec 64) (h : Agree M₀ M tp j) :
    Agree M₀ (M.writeW (wa tp j) v) tp (j + 1) := by
  intro y hy
  have := (y - tp).isLt
  have e : (M.writeW (wa tp j) v) y = M y := by
    unfold Mem.writeW; apply write_other; simp only [wa]; bv_omega
  rw [e]; exact h y (by omega)

/-- A write below word `j` of `tp` keeps `Agree` at `j`. -/
theorem Agree.writeW_below {M₀ M : Mem} {tp : Addr} {i j : Nat} (v : BitVec 64) (h : Agree M₀ M tp j)
    (hi : i + 1 ≤ j) : Agree M₀ (M.writeW (wa tp i) v) tp j := by
  intro y hy
  have := (y - tp).isLt
  have e : (M.writeW (wa tp i) v) y = M y := by
    unfold Mem.writeW; apply write_other; simp only [wa]; bv_omega
  rw [e]; exact h y hy

theorem wa_zero (p : Addr) : wa p 0 = p := by simp [wa]

theorem readW_agree {M₀ M : Mem} {tp x : Addr} {j : Nat} (h : Agree M₀ M tp j)
    (hx : ∀ b < 8, 8 * j ≤ (x + BitVec.ofNat 64 b - tp).toNat) : M.readW x 64 = M₀.readW x 64 := by
  simp only [Mem.readW]; congr 1; apply read_congr; intro b hb; exact h _ (hx b (by omega))

/-- A word of `tp` at or past `j` keeps its value. -/
theorem Agree.tp {M₀ M : Mem} {tp : Addr} {j i k : Nat} (h : Agree M₀ M tp j) (hji : j ≤ i)
    (hi : i < k + 3) (htp : tp.toNat + 8 * (k + 3) ≤ 2 ^ 64) :
    M.readW (wa tp i) 64 = M₀.readW (wa tp i) 64 :=
  readW_agree h fun b hb => by simp only [wa]; bv_omega

/-- A word of an array apart from `tp` keeps its value. -/
theorem Agree.arr {M₀ M : Mem} {tp p : Addr} {j i k : Nat} (h : Agree M₀ M tp j) (hj : j ≤ k + 3)
    (htp : tp.toNat + 8 * (k + 3) ≤ 2 ^ 64) (hp : p.toNat + 8 * k ≤ 2 ^ 64)
    (sep : p.toNat + 8 * k ≤ tp.toNat ∨ tp.toNat + 8 * (k + 3) ≤ p.toNat) (hi : i < k) :
    M.readW (wa p i) 64 = M₀.readW (wa p i) 64 :=
  readW_agree h fun b hb => by simp only [wa]; bv_omega

/-- A word apart from `tp` keeps its value. -/
theorem Agree.word {M₀ M : Mem} {tp p : Addr} {j k : Nat} (h : Agree M₀ M tp j) (hj : j ≤ k + 3)
    (htp : tp.toNat + 8 * (k + 3) ≤ 2 ^ 64) (hp : p.toNat + 8 ≤ 2 ^ 64)
    (sep : p.toNat + 8 ≤ tp.toNat ∨ tp.toNat + 8 * (k + 3) ≤ p.toNat) :
    M.readW p 64 = M₀.readW p 64 :=
  readW_agree h fun b hb => by bv_omega

theorem readW_tp_ne {M : Mem} {tp : Addr} {i j k : Nat} (v : BitVec 64) (htp : tp.toNat + 8 * (k + 3) ≤ 2 ^ 64)
    (hi : i < k + 3) (hj : j < k + 3) (hne : i ≠ j) :
    (M.writeW (wa tp j) v).readW (wa tp i) 64 = M.readW (wa tp i) 64 :=
  readW_writeW_sep _ _ _ _ (by unfold Apart; simp only [wa]; constructor <;> bv_omega)

/-! ## The first pass -/

/-- The first pass's word chain, for `b[0]` and `q`. -/
abbrev f0 (a n : Nat → BitVec 64) (b q : BitVec 64) : Nat → C → BitVec 64 × C :=
  fun m c => step0 (a (m + 1)) (n (m + 1)) b q c

/-- A pass's loop from word `j` of the chain `f`: the carries in, the words stored below `j`, and
memory from `j` on as it was. -/
structure ChainInv (s₀ s : S) (tp : Addr) (a : Nat → BitVec 64) (f : Nat → C → BitVec 64 × C)
    (c₀ : C) (j : Nat) : Prop where
  j1 : 1 ≤ j
  frame : Frame s₀ s [.rax, .rdx, .rdi, .r10, .r11, .r13, .r15]
  r15 : s.vg.gpr .r15 = BitVec.ofNat 64 (j + 3)
  r10 : s.vg.gpr .r10 = (carries f c₀ j).1
  r13 : s.vg.gpr .r13 = (carries f c₀ j).2
  rax : s.vg.gpr .rax = a (j + 1)
  agree : Agree s₀.vg.mem s.vg.mem tp j
  words : ∀ i < j, s.vg.mem.readW (wa tp i) 64 = stored f c₀ i

/-- Four more words of the chain keep `ChainInv`. -/
theorem ChainInv.next {s₀ s s' : S} {tp : Addr} {a : Nat → BitVec 64} {f : Nat → C → BitVec 64 × C} {c₀ : C}
    {j k : Nat} (hI : ChainInv s₀ s tp a f c₀ j) (htp : tp.toNat + 8 * (k + 3) ≤ 2 ^ 64) (hj : j + 4 ≤ k + 3)
    (hF : Frame s s' [.rax, .rdx, .rdi, .r10, .r11, .r13, .r15])
    (o15 : s'.vg.gpr .r15 = BitVec.ofNat 64 (j + 7))
    (o10 : s'.vg.gpr .r10 = (carries f c₀ (j + 4)).1) (o13 : s'.vg.gpr .r13 = (carries f c₀ (j + 4)).2)
    (oax : s'.vg.gpr .rax = a (j + 5))
    (omem : s'.vg.mem = (((s.vg.mem.writeW (wa tp j) (stored f c₀ j)).writeW (wa tp (j + 1)) (stored f c₀ (j + 1))).writeW
        (wa tp (j + 2)) (stored f c₀ (j + 2))).writeW (wa tp (j + 3)) (stored f c₀ (j + 3))) :
    ChainInv s₀ s' tp a f c₀ (j + 4) := by
  obtain ⟨hj1, hF₀, _, _, _, _, hag, hst⟩ := hI
  have hag' : Agree s.vg.mem s'.vg.mem tp (j + 4) := by
    rw [omem]
    exact (((Agree.refl _ tp j).writeW _).writeW _ |>.writeW _).writeW _
  refine ⟨by omega, hF₀.trans hF, o15, o10, o13, oax, hag.trans hag' (by omega), ?_⟩
  intro i hi
  rw [omem]
  rcases (by omega : i < j ∨ i = j ∨ i = j + 1 ∨ i = j + 2 ∨ i = j + 3) with h | rfl | rfl | rfl | rfl
  · rw [readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega),
      readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega)]
    exact hst i h
  · rw [readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega),
      readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_writeW_self]
  · rw [readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega),
      readW_writeW_self]
  · rw [readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_writeW_self]
  · rw [readW_writeW_self]

theorem first_step (s₀ : S) (k : Nat) (ap bp np n0p tp b q : BitVec 64) (a n : Nat → BitVec 64) (c₀ : C)
    (ar : Arrays s₀ k ap bp np n0p tp)
    (hrsi : s₀.vg.gpr .rsi = ap) (hrcx : s₀.vg.gpr .rcx = np) (hrsp : s₀.vg.gpr .rsp = tp)
    (hrbx : s₀.vg.gpr .rbx = b) (hrbp : s₀.vg.gpr .rbp = q) (hr9 : s₀.vg.gpr .r9 = BitVec.ofNat 64 k)
    (hA : ∀ i < k, s₀.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s₀.vg.mem.readW (wa np i) 64 = n i)
    (j : Nat) (s : S) (hI : ChainInv s₀ s tp a (f0 a n b q) c₀ j) (hR : j + 7 ≤ k) :
    ∃ s', Exec I (.block first) s (firstTrace ap np tp j) s' ∧
      I.eval (Rind.X86_64.Cond.vg .b) s' = some (decide (j + 7 < k)) ∧ ChainInv s₀ s' tp a (f0 a n b q) c₀ (j + 4) := by
  have hF := hI.frame
  have ar' := ar.frame hF
  have htp := ar.htp
  obtain ⟨s', hx, o10, o13, oax, o15, ocf, omem, oF⟩ :=
    first_ok s j k ap bp np n0p tp b q _ _ a n hI.j1 hR ar'
      ((hF.gpr .rsi (by decide)).trans hrsi) ((hF.gpr .rcx (by decide)).trans hrcx)
      ((hF.gpr .rsp (by decide)).trans hrsp) hI.r15 ((hF.gpr .rbx (by decide)).trans hrbx)
      ((hF.gpr .rbp (by decide)).trans hrbp) hI.r10 hI.r13 hI.rax ((hF.gpr .r9 (by decide)).trans hr9)
      (fun i hi => (hI.agree.arr (by omega) htp ar.hap ar.sepA hi).trans (hA i hi))
      (fun i hi => (hI.agree.arr (by omega) htp ar.hnp ar.sepN hi).trans (hN i hi))
  exact ⟨s', Exec.block hx, by simpa [Rind.X86_64.isa, Rind.X86_64.eval, VG.X86_64.eval] using ocf,
    hI.next htp (by omega) oF o15 o10 o13 oax omem⟩

/-- An outer pass's word chain, for `b[i]`, `q`, and the words `t` the last pass left. -/
abbrev f1 (a n t : Nat → BitVec 64) (b q : BitVec 64) : Nat → C → BitVec 64 × C :=
  fun m c => step (a (m + 1)) (n (m + 1)) (t (m + 1)) b q c

theorem inner_step (s₀ : S) (k : Nat) (ap bp np n0p tp b q : BitVec 64) (a n t : Nat → BitVec 64) (c₀ : C)
    (ar : Arrays s₀ k ap bp np n0p tp)
    (hrsi : s₀.vg.gpr .rsi = ap) (hrcx : s₀.vg.gpr .rcx = np) (hrsp : s₀.vg.gpr .rsp = tp)
    (hrbx : s₀.vg.gpr .rbx = b) (hrbp : s₀.vg.gpr .rbp = q) (hr9 : s₀.vg.gpr .r9 = BitVec.ofNat 64 k)
    (hA : ∀ i < k, s₀.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s₀.vg.mem.readW (wa np i) 64 = n i)
    (hT : ∀ i, 1 ≤ i → i ≤ k → s₀.vg.mem.readW (wa tp i) 64 = t i)
    (j : Nat) (s : S) (hI : ChainInv s₀ s tp a (f1 a n t b q) c₀ j) (hR : j + 7 ≤ k) :
    ∃ s', Exec I (.block Rind.X86_64.Mul4x.inner) s (innerTrace ap np tp j) s' ∧
      I.eval (Rind.X86_64.Cond.vg .b) s' = some (decide (j + 7 < k)) ∧
      ChainInv s₀ s' tp a (f1 a n t b q) c₀ (j + 4) := by
  have hF := hI.frame
  have ar' := ar.frame hF
  have htp := ar.htp
  obtain ⟨s', hx, o10, o13, oax, o15, ocf, omem, oF⟩ :=
    inner_ok s j k ap bp np n0p tp b q _ _ a n t hI.j1 hR ar'
      ((hF.gpr .rsi (by decide)).trans hrsi) ((hF.gpr .rcx (by decide)).trans hrcx)
      ((hF.gpr .rsp (by decide)).trans hrsp) hI.r15 ((hF.gpr .rbx (by decide)).trans hrbx)
      ((hF.gpr .rbp (by decide)).trans hrbp) hI.r10 hI.r13 hI.rax ((hF.gpr .r9 (by decide)).trans hr9)
      (fun i hi => (hI.agree.arr (by omega) htp ar.hap ar.sepA hi).trans (hA i hi))
      (fun i hi => (hI.agree.arr (by omega) htp ar.hnp ar.sepN hi).trans (hN i hi))
      (fun i h1 h2 => (hI.agree.tp (k := k) (by omega) (by omega) htp).trans (hT i (by omega) (by omega)))
  exact ⟨s', Exec.block hx, by simpa [Rind.X86_64.isa, Rind.X86_64.eval, VG.X86_64.eval] using ocf,
    hI.next htp (by omega) oF o15 o10 o13 oax omem⟩

theorem writeW_wa_zero (M : Mem) (tp : Addr) (v : BitVec 64) : M.writeW tp v = M.writeW (wa tp 0) v := by
  rw [wa_zero]

set_option maxHeartbeats 1000000 in
/-- The first pass: `body0`, its loop of `first`, and `firstTail` leave `passOut0`'s words in `tp[0..k]`. -/
theorem pass0_ok (s : S) (k : Nat) (ap bp np n0p tp rp x n0' : BitVec 64) (a bw n : Nat → BitVec 64)
    (hk8 : 8 ≤ k) (hk4 : k % 4 = 0) (ar : Arrays s k ap bp np n0p tp)
    (hrsi : s.vg.gpr .rsi = ap) (hrdx : s.vg.gpr .rdx = bp) (hrcx : s.vg.gpr .rcx = np)
    (hr8 : s.vg.gpr .r8 = n0p) (hrsp : s.vg.gpr .rsp = tp) (hrdi : s.vg.gpr .rdi = rp)
    (hrax : s.vg.gpr .rax = x) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 k)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hB : ∀ i < k, s.vg.mem.readW (wa bp i) 64 = bw i) (hn0 : s.vg.mem.readW n0p 64 = n0') :
    let A0 := (mulLo (a 0) (bw 0), mulHi (a 0) (bw 0))
    let q := n0' * A0.1
    let N0 := mac (n 0) q A0.1
    ∃ s₁ s₂ s₃, Exec I (.block body0) s (body0Trace ap bp np n0p tp k) s₁ ∧
      Exec I (.loop (.block first) (Rind.X86_64.Cond.vg .b)) s₁ (loopTrace (firstTrace ap np tp) 4 1 ((k - 8) / 4)) s₂ ∧
      Exec I (.block firstTail) s₂ (firstTailTrace ap np tp (k - 3)) s₃ ∧
      s₃.vg.gpr .rax = a 0 ∧ s₃.vg.gpr .r14 = BitVec.ofNat 64 1 ∧ s₃.vg.gpr .r12 = bp ∧ s₃.vg.gpr .r8 = n0' ∧
      (∀ i ≤ k, s₃.vg.mem.readW (wa tp i) 64 = passOut0 (f0 a n (bw 0) q) (A0.2, N0.2) k i) ∧
      s₃.vg.mem.readW (wa tp (k + 1)) 64 = x ∧ s₃.vg.mem.readW (wa tp (k + 2)) 64 = rp ∧
      Agree s.vg.mem s₃.vg.mem tp (k + 3) ∧
      Frame s s₃ [.rax, .rdx, .rdi, .rbx, .rbp, .r8, .r10, .r11, .r12, .r13, .r14, .r15] := by
  intro A0 q N0
  have htp := ar.htp
  have hA0 : s.vg.mem.readW ap 64 = a 0 := by have := hA 0 (by omega); rwa [wa_zero] at this
  have hN0 : s.vg.mem.readW np 64 = n 0 := by have := hN 0 (by omega); rwa [wa_zero] at this
  have hB0 : s.vg.mem.readW bp 64 = bw 0 := by have := hB 0 (by omega); rwa [wa_zero] at this
  obtain ⟨s₁, hx1, p10, p13, pax, p15, p14, pbx, pbp, p12, p8, pmem, pF⟩ :=
    body0_ok s k ap bp np n0p tp rp x n0' a bw n hk8 ar hrsi hrdx hrcx hr8 hrsp hrdi hrax hr9 hA hN hA0 hN0 hB0 hn0
  rw [writeW_wa_zero] at pmem
  have ag1 : Agree s.vg.mem s₁.vg.mem tp (k + 3) := by
    rw [pmem]
    exact (((Agree.refl _ tp _).writeW_below _ (by omega)).writeW_below _ (by omega)).writeW_below _ (by omega)
  have ar1 := ar.frame pF
  -- The loop of `first`.
  let f := f0 a n (bw 0) q
  let c₀ : C := (A0.2, N0.2)
  have hI1 : ChainInv s₁ s₁ tp a f c₀ 1 := by
    refine ⟨le_refl _, Frame.refl _ _, p15, p10, p13, pax, Agree.refl _ _ _, ?_⟩
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [pmem, readW_writeW_self]; rfl
  have g1 : ∀ r, r ∉ [Reg.rax, .rdx, .rdi, .rbx, .rbp, .r8, .r10, .r11, .r12, .r13, .r14, .r15] →
      s₁.vg.gpr r = s.vg.gpr r := pF.gpr
  obtain ⟨s₂, hx2, hI2⟩ := loop_ok (body := .block first) (c := Rind.X86_64.Cond.vg .b)
    (fun j s => ChainInv s₁ s tp a f c₀ j) (fun j => j + 7 ≤ k) (fun j => decide (j + 7 < k))
    (firstTrace ap np tp) 4
    (fun j s' hI hR => first_step s₁ k ap bp np n0p tp (bw 0) q a n c₀ ar1
      ((g1 .rsi (by decide)).trans hrsi) ((g1 .rcx (by decide)).trans hrcx) ((g1 .rsp (by decide)).trans hrsp)
      pbx pbp ((g1 .r9 (by decide)).trans hr9)
      (fun i hi => (ag1.arr (by omega) htp ar.hap ar.sepA hi).trans (hA i hi))
      (fun i hi => (ag1.arr (by omega) htp ar.hnp ar.sepN hi).trans (hN i hi)) j s' hI hR)
    ((k - 8) / 4) 1 s₁ hI1 (fun i hi => by omega) (fun i hi => by simp; omega) (by simp; omega)
  rw [show 1 + 4 * ((k - 8) / 4 + 1) = k - 3 by omega] at hI2
  have ag2 : Agree s.vg.mem s₂.vg.mem tp (k + 3) := ag1.trans (hI2.agree.mono (by omega)) (le_refl _)
  have F2 := hI2.frame
  have ar2 := ar1.frame F2
  -- `firstTail`.
  obtain ⟨s₃, hx3, oax, o14, omem, oF⟩ :=
    firstTail_ok s₂ (k - 3) k 0 ap bp np n0p tp (bw 0) q _ _ a n (by omega) (by omega) ar2
      ((F2.gpr .rsi (by decide)).trans ((g1 .rsi (by decide)).trans hrsi))
      ((F2.gpr .rcx (by decide)).trans ((g1 .rcx (by decide)).trans hrcx))
      ((F2.gpr .rsp (by decide)).trans ((g1 .rsp (by decide)).trans hrsp))
      hI2.r15 ((F2.gpr .rbx (by decide)).trans pbx) ((F2.gpr .rbp (by decide)).trans pbp)
      hI2.r10 hI2.r13 hI2.rax ((F2.gpr .r14 (by decide)).trans (p14.trans rfl))
      (fun i hi => (ag2.arr (le_refl _) htp ar.hap ar.sepA hi).trans (hA i hi))
      (fun i hi => (ag2.arr (le_refl _) htp ar.hnp ar.sepN hi).trans (hN i hi))
      (by have := (ag2.arr (le_refl _) htp ar.hap ar.sepA (i := 0) (by omega)).trans (hA 0 (by omega))
          rwa [wa_zero] at this)
  have ag3 : Agree s₂.vg.mem s₃.vg.mem tp (k + 3) := by
    rw [omem]
    exact ((((Agree.refl _ tp _).writeW_below _ (by omega)).writeW_below _ (by omega)).writeW_below _
      (by omega)).writeW_below _ (by omega)
  refine ⟨s₁, s₂, s₃, Exec.block hx1, hx2, Exec.block hx3, oax, o14, ?_, ?_, ?_, ?_, ?_,
    ag2.trans ag3 (le_refl _), pF.trans ((F2.mono (by decide)).trans (oF.mono (by decide)))⟩
  · exact (oF.gpr .r12 (by decide)).trans ((F2.gpr .r12 (by decide)).trans p12)
  · exact (oF.gpr .r8 (by decide)).trans ((F2.gpr .r8 (by decide)).trans p8)
  · intro i hi
    rw [omem]
    rcases (by omega : i < k - 3 ∨ i = k - 3 ∨ i = k - 3 + 1 ∨ i = k - 3 + 2 ∨ i = k - 3 + 3) with
      h | rfl | rfl | rfl | rfl
    · rw [readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega),
        readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega),
        hI2.words i h]
      simp only [passOut0, show i + 1 < k by omega, ↓reduceIte]; rfl
    · rw [readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega),
        readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_writeW_self]
      simp only [passOut0, show k - 3 + 1 < k by omega, ↓reduceIte]; rfl
    · rw [readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega),
        readW_writeW_self]
      simp only [passOut0, show k - 3 + 1 + 1 < k by omega, ↓reduceIte]; rfl
    · rw [readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_writeW_self]
      simp only [passOut0, show ¬ k - 3 + 2 + 1 < k by omega, show k - 3 + 2 + 1 = k by omega, Nat.lt_irrefl,
        show k - 1 = k - 3 + 1 + 1 by omega, ↓reduceIte]; rfl
    · rw [readW_writeW_self]
      simp only [passOut0, show ¬ k - 3 + 3 + 1 < k by omega, show ¬ k - 3 + 3 + 1 = k by omega,
        show k - 1 = k - 3 + 1 + 1 by omega, ↓reduceIte]; rfl
  · rw [omem, readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega),
      readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega),
      hI2.agree.tp (k := k) (by omega) (by omega) htp, pmem, readW_tp_ne _ htp (by omega) (by omega) (by omega),
      readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_writeW_self]
  · rw [omem, readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega),
      readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega),
      hI2.agree.tp (k := k) (by omega) (by omega) htp, pmem, readW_tp_ne _ htp (by omega) (by omega) (by omega),
      readW_writeW_self]

/-- An outer pass's trace. -/
def passTrace (ap bp np tp : Addr) (k i : Nat) : List Leak :=
  outerHeadTrace ap bp np tp i ++
    (loopTrace (innerTrace ap np tp) 4 1 ((k - 8) / 4) ++ outerTailTrace ap np tp (k - 3) k)

/-- An outer pass's program. -/
abbrev passProg : Prog I :=
  .seq (.block outerHead) (.seq (.loop (.block Rind.X86_64.Mul4x.inner) (Rind.X86_64.Cond.vg .b)) (.block outerTail))

set_option maxHeartbeats 1000000 in
/-- Outer pass `i`: `outerHead`, its loop of `inner`, and `outerTail` leave `passOut`'s words in `tp[0..k]`. -/
theorem pass_ok (s : S) (k i : Nat) (ap bp np n0p tp n0' : BitVec 64) (a bw n t : Nat → BitVec 64)
    (hk8 : 8 ≤ k) (hk4 : k % 4 = 0) (hi : i < k) (ar : Arrays s k ap bp np n0p tp)
    (hrsi : s.vg.gpr .rsi = ap) (hrcx : s.vg.gpr .rcx = np) (hrsp : s.vg.gpr .rsp = tp)
    (hr12 : s.vg.gpr .r12 = bp) (hr8 : s.vg.gpr .r8 = n0') (hrax : s.vg.gpr .rax = a 0)
    (hr14 : s.vg.gpr .r14 = BitVec.ofNat 64 i) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 k)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i)
    (hB : ∀ i < k, s.vg.mem.readW (wa bp i) 64 = bw i)
    (hT : ∀ j ≤ k, s.vg.mem.readW (wa tp j) 64 = t j) :
    let A0 := mac (a 0) (bw i) (t 0)
    let q := n0' * A0.1
    let N0 := mac (n 0) q A0.1
    ∃ s', Exec I passProg s (passTrace ap bp np tp k i) s' ∧
      s'.vg.gpr .rax = a 0 ∧ s'.vg.gpr .r14 = BitVec.ofNat 64 (i + 1) ∧
      s'.vg.cf = some (decide (i + 1 < k)) ∧
      (∀ j ≤ k, s'.vg.mem.readW (wa tp j) 64 = passOut (f1 a n t (bw i) q) (A0.2, N0.2) k (t k) j) ∧
      Agree s.vg.mem s'.vg.mem tp (k + 1) ∧
      Frame s s' [.rax, .rdx, .rdi, .rbx, .rbp, .r10, .r11, .r13, .r14, .r15] := by
  intro A0 q N0
  have htp := ar.htp
  have hN0 : s.vg.mem.readW np 64 = n 0 := by have := hN 0 (by omega); rwa [wa_zero] at this
  have hT0 : s.vg.mem.readW tp 64 = t 0 := by have := hT 0 (by omega); rwa [wa_zero] at this
  obtain ⟨s₁, hx1, p10, p13, pax, p15, pbx, pbp, pmem, pF⟩ :=
    outerHead_ok s k i ap bp np n0p tp n0' a bw n t hk8 hi ar hrsi hrcx hrsp hr12 hr8 hrax hr14 hA hN hB hN0
      hT0 (hT 1 (by omega))
  rw [writeW_wa_zero] at pmem
  have ag1 : Agree s.vg.mem s₁.vg.mem tp (k + 1) := by
    rw [pmem]; exact (Agree.refl _ tp _).writeW_below _ (by omega)
  have ar1 := ar.frame pF
  let f := f1 a n t (bw i) q
  let c₀ : C := (A0.2, N0.2)
  have hI1 : ChainInv s₁ s₁ tp a f c₀ 1 := by
    refine ⟨le_refl _, Frame.refl _ _, p15, p10, p13, pax, Agree.refl _ _ _, ?_⟩
    intro j hj
    obtain rfl : j = 0 := by omega
    rw [pmem, readW_writeW_self]; rfl
  have g1 : ∀ r, r ∉ [Reg.rax, .rdx, .rdi, .rbx, .rbp, .r10, .r11, .r13, .r15] →
      s₁.vg.gpr r = s.vg.gpr r := pF.gpr
  have hT1 : ∀ j, 1 ≤ j → j ≤ k → s₁.vg.mem.readW (wa tp j) 64 = t j := fun j h1 h2 => by
    rw [pmem, readW_tp_ne _ htp (by omega) (by omega) (by omega), hT j h2]
  obtain ⟨s₂, hx2, hI2⟩ := loop_ok (body := .block Rind.X86_64.Mul4x.inner) (c := Rind.X86_64.Cond.vg .b)
    (fun j s => ChainInv s₁ s tp a f c₀ j) (fun j => j + 7 ≤ k) (fun j => decide (j + 7 < k))
    (innerTrace ap np tp) 4
    (fun j s' hI hR => inner_step s₁ k ap bp np n0p tp (bw i) q a n t c₀ ar1
      ((g1 .rsi (by decide)).trans hrsi) ((g1 .rcx (by decide)).trans hrcx) ((g1 .rsp (by decide)).trans hrsp)
      pbx pbp ((g1 .r9 (by decide)).trans hr9)
      (fun i hi => (ag1.arr (by omega) htp ar.hap ar.sepA hi).trans (hA i hi))
      (fun i hi => (ag1.arr (by omega) htp ar.hnp ar.sepN hi).trans (hN i hi)) hT1 j s' hI hR)
    ((k - 8) / 4) 1 s₁ hI1 (fun i hi => by omega) (fun i hi => by simp; omega) (by simp; omega)
  rw [show 1 + 4 * ((k - 8) / 4 + 1) = k - 3 by omega] at hI2
  have ag2 : Agree s.vg.mem s₂.vg.mem tp (k + 1) := ag1.trans (hI2.agree.mono (by omega)) (le_refl _)
  have F2 := hI2.frame
  have ar2 := ar1.frame F2
  obtain ⟨s₃, hx3, oax, o14, ocf, omem, oF⟩ :=
    outerTail_ok s₂ (k - 3) k i ap bp np n0p tp (bw i) q _ _ a n t (by omega) (by omega) ar2
      ((F2.gpr .rsi (by decide)).trans ((g1 .rsi (by decide)).trans hrsi))
      ((F2.gpr .rcx (by decide)).trans ((g1 .rcx (by decide)).trans hrcx))
      ((F2.gpr .rsp (by decide)).trans ((g1 .rsp (by decide)).trans hrsp))
      hI2.r15 ((F2.gpr .rbx (by decide)).trans pbx) ((F2.gpr .rbp (by decide)).trans pbp)
      hI2.r10 hI2.r13 hI2.rax ((F2.gpr .r14 (by decide)).trans ((g1 .r14 (by decide)).trans hr14))
      ((F2.gpr .r9 (by decide)).trans ((g1 .r9 (by decide)).trans hr9)) hi
      (fun i hi => (ag2.arr (by omega) htp ar.hap ar.sepA hi).trans (hA i hi))
      (fun i hi => (ag2.arr (by omega) htp ar.hnp ar.sepN hi).trans (hN i hi))
      (by have := (ag2.arr (by omega) htp ar.hap ar.sepA (i := 0) (by omega)).trans (hA 0 (by omega))
          rwa [wa_zero] at this)
      (fun j h1 h2 => (hI2.agree.tp (k := k) (by omega) (by omega) htp).trans (hT1 j (by omega) (by omega)))
  have ag3 : Agree s₂.vg.mem s₃.vg.mem tp (k + 1) := by
    rw [omem]
    exact ((((Agree.refl _ tp _).writeW_below _ (by omega)).writeW_below _ (by omega)).writeW_below _
      (by omega)).writeW_below _ (by omega)
  refine ⟨s₃, Exec.seq (Exec.block hx1) (Exec.seq hx2 (Exec.block hx3)), oax, o14, ocf, ?_,
    ag2.trans ag3 (le_refl _), (pF.mono (by decide)).trans ((F2.mono (by decide)).trans (oF.mono (by decide)))⟩
  intro j hj
  rw [omem]
  rcases (by omega : j < k - 3 ∨ j = k - 3 ∨ j = k - 3 + 1 ∨ j = k - 3 + 2 ∨ j = k - 3 + 3) with
    h | rfl | rfl | rfl | rfl
  · rw [readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega),
      readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega),
      hI2.words j h]
    simp only [passOut, show j + 1 < k by omega, ↓reduceIte]; rfl
  · rw [readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega),
      readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_writeW_self]
    simp only [passOut, show k - 3 + 1 < k by omega, ↓reduceIte]; rfl
  · rw [readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_tp_ne _ htp (by omega) (by omega) (by omega),
      readW_writeW_self]
    simp only [passOut, show k - 3 + 1 + 1 < k by omega, ↓reduceIte]; rfl
  · rw [readW_tp_ne _ htp (by omega) (by omega) (by omega), readW_writeW_self]
    simp only [passOut, show ¬ k - 3 + 2 + 1 < k by omega, show k - 3 + 2 + 1 = k by omega, Nat.lt_irrefl,
      show k - 1 = k - 3 + 1 + 1 by omega, ↓reduceIte]; rfl
  · rw [readW_writeW_self]
    simp only [passOut, show ¬ k - 3 + 3 + 1 < k by omega, show ¬ k - 3 + 3 + 1 = k by omega,
      show k - 1 = k - 3 + 1 + 1 by omega, ↓reduceIte]; rfl

end rind.x86_64.mul4x
