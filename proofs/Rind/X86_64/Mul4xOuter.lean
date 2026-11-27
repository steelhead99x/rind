import Rind.X86_64.Mul4xLoop

/-! # bn_mul4x_mont's passes

The loop of outer passes, and what all `k` passes leave in `tp`: `t` with
`2^(64k)·t = a·b + Q·n` for some `Q`, and `t < a + n`. -/

open VG VG.X86_64 Rind.X86_64.Mul4x rind.x86_64.asm

set_option linter.unusedSimpArgs false

namespace rind.x86_64.mul4x

/-- A pass keeps `V < A + N` and `2^(64i)·V = A·B_i + Q·N`, `B_i` the low `i` words of `b`. -/
theorem mont_step (A N V V' Bi Q b q i : Nat) (hb : b < 2 ^ 64) (hq : q < 2 ^ 64)
    (H : 2 ^ 64 * V' = V + A * b + q * N) (hV : V < A + N) (hQ : 2 ^ (64 * i) * V = A * Bi + Q * N) :
    V' < A + N ∧ 2 ^ (64 * (i + 1)) * V' = A * (Bi + b * 2 ^ (64 * i)) + (Q + 2 ^ (64 * i) * q) * N := by
  constructor
  · have h1 : A * (b + 1) ≤ A * 2 ^ 64 := Nat.mul_le_mul_left A (by omega)
    have h2 : (q + 1) * N ≤ 2 ^ 64 * N := Nat.mul_le_mul_right N (by omega)
    have h3 : 2 ^ 64 * V' < 2 ^ 64 * (A + N) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left h3
  · have e : 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
    rw [e]
    zify at H hQ ⊢
    linear_combination (2 : ℤ) ^ (64 * i) * H + hQ

/-- The outer loop before pass `i`: the words `t` the passes so far left, with their bound and value. -/
structure OuterInv (s₁ s : S) (k : Nat) (tp : Addr) (a bw n : Nat → BitVec 64) (i : Nat) : Prop where
  frame : Frame s₁ s [.rax, .rdx, .rdi, .rbx, .rbp, .r10, .r11, .r13, .r14, .r15]
  rax : s.vg.gpr .rax = a 0
  r14 : s.vg.gpr .r14 = BitVec.ofNat 64 i
  agree : Agree s₁.vg.mem s.vg.mem tp (k + 1)
  words : ∃ t : Nat → BitVec 64, (∀ j ≤ k, s.vg.mem.readW (wa tp j) 64 = t j) ∧
    val t (k + 1) < val a k + val n k ∧ ∃ Q, 2 ^ (64 * i) * val t (k + 1) = val a k * val bw i + Q * val n k

set_option maxHeartbeats 1000000 in
theorem outer_step (s₁ : S) (k : Nat) (ap bp np n0p tp n0' : BitVec 64) (a bw n : Nat → BitVec 64)
    (hk8 : 8 ≤ k) (hk4 : k % 4 = 0) (ar : Arrays s₁ k ap bp np n0p tp)
    (hrsi : s₁.vg.gpr .rsi = ap) (hrcx : s₁.vg.gpr .rcx = np) (hrsp : s₁.vg.gpr .rsp = tp)
    (hr12 : s₁.vg.gpr .r12 = bp) (hr8 : s₁.vg.gpr .r8 = n0') (hr9 : s₁.vg.gpr .r9 = BitVec.ofNat 64 k)
    (hA : ∀ i < k, s₁.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s₁.vg.mem.readW (wa np i) 64 = n i)
    (hB : ∀ i < k, s₁.vg.mem.readW (wa bp i) 64 = bw i)
    (hn0 : ((n 0).toNat * n0'.toNat + 1) % 2 ^ 64 = 0)
    (i : Nat) (s : S) (hI : OuterInv s₁ s k tp a bw n i) (hi : i < k) :
    ∃ s', Exec I passProg s (passTrace ap bp np tp k i) s' ∧
      I.eval (Rind.X86_64.Cond.vg .b) s' = some (decide (i + 1 < k)) ∧ OuterInv s₁ s' k tp a bw n (i + 1) := by
  obtain ⟨hF, hax, h14, hag, t, hT, hV, Q, hQ⟩ := hI
  have htp := ar.htp
  have g : ∀ r, r ∉ [Reg.rax, .rdx, .rdi, .rbx, .rbp, .r10, .r11, .r13, .r14, .r15] → s.vg.gpr r = s₁.vg.gpr r :=
    hF.gpr
  obtain ⟨s', hx, oax, o14, ocf, owords, oag, oF⟩ :=
    pass_ok s k i ap bp np n0p tp n0' a bw n t hk8 hk4 hi (ar.frame hF)
      ((g .rsi (by decide)).trans hrsi) ((g .rcx (by decide)).trans hrcx) ((g .rsp (by decide)).trans hrsp)
      ((g .r12 (by decide)).trans hr12) ((g .r8 (by decide)).trans hr8) hax h14 ((g .r9 (by decide)).trans hr9)
      (fun j hj => (hag.arr (by omega) htp ar.hap ar.sepA hj).trans (hA j hj))
      (fun j hj => (hag.arr (by omega) htp ar.hnp ar.sepN hj).trans (hN j hj))
      (fun j hj => (hag.arr (by omega) htp ar.hbp ar.sepB hj).trans (hB j hj)) hT
  refine ⟨s', hx, by simpa [Rind.X86_64.isa, Rind.X86_64.eval, VG.X86_64.eval] using ocf, hF.trans oF, oax, o14,
    hag.trans oag (le_refl _), ?_⟩
  -- The pass's arithmetic.
  let A0 := mac (a 0) (bw i) (t 0)
  let q := n0' * A0.1
  let t' := passOut (f1 a n t (bw i) q) (A0.2, (mac (n 0) q A0.1).2) k (t k)
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  have hP : 2 ^ 64 * val t' (K + 1 + 1) = val t (K + 1 + 1) + val a (K + 1) * (bw i).toNat + q.toNat * val n (K + 1) :=
    pass_nat a n t (bw i) q K (mac_q (n 0) n0' A0.1 hn0)
  obtain ⟨h1, h2⟩ := mont_step (val a (K + 1)) (val n (K + 1)) (val t (K + 1 + 1)) (val t' (K + 1 + 1)) (val bw i) Q
    (bw i).toNat q.toNat i (bw i).isLt q.isLt hP hV hQ
  exact ⟨t', owords, h1, Q + 2 ^ (64 * i) * q.toNat, by rw [h2]; rfl⟩

/-- The trace of the loop of outer passes. -/
def outerTrace (ap bp np tp : Addr) (k : Nat) : List Leak := loopTrace (passTrace ap bp np tp k) 1 1 (k - 2)

theorem outer_ok (s₁ : S) (k : Nat) (ap bp np n0p tp n0' : BitVec 64) (a bw n : Nat → BitVec 64)
    (hk8 : 8 ≤ k) (hk4 : k % 4 = 0) (ar : Arrays s₁ k ap bp np n0p tp)
    (hrsi : s₁.vg.gpr .rsi = ap) (hrcx : s₁.vg.gpr .rcx = np) (hrsp : s₁.vg.gpr .rsp = tp)
    (hr12 : s₁.vg.gpr .r12 = bp) (hr8 : s₁.vg.gpr .r8 = n0') (hr9 : s₁.vg.gpr .r9 = BitVec.ofNat 64 k)
    (hA : ∀ i < k, s₁.vg.mem.readW (wa ap i) 64 = a i) (hN : ∀ i < k, s₁.vg.mem.readW (wa np i) 64 = n i)
    (hB : ∀ i < k, s₁.vg.mem.readW (wa bp i) 64 = bw i)
    (hn0 : ((n 0).toNat * n0'.toNat + 1) % 2 ^ 64 = 0) (hI : OuterInv s₁ s₁ k tp a bw n 1) :
    ∃ s', Exec I (.loop passProg (Rind.X86_64.Cond.vg .b)) s₁ (outerTrace ap bp np tp k) s' ∧
      OuterInv s₁ s' k tp a bw n k := by
  obtain ⟨s', hx, hI'⟩ := loop_ok (body := passProg) (c := Rind.X86_64.Cond.vg .b)
    (fun i s => OuterInv s₁ s k tp a bw n i) (fun i => i < k) (fun i => decide (i + 1 < k)) (passTrace ap bp np tp k) 1
    (fun i s hI hi => outer_step s₁ k ap bp np n0p tp n0' a bw n hk8 hk4 ar hrsi hrcx hrsp hr12 hr8 hr9 hA hN hB hn0
      i s hI hi)
    (k - 2) 1 s₁ hI (fun i hi => by omega) (fun i hi => by simp; omega) (by simp; omega)
  rw [show 1 + 1 * (k - 2 + 1) = k by omega] at hI'
  exact ⟨s', hx, hI'⟩

end rind.x86_64.mul4x
