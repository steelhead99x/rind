import Rind.X86_64.Sqrx8xBlocks
import Rind.X86_64.Mul4xSub

/-! # `t`'s value, and the triangle's sum

`t`'s value as words are stored into it, and `Q R`, the products `a_i · a_j`, `i < j`, of rows `i` below `8R`,
which the triangle phase adds up row block by row block: twice it plus those rows' squares is
`A(8R) · (2 A(k) - A(8R))`, where `A(n)` is `a`'s first `n` words' value, so `a²` once `8R = k`. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 4096

namespace rind.x86_64.sqrx8x

/-! ## `t` under stores -/

theorem tw_write_self (M : Mem) (fp : Addr) (p : Nat) (v : BitVec 64) :
    tw (M.writeW (wa fp (p + 7)) v) fp p = v := readW_writeW_self _ _ _

theorem tw_write_ne (M : Mem) (fp : Addr) (p q : Nat) (v : BitVec 64) (hpq : q ≠ p)
    (hp : fp.toNat + 8 * (p + 8) ≤ 2 ^ 64) (hq : fp.toNat + 8 * (q + 8) ≤ 2 ^ 64) :
    tw (M.writeW (wa fp (p + 7)) v) fp q = tw M fp q :=
  readW_writeW_wa _ _ _ _ _ _ (by omega) (by omega) (by omega)

/-- `t`'s value after a store into word `p`. -/
theorem val_write (M : Mem) (fp : Addr) (p N : Nat) (v : BitVec 64) (hp : p < N)
    (hfp : fp.toNat + 8 * (N + 7) ≤ 2 ^ 64) :
    (val (tw (M.writeW (wa fp (p + 7)) v) fp) N : ℤ) =
      val (tw M fp) N + ((v.toNat : ℤ) - (tw M fp p).toNat) * 2 ^ (64 * p) := by
  induction N with
  | zero => omega
  | succ N ih =>
    show ((gsum _ N + _ : Nat) : ℤ) = (gsum _ N + _ : Nat) + _
    beta_reduce
    by_cases h : p = N
    · subst h
      have e : gsum (fun i => (tw (M.writeW (wa fp (p + 7)) v) fp i).toNat) p = gsum (fun i => (tw M fp i).toNat) p :=
        gsum_congr fun m hm => by rw [tw_write_ne M fp p m v (by omega) (by omega) (by omega)]
      rw [e, tw_write_self]; push_cast; ring
    · have := ih (by omega) (by omega)
      rw [tw_write_ne M fp p N v (Ne.symm h) (by omega) (by omega)]
      push_cast at this ⊢
      rw [this]; ring

/-- `t`'s `n` words from word `q`. -/
def twl (M : Mem) (fp : Addr) : Nat → Nat → List (BitVec 64)
  | _, 0 => []
  | q, n + 1 => tw M fp q :: twl M fp (q + 1) n

theorem twl_length (M : Mem) (fp : Addr) (q n : Nat) : (twl M fp q n).length = n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => simp [twl, ih]

theorem twl_write (M : Mem) (fp : Addr) (p q n : Nat) (v : BitVec 64) (hpq : p < q)
    (hfp : fp.toNat + 8 * (q + n + 7) ≤ 2 ^ 64) :
    twl (M.writeW (wa fp (p + 7)) v) fp q n = twl M fp q n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [twl]
    rw [tw_write_ne _ _ _ _ _ (by omega) (by omega) (by omega), ih (q + 1) (by omega) (by omega)]

/-- `t`'s value after the stores `ws` from word `q`: up by them, down by the words they replace. -/
theorem val_wrs (M : Mem) (fp : Addr) (q N : Nat) (ws : List (BitVec 64)) (hq : q + ws.length ≤ N)
    (hfp : fp.toNat + 8 * (N + 7) ≤ 2 ^ 64) :
    (val (tw (wrs M fp q ws) fp) N : ℤ) + 2 ^ (64 * q) * hsum (twl M fp q ws.length) =
      val (tw M fp) N + 2 ^ (64 * q) * hsum ws := by
  induction ws generalizing M q with
  | nil => simp [wrs, twl, hsum]
  | cons w ws ih =>
    simp only [List.length_cons] at hq
    have h1 := ih (M.writeW (wa fp (q + 7)) w) (q + 1) (by omega)
    rw [twl_write M fp q (q + 1) ws.length w (by omega) (by omega)] at h1
    have h2 := val_write M fp q N w (by omega) hfp
    simp only [wrs, List.length_cons, twl, hsum]
    have e : (2 : ℤ) ^ (64 * (q + 1)) = 2 ^ (64 * q) * 2 ^ 64 := by rw [Nat.mul_succ, pow_add]
    rw [e] at h1
    push_cast
    linear_combination h1 + h2

theorem hsum_eq_val (f : Nat → BitVec 64) :
    hsum [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] = val f 8 := by
  simp only [hsum, val, gsum]; ring

/-! ## The triangle's sum -/

/-- Row block `R`'s eight words' value. -/
abbrev rowV (a : Nat → BitVec 64) (R : Nat) : Nat := val (fun i => a (8 * R + i)) 8

/-- The squares `a_i²` of row block `R`, at their weights from word `16R`. -/
def sqb (a : Nat → BitVec 64) (R : Nat) : Nat :=
  (a (8 * R)).toNat * (a (8 * R)).toNat + (a (8 * R + 1)).toNat * (a (8 * R + 1)).toNat * 2 ^ 128 +
    (a (8 * R + 2)).toNat * (a (8 * R + 2)).toNat * 2 ^ 256 + (a (8 * R + 3)).toNat * (a (8 * R + 3)).toNat * 2 ^ 384 +
    (a (8 * R + 4)).toNat * (a (8 * R + 4)).toNat * 2 ^ 512 + (a (8 * R + 5)).toNat * (a (8 * R + 5)).toNat * 2 ^ 640 +
    (a (8 * R + 6)).toNat * (a (8 * R + 6)).toNat * 2 ^ 768 + (a (8 * R + 7)).toNat * (a (8 * R + 7)).toNat * 2 ^ 896

/-- The products `a_i · a_j`, `i < j`, of rows below `8R`. -/
def Q (a : Nat → BitVec 64) (k : Nat) : Nat → Nat
  | 0 => 0
  | R + 1 => Q a k R + diag8 (fun i => a (8 * R + i)) * 2 ^ (64 * (16 * R)) +
      rowV a R * val (fun i => a (8 * R + 8 + i)) (k - 8 * R - 8) * 2 ^ (64 * (16 * R + 8))

/-- The squares of rows below `8R`. -/
def SQ (a : Nat → BitVec 64) : Nat → Nat
  | 0 => 0
  | R + 1 => SQ a R + sqb a R * 2 ^ (64 * (16 * R))

theorem diag_sq (a : Nat → BitVec 64) (R : Nat) :
    2 * diag8 (fun i => a (8 * R + i)) + sqb a R = rowV a R * rowV a R := by
  simp only [diag8, sqb, rowV, val, gsum]; ring

theorem Q_ident (a : Nat → BitVec 64) (k R : Nat) (hR : 8 * R ≤ k) :
    2 * Q a k R + SQ a R + val a (8 * R) * val a (8 * R) = 2 * val a (8 * R) * val a k := by
  induction R with
  | zero => simp [Q, SQ, val, gsum]
  | succ R ih =>
    have ih := ih (by omega)
    have v1 := val_split a (8 * R) 8
    have v2 := val_split a (8 * R + 8) (k - 8 * R - 8)
    rw [show 8 * R + 8 + (k - 8 * R - 8) = k by omega] at v2
    have d := diag_sq a R
    simp only [Q, SQ, show 8 * (R + 1) = 8 * R + 8 by ring]
    rw [v1] at v2 ⊢
    rw [v2] at ih ⊢
    have e1 : (2 : Nat) ^ (64 * (16 * R)) = 2 ^ (64 * (8 * R)) * 2 ^ (64 * (8 * R)) := by rw [← pow_add]; ring_nf
    have e2 : (2 : Nat) ^ (64 * (16 * R + 8)) = 2 ^ (64 * (8 * R)) * 2 ^ (64 * (8 * R + 8)) := by
      rw [← pow_add]; ring_nf
    have e3 : (2 : Nat) ^ (64 * (8 * R + 8)) = 2 ^ (64 * (8 * R)) * 2 ^ 512 := by rw [← pow_add]; ring_nf
    rw [e1, e2, e3] at *
    simp only [rowV] at d
    zify at ih d ⊢
    linear_combination ih + (2 : ℤ) ^ (64 * (8 * R)) * 2 ^ (64 * (8 * R)) * d

/-- The products so far fit in `8R + k` words. -/
theorem Q_lt (a : Nat → BitVec 64) (k R : Nat) (hR : 8 * R ≤ k) : Q a k R < 2 ^ (64 * (8 * R + k)) := by
  have h := Q_ident a k R hR
  have h1 := val_lt a (8 * R)
  have h2 := val_lt a k
  have h3 : val a (8 * R) * val a k < 2 ^ (64 * (8 * R)) * 2 ^ (64 * k) := by
    rcases Nat.eq_zero_or_pos (val a k) with h0 | h0
    · rw [h0, Nat.mul_zero]; positivity
    · calc val a (8 * R) * val a k < 2 ^ (64 * (8 * R)) * val a k := Nat.mul_lt_mul_of_pos_right h1 h0
        _ ≤ _ := Nat.mul_le_mul_left _ h2.le
  rw [show 64 * (8 * R + k) = 64 * (8 * R) + 64 * k by ring, Nat.pow_add]
  nlinarith

end rind.x86_64.sqrx8x
