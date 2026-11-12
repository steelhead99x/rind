import Rind.Keccak
import Rind.HashSpec
import Mathlib.Tactic.LinearCombination

/-!
# SHA-3 and SHAKE over bytes

FIPS 202's sponge on a byte message, its state as 200 bytes: the lanes' bytes
in order, each least significant byte first, as Appendix B.1 converts strings
to bytes. Absorbing XORs each whole `R`-byte block of the padded message into
the state and applies KECCAK-f[1600], s2n-bignum's `keccak 24` on the state's
lanes; squeezing reads `R` bytes of the state before each further KECCAK-f.
Padding is Appendix B.2's: a byte holding the suffix bits and the first
padding bit, zeros, and the top bit of the block's last byte.

`sha3_256_eq` and its siblings prove these FIPS 202's SHA-3 and SHAKE functions
as SymCrypt's transliteration (`Rind.SymCrypt.Sha3`) defines them, on the
message's bits.
-/

namespace rind.spec

open Spec Spec.SHA3
open scoped Spec.Notations

/-- The state's bytes: each lane's, least significant first. -/
def stateBytes (L : List (BitVec 64)) : List Byte := L.flatMap BitVec.toLEBytes

/-- The 25 lanes whose bytes are `S`. -/
def stateLanes (S : List Byte) : List (BitVec 64) :=
  (List.range 25).map fun i => (BitVec.fromLEBytes ((S.drop (8 * i)).take 8)).setWidth 64

/-- KECCAK-f[1600] on the state's bytes. -/
def keccakF (S : List Byte) : List Byte := stateBytes (keccak 24 (stateLanes S))

/-- `S` with `B` XORed into it from byte `off`. -/
def xorAt (S : List Byte) (off : Nat) (B : List Byte) : List Byte :=
  S.mapIdx fun i x => if off ≤ i ∧ i < off + B.length then x ^^^ B[i - off]! else x

/-- Appendix B.2's padding of `M` to whole `R`-byte blocks: the byte `d`, which
holds the suffix bits and the first padding bit, zeros, and the last
padding bit, the top bit of the last byte. -/
def keccakPad (R : Nat) (d : Byte) (M : List Byte) : List Byte :=
  let q := R - M.length % R
  xorAt (M ++ d :: List.replicate (q - 1) 0) (M.length + q - 1) [0x80]

/-- The state after absorbing each whole `R`-byte block of `P` into `S`. -/
def absorb (R : Nat) (S P : List Byte) : List Byte :=
  (blocks R P).foldl (fun S B => keccakF (xorAt S 0 B)) S

/-- `n` bytes squeezed from `S`: `R` from it, then `R` from each KECCAK-f of it
in turn. -/
def squeeze (R n : Nat) (S : List Byte) : List Byte :=
  (List.range n).map fun k => (keccakF^[k / R] S)[k % R]!

/-- The sponge at rate `R` bytes: `n` bytes of `M` padded with `d`. -/
def sponge (R : Nat) (d : Byte) (M : List Byte) (n : Nat) : List Byte :=
  squeeze R n (absorb R (List.replicate 200 0) (keccakPad R d M))

/-- The pad byte of SHA-3: suffix `01`, then the first padding bit. -/
def sha3Pad : Byte := 0x06

/-- The pad byte of SHAKE: suffix `1111`, then the first padding bit. -/
def shakePad : Byte := 0x1f

def sha3_256 (M : List Byte) : List Byte := sponge 136 sha3Pad M 32
def sha3_384 (M : List Byte) : List Byte := sponge 104 sha3Pad M 48
def sha3_512 (M : List Byte) : List Byte := sponge 72 sha3Pad M 64
def shake128 (M : List Byte) (n : Nat) : List Byte := sponge 168 shakePad M n
def shake256 (M : List Byte) (n : Nat) : List Byte := sponge 136 shakePad M n

/-! ## The state's bits -/

/-- The string whose bits are `S`'s, each byte's least significant first. -/
def bitsOf (S : List Byte) : Vector Bool b :=
  Vector.ofFn fun i => S[i.val / 8]!.toNat.testBit (i.val % 8)

theorem testBit_flatMap_toLEBytes (L : List (BitVec 64)) (k t : Nat) (ht : t < 8) :
    (L.flatMap BitVec.toLEBytes)[k]!.toNat.testBit t = (L[k / 8]!)[8 * (k % 8) + t]! := by
  induction L generalizing k with
  | nil => simp
  | cons a L ih =>
    have ha : a.toLEBytes.length = 8 := by simp
    have hb := BitVec.toLEBytes_getElem!_testBit a (k % 8) t ht
    simp only [Byte.testBit] at hb
    rw [List.flatMap_cons, List.getElem!_eq_getElem?_getD]
    by_cases hk : k < 8
    · rw [List.getElem?_append_left (by omega), ← List.getElem!_eq_getElem?_getD,
        Nat.div_eq_of_lt hk, List.getElem!_cons_zero, ← hb, Nat.mod_eq_of_lt hk]
    · rw [List.getElem?_append_right (by omega), ha, ← List.getElem!_eq_getElem?_getD, ih,
        show (k - 8) / 8 = k / 8 - 1 by omega, show (k - 8) % 8 = k % 8 by omega,
        show k / 8 = (k / 8 - 1) + 1 by omega]
      simp

theorem bitsOf_stateBytes (L : List (BitVec 64)) : bitsOf (stateBytes L) = lanesToString L := by
  ext i hi
  simp only [b] at hi
  simp only [bitsOf, lanesToString, Vector.getElem_ofFn, stateBytes]
  rw [testBit_flatMap_toLEBytes _ _ _ (by omega), BitVec.getElem!_eq_testBit_toNat,
    ← BitVec.getLsbD]
  congr 2 <;> omega

theorem lanesToString_stateLanes (S : List Byte) : lanesToString (stateLanes S) = bitsOf S := by
  ext i hi
  simp only [b] at hi
  simp only [bitsOf, lanesToString, Vector.getElem_ofFn, stateLanes]
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some, BitVec.getLsbD_setWidth]
  rw [decide_eq_true (show i % 64 < 64 by omega), Bool.true_and]
  have hlen : ((S.drop (8 * (i / 64))).take 8).length = min 8 (S.length - 8 * (i / 64)) := by
    simp
  by_cases hl : i % 64 < 8 * ((S.drop (8 * (i / 64))).take 8).length
  all_goals have hl' := hl; rw [hlen] at hl'
  · rw [BitVec.getLsbD_eq_getElem hl, BitVec.fromLEBytes_getElem]
    simp only [List.getElem_take, List.getElem_drop, Byte.testBit]
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some]
    simp only [show 8 * (i / 64) + i % 64 / 8 = i / 8 by omega, show i % 64 % 8 = i % 8 by omega]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

theorem bitsOf_keccakF (S : List Byte) : bitsOf (keccakF S) = KECCAK_f (bitsOf S) := by
  rw [keccakF, bitsOf_stateBytes, keccak_eq_KECCAK_f, lanesToString_stateLanes]

theorem bitsOf_iterate_keccakF (k : Nat) (S : List Byte) :
    bitsOf (keccakF^[k] S) = KECCAK_f^[k] (bitsOf S) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', bitsOf_keccakF, ih]

/-! ## SymCrypt's sponge, bit by bit -/

theorem getElem_Trunc {n s : Nat} (X : Vector Bool n) (h : s ≤ n) (j : Nat) (hj : j < s) :
    (Spec.SHA3.Trunc s X h)[j] = X[j] := by
  simp [Spec.SHA3.Trunc, slice]

theorem getElem_vappend {m n : Nat} (u : Vector Bool m) (v : Vector Bool n) (j : Nat)
    (hj : j < m + n) :
    (u ‖ v)[j] = if h : j < m then u[j] else v[j - m] :=
  Vector.getElem_append hj

/-- Bit `j` that `SPONGE.squeeze` appends to `Z` comes from `S` after `j / r`
more permutations, past `Z`'s bits. -/
theorem getElem_squeeze {m d r : Nat} (f : Vector Bool b → Vector Bool b) (Z : Vector Bool m)
    (S : Vector Bool b) (hr : 0 < r ∧ r < b) (j : Nat) (hj : j < d) :
    (SPONGE.squeeze (d := d) f r Z S hr)[j] =
      if h : j < m then Z[j] else
        (f^[(j - m) / r] S)[(j - m) % r]'(by have := Nat.mod_lt (j - m) hr.1; omega) := by
  rw [SPONGE.squeeze]
  split
  · rename_i hd
    rw [getElem_Trunc _ _ _ hj]
    simp only [show j < m by omega, ↓reduceDIte]
  · rename_i hd
    simp only [SPONGE.squeeze_step]
    rw [getElem_squeeze f (Z ‖ Spec.SHA3.Trunc r S _) (f S) hr j hj]
    by_cases h1 : j < m
    · simp only [show j < m + r by omega, h1, ↓reduceDIte, getElem_vappend _ _ _ (show j < m + r by omega)]
    · by_cases h2 : j < m + r
      · simp only [h1, h2, ↓reduceDIte, getElem_vappend _ _ _ h2]
        rw [getElem_Trunc _ _ _ (by omega)]
        simp only [Nat.div_eq_of_lt (show j - m < r by omega), Function.iterate_zero, id,
          Nat.mod_eq_of_lt (show j - m < r by omega)]
      · simp only [h1, h2, ↓reduceDIte]
        have hq : (j - m) / r = (j - (m + r)) / r + 1 := by
          rw [show j - m = (j - (m + r)) + r by omega, Nat.add_div_right _ hr.1]
        have hm : (j - m) % r = (j - (m + r)) % r := by
          rw [show j - m = (j - (m + r)) + r by omega, Nat.add_mod_right]
        simp only [hq, hm, Function.iterate_succ_apply]
termination_by d - m
decreasing_by omega

/-! ## Bytes and blocks -/

@[simp] theorem length_xorAt (S : List Byte) (off : Nat) (B : List Byte) :
    (xorAt S off B).length = S.length := by
  simp [xorAt]

theorem getElem!_xorAt (S : List Byte) (off : Nat) (B : List Byte) (i : Nat) (hi : i < S.length) :
    (xorAt S off B)[i]! =
      if off ≤ i ∧ i < off + B.length then S[i]! ^^^ B[i - off]! else S[i]! := by
  simp only [xorAt, List.getElem!_eq_getElem?_getD, List.getElem?_mapIdx,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

theorem length_keccakRound (rc : BitVec 64) (L : List (BitVec 64)) :
    (keccakRound rc L).length = 25 := by
  simp [keccakRound]

@[simp] theorem length_keccakF (S : List Byte) : (keccakF S).length = 200 := by
  simp [keccakF, stateBytes, keccak, length_keccakRound]

theorem length_iterate_keccakF (k : Nat) (S : List Byte) (hS : S.length = 200) :
    (keccakF^[k] S).length = 200 := by
  cases k with
  | zero => exact hS
  | succ k => rw [Function.iterate_succ_apply']; exact length_keccakF _

theorem blocks_eq_map (R : Nat) (hR : 0 < R) (P : List Byte) :
    blocks R P = (List.range (P.length / R)).map fun i => (P.drop (i * R)).take R := by
  induction h : P.length / R generalizing P with
  | zero =>
    have : ¬(0 < R ∧ R ≤ P.length) := by have := (Nat.div_eq_zero_iff_lt hR).1 h; omega
    rw [blocks]
    simp only [this, ↓reduceIte, List.range_zero, List.map_nil]
  | succ k ih =>
    have hP : R ≤ P.length := by
      by_contra hc; rw [Nat.div_eq_of_lt (by omega)] at h; omega
    have hk : (P.drop R).length / R = k := by
      have := Nat.add_div_right (P.length - R) hR
      rw [Nat.sub_add_cancel hP] at this
      rw [List.length_drop]; omega
    rw [blocks]
    simp only [show 0 < R ∧ R ≤ P.length from ⟨hR, hP⟩]
    rw [ih (P.drop R) hk, List.range_succ_eq_map]
    simp [List.drop_drop, Nat.add_mul, Nat.add_comm]

/-- Folding a step over a list commutes with `φ`, which takes each step on
values meeting `Inv` to another step. -/
theorem foldl_hom {α β γ : Type} (l : List γ) (g1 : α → γ → α) (g2 : β → γ → β) (φ : α → β)
    (Inv : α → Prop) (h : ∀ a i, i ∈ l → Inv a → Inv (g1 a i) ∧ φ (g1 a i) = g2 (φ a) i)
    (a : α) (ha : Inv a) : Inv (l.foldl g1 a) ∧ φ (l.foldl g1 a) = l.foldl g2 (φ a) := by
  induction l generalizing a with
  | nil => exact ⟨ha, rfl⟩
  | cons x l ih =>
    obtain ⟨h1, h2⟩ := h a x (by simp) ha
    simp only [List.foldl_cons, ← h2]
    exact ih (fun a i hi => h a i (by simp [hi])) _ h1

/-! ## Absorbing, bit by bit -/

/-- Bits `i * r` to `i * r + r` of `P`, zero past them: SymCrypt's block `i`,
zero-extended. -/
def blockBits {m : Nat} (P : Vector Bool m) (r i : Nat) : Vector Bool b :=
  Vector.ofFn fun t => if h : t.val < r ∧ i * r + t.val < m then P[i * r + t.val] else false

theorem zeroExtend_slice {m : Nat} (P : Vector Bool m) (r i : Nat) (h : i * r + r ≤ m) :
    Bits.zeroExtend (slice P (i * r) r h) b = blockBits P r i := by
  ext t ht
  simp only [Bits.zeroExtend, slice, blockBits, Vector.getElem_ofFn]
  by_cases h1 : t < r
  · simp [h1, show i * r + t < m by omega]
  · simp [h1]

theorem map_val_finRange (n : Nat) : (List.finRange n).map Fin.val = List.range n :=
  List.ext_getElem (by simp) (by simp)

theorem testBit_xor_byte (x y : Byte) (t : Nat) :
    (x ^^^ y).toNat.testBit t = (x.toNat.testBit t != y.toNat.testBit t) := by
  rw [BitVec.toNat_xor, Nat.testBit_xor]

/-- XORing block `i` of a message into the state XORs its bits. -/
theorem bitsOf_xorAt_block (R : Nat) (P : List Byte) {m : Nat} (Pb : Vector Bool m)
    (hm : m = 8 * P.length) (hP : ∀ i (h : i < m), Pb[i] = P[i / 8]!.toNat.testBit (i % 8))
    (S : List Byte) (hS : S.length = 200) (i : Nat) (hi : i * R + R ≤ P.length) :
    bitsOf (xorAt S 0 ((P.drop (i * R)).take R)) = bitsOf S ^^^ blockBits Pb (8 * R) i := by
  subst hm
  ext t ht
  have ht1 : t < 1600 := ht
  rw [getElem_vxor _ _ _ ht]
  simp only [bitsOf, blockBits, Vector.getElem_ofFn]
  rw [getElem!_xorAt _ _ _ _ (by omega)]
  have hB : ((P.drop (i * R)).take R).length = R := by
    simp only [List.length_take, List.length_drop]; omega
  have e1 : i * (8 * R) = 8 * (i * R) := by ring
  rw [hB]
  simp only [e1]
  by_cases ht' : t < 8 * R
  · rw [ite_eq_left (by omega), testBit_xor_byte, dite_eq_left (by omega), hP]
    have e2 : (8 * (i * R) + t) / 8 = i * R + t / 8 := by omega
    have e3 : (8 * (i * R) + t) % 8 = t % 8 := by omega
    rw [e2, e3, List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
      List.getElem?_take, ite_eq_left (by omega), List.getElem?_drop, Nat.sub_zero,
      List.getElem!_eq_getElem?_getD]
    omega
  · rw [ite_eq_right (by omega), dite_eq_right (by omega)]
    simp

/-- Absorbing `P`'s blocks into the zero state, as SymCrypt's
`SPONGE.absorb` does to its bits. -/
theorem bitsOf_absorb (R : Nat) (hR : 0 < R) (P : List Byte) {m : Nat} (Pb : Vector Bool m)
    (hm : m = 8 * P.length) (hP : ∀ i (h : i < m), Pb[i] = P[i / 8]!.toNat.testBit (i % 8))
    (hdiv : m % (8 * R) = 0) :
    bitsOf (absorb R (List.replicate 200 0) P) = SPONGE.absorb KECCAK_f (8 * R) Pb hdiv (by omega) := by
  have hk : m / (8 * R) = P.length / R := by rw [hm, Nat.mul_div_mul_left _ _ (by omega)]
  have hl : (Vector.foldl (fun S Pi => KECCAK_f (S ⊕ Bits.zeroExtend Pi b)) 0
      (Spec.SHA3.blocks Pb (8 * R) (by omega) hdiv)) =
      SPONGE.absorb KECCAK_f (8 * R) Pb hdiv (by omega) := by
    unfold SPONGE.absorb; simp
  rw [← hl, ← Vector.foldl_toList, Spec.SHA3.blocks, Vector.toList_ofFn, List.ofFn_eq_map,
    List.foldl_map]
  simp only [zeroExtend_slice]
  rw [← List.foldl_map (f := Fin.val) (g := fun S i => KECCAK_f (S ⊕ blockBits Pb (8 * R) i)),
    map_val_finRange, hk, absorb, blocks_eq_map R hR, List.foldl_map]
  have h0 : bitsOf (List.replicate 200 0) = (0 : Vector Bool b) := by
    ext t ht
    have ht1 : t < 1600 := ht
    have hz : (List.replicate 200 (0 : Byte))[t / 8]! = 0 := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left (by omega)]
      rfl
    simp only [bitsOf, Vector.getElem_ofFn, hz]
    show _ = (Bits.ofNatLE 0 : Vector Bool b)[t]
    simp [Bits.ofNatLE]
  rw [← h0]
  refine (foldl_hom _ _ _ bitsOf (fun S => S.length = 200) ?_ _ (List.length_replicate ..)).2
  intro S i hi hS
  simp only [List.mem_range] at hi
  refine ⟨by simp, ?_⟩
  have hi' : i * R + R ≤ P.length := by
    have h1 := Nat.mul_le_mul_right R (show i + 1 ≤ P.length / R by omega)
    have h2 := Nat.div_mul_le_self P.length R
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  rw [bitsOf_keccakF, bitsOf_xorAt_block R P Pb hm hP S hS i hi']

/-! ## Padding, bit by bit -/

/-- `pad10*1` fills a message of `8 * a + ℓ` bits, `ℓ` suffix bits past whole
bytes, to the whole `R`-byte blocks that `keccakPad` does. -/
theorem padLen_eq (R a ℓ : Nat) (hR : 0 < R) (hℓ : ℓ + 2 ≤ 8) :
    8 * a + ℓ + padLen (8 * R) (8 * a + ℓ) = 8 * (a + (R - a % R)) := by
  have hk := Nat.div_add_mod a R
  have hc := Nat.mod_lt a hR
  generalize a / R = k at hk
  generalize a % R = c at hk hc ⊢
  subst hk
  obtain ⟨y, hy⟩ : ∃ y, y + 8 * c + ℓ + 2 = 8 * R := ⟨8 * R - 8 * c - ℓ - 2, by omega⟩
  have hy' : (y : Int) + 8 * c + ℓ + 2 = 8 * R := by exact_mod_cast hy
  have hj : (-((8 * (R * k + c) + ℓ : Nat) : Int) - 2) % ((8 * R : Nat) : Int) = y := by
    rw [show (-((8 * (R * k + c) + ℓ : Nat) : Int) - 2) =
        (y : Int) + ((8 * R : Nat) : Int) * (-(k : Int) - 1) by
      push_cast; linear_combination (-1 : Int) * hy']
    rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  simp only [padLen, padLen.j]
  rw [hj, Int.toNat_natCast]
  omega

theorem length_keccakPad (R : Nat) (hR : 0 < R) (d : Byte) (M : List Byte) :
    (keccakPad R d M).length = M.length + (R - M.length % R) := by
  have := Nat.mod_lt M.length hR
  simp only [keccakPad, length_xorAt, List.length_append, List.length_cons, List.length_replicate]
  omega

theorem testBit_0x80 (t : Nat) (ht : t < 8) : (0x80 : Byte).toNat.testBit t = (t == 7) := by
  interval_cases t <;> rfl

/-- Bit `t` of byte `k` of the padded message. -/
theorem testBit_keccakPad (R : Nat) (hR : 0 < R) (d : Byte) (M : List Byte) (k t : Nat)
    (hk : k < M.length + (R - M.length % R)) (ht : t < 8) :
    (keccakPad R d M)[k]!.toNat.testBit t =
      ((if k < M.length then M[k]!.toNat.testBit t else (k == M.length && d.toNat.testBit t)) !=
        (k == M.length + (R - M.length % R) - 1 && t == 7)) := by
  have := Nat.mod_lt M.length hR
  have hin : (M ++ d :: List.replicate (R - M.length % R - 1) 0)[k]! =
      if k < M.length then M[k]! else if k = M.length then d else 0 := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
    by_cases h1 : k < M.length
    · rw [List.getElem?_append_left h1, ite_eq_left h1]
    · rw [List.getElem?_append_right (by omega), ite_eq_right h1]
      by_cases h2 : k = M.length
      · subst h2; simp
      · rw [ite_eq_right h2, show k - M.length = (k - M.length - 1) + 1 by omega, List.getElem?_cons_succ,
          List.getElem?_replicate, ite_eq_left (by omega)]
        rfl
  unfold keccakPad
  rw [getElem!_xorAt _ _ _ _ (by simp; omega), hin]
  simp only [List.length_singleton]
  have hq1 : M.length ≤ M.length + (R - M.length % R) - 1 := by omega
  generalize hq : M.length + (R - M.length % R) - 1 = q at hk hq1 ⊢
  split_ifs with h3 h1 h2 h1 h2
  all_goals try rw [testBit_xor_byte, show k - q = 0 by omega, List.getElem!_cons_zero,
    testBit_0x80 t ht]
  all_goals (try (exfalso; omega))
  all_goals (try simp only [show (k == q) = true by simp; omega])
  all_goals (try simp only [show (k == q) = false by simp; omega])
  all_goals (try simp only [show (k == M.length) = true by simp; omega])
  all_goals (try simp only [show (k == M.length) = false by simp; omega])
  all_goals simp

/-- `pad10*1`: a one, zeros, and a one. -/
theorem getElem_pad101 (x m p : Nat) (hp : p < padLen x m) :
    («pad10*1» x m)[p] = (p == 0 || p == padLen x m - 1) := by
  unfold «pad10*1»
  rw [getElem_vappend _ _ _ hp]
  split
  · rename_i h1
    rw [getElem_vappend _ _ _ h1]
    split
    · rename_i h2
      simp only [show p = 0 by omega]
      rfl
    · rename_i h2
      simp only [Vector.getElem_replicate]
      simp only [padLen] at hp ⊢
      rw [show (p == 0) = false by simp; omega, show (p == 1 + padLen.j x m + 1 - 1) = false by simp; omega]
      rfl
  · rename_i h1
    simp only [padLen] at hp ⊢
    rw [show (p == 1 + padLen.j x m + 1 - 1) = true by simp; omega]
    simp only [Bool.or_true, show p - (1 + padLen.j x m) = 0 by omega]
    rfl

/-- `M` as SymCrypt's byte string. -/
def toB (M : List Byte) : 𝔹 M.length := ⟨M.toArray, rfl⟩

theorem getElem_bytesToBits_toB (M : List Byte) (i : Nat) (hi : i < 8 * M.length) :
    (bytesToBits (toB M))[i] = M[i / 8]!.toNat.testBit (i % 8) := by
  simp only [bytesToBits, toB, Vector.getElem_ofFn, Vector.getElem_mk, List.getElem_toArray]
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

theorem beq_true_of {a c : Nat} (h : a = c) : (a == c) = true := by simp [h]
theorem beq_false_of {a c : Nat} (h : a ≠ c) : (a == c) = false := by simp [h]

/-- The padded message's bits are the bytes `keccakPad` writes. -/
theorem getElem_padded (R ℓ : Nat) (hR : 0 < R) (d : Byte) (sfx : Vector Bool ℓ) (hℓ : ℓ + 2 ≤ 8)
    (hd : ∀ t < 8, d.toNat.testBit t = if h : t < ℓ then sfx[t] else decide (t = ℓ))
    (M : List Byte) (i : Nat) (hi : i < 8 * M.length + ℓ + padLen (8 * R) (8 * M.length + ℓ)) :
    ((bytesToBits (toB M) ‖ sfx) ‖ «pad10*1» (8 * R) (8 * M.length + ℓ))[i] =
      (keccakPad R d M)[i / 8]!.toNat.testBit (i % 8) := by
  have hpl := padLen_eq R M.length ℓ hR hℓ
  have hq := Nat.mod_lt M.length hR
  have hplen : 2 ≤ padLen (8 * R) (8 * M.length + ℓ) := by simp only [padLen]; omega
  rw [testBit_keccakPad R hR d M (i / 8) (i % 8) (by omega) (by omega), getElem_vappend _ _ _ hi]
  split
  · rename_i h1
    rw [getElem_vappend _ _ _ h1]
    split
    · rename_i h2
      rw [getElem_bytesToBits_toB _ _ h2, ite_eq_left (by omega), beq_false_of (by omega), Bool.false_and,
        Bool.bne_false]
    · rename_i h2
      rw [ite_eq_right (by omega), beq_true_of (by omega), beq_false_of (show i % 8 ≠ 7 by omega),
        Bool.and_false, Bool.bne_false, hd _ (by omega), dite_eq_left (by omega), Bool.true_and]
      congr 1; omega
  · rename_i h1
    rw [getElem_pad101 _ _ _ (by omega), ite_eq_right (by omega)]
    by_cases h2 : i / 8 = M.length
    · rw [beq_true_of h2, hd _ (by omega), dite_eq_right (by omega), Bool.true_and]
      by_cases h3 : i % 8 = ℓ
      · rw [beq_true_of (show i - (8 * M.length + ℓ) = 0 by omega),
          beq_false_of (show i % 8 ≠ 7 by omega), Bool.and_false]
        simp [h3]
      · rw [beq_false_of (show i - (8 * M.length + ℓ) ≠ 0 by omega)]
        simp only [h3, decide_false, Bool.false_or, Bool.false_bne]
        by_cases h4 : i = 8 * M.length + ℓ + padLen (8 * R) (8 * M.length + ℓ) - 1
        · rw [beq_true_of (by omega), beq_true_of (show i / 8 = M.length + (R - M.length % R) - 1 by
            omega), beq_true_of (show i % 8 = 7 by omega)]
          rfl
        · rw [beq_false_of (by omega)]
          by_cases h5 : i / 8 = M.length + (R - M.length % R) - 1
          · rw [beq_true_of h5, beq_false_of (show i % 8 ≠ 7 by omega)]
            rfl
          · rw [beq_false_of h5]
            rfl
    · rw [beq_false_of h2, Bool.false_and, Bool.false_bne,
        beq_false_of (show i - (8 * M.length + ℓ) ≠ 0 by omega), Bool.false_or]
      by_cases h4 : i = 8 * M.length + ℓ + padLen (8 * R) (8 * M.length + ℓ) - 1
      · rw [beq_true_of (by omega), beq_true_of (show i / 8 = M.length + (R - M.length % R) - 1 by
          omega), beq_true_of (show i % 8 = 7 by omega)]
        rfl
      · rw [beq_false_of (by omega)]
        by_cases h5 : i / 8 = M.length + (R - M.length % R) - 1
        · rw [beq_true_of h5, beq_false_of (show i % 8 ≠ 7 by omega)]
          rfl
        · rw [beq_false_of h5]
          rfl

/-! ## The sponge is FIPS 202's -/

/-- Bit `j` of SymCrypt's `SPONGE` on the suffixed message is bit `j` of `sponge`'s bytes. -/
theorem getElem_SPONGE (R ℓ r : Nat) (hR : 0 < R) (hr8 : r = 8 * R) (d : Byte)
    (sfx : Vector Bool ℓ) (hℓ : ℓ + 2 ≤ 8)
    (hd : ∀ t < 8, d.toNat.testBit t = if h : t < ℓ then sfx[t] else decide (t = ℓ))
    (M : List Byte) (n : Nat) (h1 : 0 < r ∧ r < b) (h2 : r ≤ b) (j : Nat) (hj : j < 8 * n) :
    (SPONGE KECCAK_f r (bytesToBits (toB M) ‖ sfx) (8 * n) h1 h2)[j] =
      (sponge R d M n)[j / 8]!.toNat.testBit (j % 8) := by
  subst hr8
  have hpl := padLen_eq R M.length ℓ hR hℓ
  have hS : SPONGE KECCAK_f (8 * R) (bytesToBits (toB M) ‖ sfx) (8 * n) h1 h2 =
      SPONGE.squeeze KECCAK_f (8 * R) (#v[] : Vector Bool 0) (SPONGE.absorb KECCAK_f (8 * R)
        ((bytesToBits (toB M) ‖ sfx) ‖ «pad10*1» (8 * R) (8 * M.length + ℓ))
        (padLen_dvd _ _) h1.1) h1 := rfl
  rw [hS, getElem_squeeze _ _ _ _ _ hj, dite_eq_right (Nat.not_lt_zero _)]
  rw [← bitsOf_absorb R hR (keccakPad R d M) _ (by rw [length_keccakPad R hR, ← hpl])
    (fun i hi => getElem_padded R ℓ hR d sfx hℓ hd M i hi)]
  rw [← bitsOf_iterate_keccakF]
  simp only [bitsOf, Vector.getElem_ofFn, Nat.sub_zero, sponge, squeeze]
  generalize absorb R (List.replicate 200 0) (keccakPad R d M) = S
  have hm : ((List.range n).map fun k => (keccakF^[k / R] S)[k % R]!)[j / 8]! =
      (keccakF^[j / 8 / R] S)[j / 8 % R]! := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  rw [hm, Nat.mod_mul, ← Nat.div_div_eq_div_mul, show (j % 8 + 8 * (j / 8 % R)) / 8 = j / 8 % R by omega,
    show (j % 8 + 8 * (j / 8 % R)) % 8 = j % 8 by omega]

/-- The bytes of SymCrypt's `KECCAK[c]` on the suffixed message are `sponge`'s,
`c` twice the rate's complement. -/
theorem bitsToBytes_KECCAK (R ℓ : Nat) (hR : 8 < R ∧ R < 200) (d : Byte) (sfx : Vector Bool ℓ)
    (hℓ : ℓ + 2 ≤ 8)
    (hd : ∀ t < 8, d.toNat.testBit t = if h : t < ℓ then sfx[t] else decide (t = ℓ))
    (M : List Byte) (n : Nat) (hc : 0 < 1600 - 8 * R ∧ 1600 - 8 * R < 1536) :
    (bitsToBytes (KECCAK (1600 - 8 * R) (bytesToBits (toB M) ‖ sfx) (8 * n) hc)).toList =
      sponge R d M n := by
  apply List.ext_getElem (by simp [sponge, squeeze])
  intro k hk1 hk2
  simp only [Vector.length_toList] at hk1
  rw [Vector.getElem_toList]
  apply Byte.ext_testBit
  intro t ht
  rw [bitsToBytes_testBit _ _ hk1 _ ht, KECCAK,
    getElem_SPONGE R ℓ _ (by omega) (by omega) d sfx hℓ hd M n _ _ _ (by omega),
    show (8 * k + t) / 8 = k by omega, show (8 * k + t) % 8 = t by omega,
    List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk2]
  rfl

theorem sha3Pad_testBit : ∀ t < 8, sha3Pad.toNat.testBit t =
    if h : t < 2 then hashSuffix[t] else decide (t = 2) := by decide

theorem shakePad_testBit : ∀ t < 8, shakePad.toNat.testBit t =
    if h : t < 4 then xofSuffix[t] else decide (t = 4) := by decide

/-- SHA3-256 is FIPS 202's. -/
theorem sha3_256_eq (M : List Byte) : sha3_256 M = (Spec.SHA3.sha3_256 (toB M)).toList :=
  (bitsToBytes_KECCAK 136 2 (by omega) sha3Pad hashSuffix (by omega) sha3Pad_testBit M 32
    (by omega)).symm

/-- SHA3-384 is FIPS 202's. -/
theorem sha3_384_eq (M : List Byte) : sha3_384 M = (Spec.SHA3.sha3_384 (toB M)).toList :=
  (bitsToBytes_KECCAK 104 2 (by omega) sha3Pad hashSuffix (by omega) sha3Pad_testBit M 48
    (by omega)).symm

/-- SHA3-512 is FIPS 202's. -/
theorem sha3_512_eq (M : List Byte) : sha3_512 M = (Spec.SHA3.sha3_512 (toB M)).toList :=
  (bitsToBytes_KECCAK 72 2 (by omega) sha3Pad hashSuffix (by omega) sha3Pad_testBit M 64
    (by omega)).symm

/-- SHAKE128 is FIPS 202's. -/
theorem shake128_eq (M : List Byte) (n : Nat) :
    shake128 M n = (Spec.SHA3.shake128 (toB M) n).toList :=
  (bitsToBytes_KECCAK 168 4 (by omega) shakePad xofSuffix (by omega) shakePad_testBit M n
    (by omega)).symm

/-- SHAKE256 is FIPS 202's. -/
theorem shake256_eq (M : List Byte) (n : Nat) :
    shake256 M n = (Spec.SHA3.shake256 (toB M) n).toList :=
  (bitsToBytes_KECCAK 136 4 (by omega) shakePad xofSuffix (by omega) shakePad_testBit M n
    (by omega)).symm

end rind.spec
