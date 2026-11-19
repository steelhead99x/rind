import Rind.AesModes
import Rind.Core
open Aeneas Aeneas.Std Result rind.vale rind.simd

/-!
# SP 800-38A's modes on blocks and counters

What both targets' proofs of AES-CTR and AES-CBC share, and `admin/prove`'s
copies of `Rind.X86_64.AesModesApi` use: the counter blocks CTR's big-endian
counter reaches, CBC's chaining over whole blocks as a routine's per-block
theorem states it, and `as_chunks_mut`'s chunks. Nothing here is a target's.
-/

namespace rind.modes

/-! ## Big-endian counters -/

theorem be32_eq (c : Nat) : be32 c =
    [BitVec.ofNat 8 (c / 2 ^ 24), BitVec.ofNat 8 (c / 2 ^ 16), BitVec.ofNat 8 (c / 2 ^ 8), BitVec.ofNat 8 c] := by
  simp [be32, be128, List.range_succ]

theorem length_be32 (c : Nat) : (be32 c).length = 4 := by simp [be32_eq]

theorem length_be128 (c : Nat) : (be128 c).length = 16 := by simp [be128]

theorem ofBe_foldl (l : List (BitVec 8)) (a : Nat) :
    l.foldl (fun a b => 256 * a + b.toNat) a = a * 256 ^ l.length + ofBe l := by
  induction l generalizing a with
  | nil => simp [ofBe]
  | cons b l ih =>
    simp only [List.foldl_cons, ofBe] at ih ⊢
    rw [ih, ih (256 * 0 + b.toNat), List.length_cons, pow_succ]
    ring

theorem ofBe_append (l1 l2 : List (BitVec 8)) : ofBe (l1 ++ l2) = ofBe l1 * 256 ^ l2.length + ofBe l2 := by
  rw [ofBe, List.foldl_append, ofBe_foldl]; rfl

theorem ofBe_cons (b : BitVec 8) (l : List (BitVec 8)) : ofBe (b :: l) = b.toNat * 256 ^ l.length + ofBe l := by
  rw [show b :: l = [b] ++ l from rfl, ofBe_append]; simp [ofBe]

theorem ofBe_lt (l : List (BitVec 8)) : ofBe l < 256 ^ l.length := by
  induction l with
  | nil => simp [ofBe]
  | cons b l ih =>
    rw [ofBe_cons, List.length_cons, pow_succ]
    have hb : b.toNat < 256 := b.isLt
    have hb' : b.toNat * 256 ^ l.length + 256 ^ l.length ≤ 256 ^ l.length * 256 := by
      rw [← Nat.succ_mul, Nat.mul_comm]; exact Nat.mul_le_mul_left _ hb
    omega

theorem ofBe_be32 (c : Nat) : ofBe (be32 c) = c % 2 ^ 32 := by
  rw [be32_eq]
  simp only [ofBe, List.foldl_cons, List.foldl_nil, BitVec.toNat_ofNat]
  omega

/-- Byte `i` of a big-endian number is its digit `i`. -/
theorem ofBe_digit : ∀ (l : List (BitVec 8)) (i : Nat), i < l.length →
    ofBe l / 256 ^ (l.length - 1 - i) % 256 = (l[i]!).toNat
  | [], i, h => absurd h (by simp)
  | b :: l, 0, _ => by
    rw [ofBe_cons]
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem!_cons_zero]
    have hR := ofBe_lt l
    have hp : 0 < 256 ^ l.length := by positivity
    have hb : b.toNat < 256 := b.isLt
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hR, Nat.zero_add, Nat.mod_eq_of_lt hb]
  | b :: l, i + 1, h => by
    have hi : i < l.length := by simp at h; omega
    rw [ofBe_cons, List.getElem!_cons_succ, ← ofBe_digit l i hi]
    simp only [List.length_cons]
    rw [show l.length + 1 - 1 - (i + 1) = l.length - 1 - i by omega]
    have hp : 0 < 256 ^ (l.length - 1 - i) := by positivity
    have e : b.toNat * 256 ^ l.length = (256 * (b.toNat * 256 ^ i)) * 256 ^ (l.length - 1 - i) := by
      rw [show l.length = (i + 1) + (l.length - 1 - i) by omega, pow_add, pow_succ]
      simp only [show i + 1 + (l.length - 1 - i) - 1 - i = l.length - 1 - i by omega]
      ring
    rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.add_mul_mod_self_left]

theorem be128_ofBe (l : List (BitVec 8)) (hl : l.length = 16) : be128 (ofBe l) = l := by
  apply List.ext_getElem (by simp [be128, hl])
  intro i h1 h2
  have hi : i < 16 := by simpa [be128] using h1
  have hd := ofBe_digit l i (by omega)
  rw [hl, show 16 - 1 - i = 15 - i by omega] at hd
  simp only [be128, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, show (2 : Nat) ^ 8 = 256 from rfl, hd]
  simp [h2]

/-- SP 800-38A's counter block `q` after the nonce `n` and the 32-bit count
`c`: the nonce, then `c + q` modulo `2^32`, big-endian. -/
theorem be128_ctrBlock (n : List (BitVec 8)) (hn : n.length = 12) (c q : Nat) :
    be128 (ctrBlock 32 (ofBe (n ++ be32 c)) q) = n ++ be32 ((c + q) % 2 ^ 32) := by
  have key : ctrBlock 32 (ofBe (n ++ be32 c)) q = ofBe (n ++ be32 ((c + q) % 2 ^ 32)) := by
    rw [ofBe_append, ofBe_append, length_be32, length_be32, ofBe_be32, ofBe_be32, ctrBlock,
      show (256 : Nat) ^ 4 = 2 ^ 32 from rfl]
    generalize ofBe n = N
    omega
  rw [key, be128_ofBe _ (by simp [hn, length_be32])]

/-! ## Blocks as bytes -/

theorem leQuad32ToBytes_leBytesToQuad32 (l : List (BitVec 8)) (hl : l.length = 16) :
    leQuad32ToBytes (leBytesToQuad32 l) = l := by
  apply List.ext_getElem (by simp [leQuad32ToBytes, hl])
  intro i h1 h2
  have hi : i < 16 := by simpa [leQuad32ToBytes] using h1
  have := leQuad32ToBytes_getElem! (leBytesToQuad32 l) hi
  rw [byte_leBytesToQuad32 _ hi] at this
  simpa [List.getElem!_eq_getElem?_getD, h1, h2] using this

theorem leBytesToQuad32_leQuad32ToBytes' (q : Quad32) : leBytesToQuad32 (leQuad32ToBytes q) = q := by
  apply eq_of_byte_eq; intro i hi
  rw [byte_leBytesToQuad32 _ hi, leQuad32ToBytes_getElem! _ hi]

theorem leBytesToQuad32_xor (a b : List (BitVec 8)) (ha : a.length = 16) (hb : b.length = 16) :
    leBytesToQuad32 (List.zipWith (· ^^^ ·) a b) = leBytesToQuad32 a ^^^ leBytesToQuad32 b := by
  apply eq_of_byte_eq; intro i hi
  rw [byte_xor, byte_leBytesToQuad32 _ hi, byte_leBytesToQuad32 _ hi, byte_leBytesToQuad32 _ hi]
  simp [ha, hb, hi]

theorem leQuad32ToBytes_xor (x y : Quad32) :
    leQuad32ToBytes (x ^^^ y) = List.zipWith (· ^^^ ·) (leQuad32ToBytes x) (leQuad32ToBytes y) := by
  apply List.ext_getElem (by simp [leQuad32ToBytes])
  intro i h1 h2
  simp only [leQuad32ToBytes, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  exact byte_xor x y i

theorem length_flatMap16 (l : List (Std.Array U8 16#usize)) : (l.flatMap (·.val)).length = 16 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]; omega

theorem getElem!_flatMap16 (l : List (Std.Array U8 16#usize)) {j : Nat} (hj : j < 16 * l.length) :
    (l.flatMap (·.val))[j]! = (l[j / 16]!).val[j % 16]! := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    have ha : a.val.length = 16 := a.property
    rw [List.flatMap_cons]
    by_cases h : j < 16
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by omega), Nat.div_eq_of_lt h,
        Nat.mod_eq_of_lt h]
      simp [List.getElem!_eq_getElem?_getD]
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega), ha,
        ← List.getElem!_eq_getElem?_getD, ih (by simp at hj; omega)]
      have e1 : j / 16 = (j - 16) / 16 + 1 := by omega
      have e2 : j % 16 = (j - 16) % 16 := by omega
      rw [e1, e2]
      simp [List.getElem!_eq_getElem?_getD]

/-! ## CBC's chaining -/

/-- Blocks each the cipher `E` of the input block XORed with the IV, for the
first, or the previous output block, for the rest, are CBC's encryption. -/
theorem cbc_encrypt_chain (alg : Algorithm) (key : List (BitVec 8)) (E : Quad32 → Quad32)
    (hE : ∀ b, E b = aesEncrypt alg (seqNat8ToSeqNat32LE key) b) :
    ∀ (bs rs : List (Std.Array U8 16#usize)) (V : Quad32), rs.length = bs.length →
      (∀ i < bs.length, loadBytes rs[i]!.val =
        E (loadBytes bs[i]!.val ^^^ if i = 0 then V else loadBytes rs[i - 1]!.val)) →
      (rs.flatMap (·.val)).map (·.bv) =
        cbcEncrypt alg key (leQuad32ToBytes V) ((bs.flatMap (·.val)).map (·.bv))
  | [], rs, V, hl, _ => by
    have : rs = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst this
    rw [cbcEncrypt]
    simp
  | b :: bs, rs, V, hl, h => by
    obtain ⟨r, rs', rfl⟩ : ∃ r rs', rs = r :: rs' := by
      cases rs with
      | nil => simp at hl
      | cons r rs' => exact ⟨r, rs', rfl⟩
    have h0 := h 0 (by simp)
    simp only [List.getElem!_cons_zero, ite_true] at h0
    have ih := cbc_encrypt_chain alg key E hE bs rs' (loadBytes r.val) (by simpa using hl)
      (fun i hi => by
        have := h (i + 1) (by simp; omega)
        rcases i with _ | i <;> simpa using this)
    have hbl : (b.val.map (·.bv)).length = 16 := by simp
    have hrl : (r.val.map (·.bv)).length = 16 := by simp
    have hr : r.val.map (·.bv) = leQuad32ToBytes (loadBytes r.val) := by
      rw [loadBytes, leQuad32ToBytes_leBytesToQuad32 _ hrl]
    have hc : aesBlock alg key (List.zipWith (· ^^^ ·) (b.val.map (·.bv)) (leQuad32ToBytes V)) =
        r.val.map (·.bv) := by
      rw [hr, h0, hE, aesBlock, leBytesToQuad32_xor _ _ hbl (by simp [leQuad32ToBytes]),
        leBytesToQuad32_leQuad32ToBytes']
      rfl
    rw [← hr] at ih
    rw [List.flatMap_cons, List.map_append, List.flatMap_cons, List.map_append, cbcEncrypt,
      ite_eq_right (by simp), List.take_left' hbl, List.drop_left' hbl]
    simp only [hc, ih]

/-- Blocks each the inverse cipher `D` of the input block XORed with the IV,
for the first, or the previous input block, for the rest, are CBC's
decryption. -/
theorem cbc_decrypt_chain (alg : Algorithm) (key : List (BitVec 8)) (D : Quad32 → Quad32)
    (hD : ∀ b, D b = aesDecrypt alg (seqNat8ToSeqNat32LE key) b) :
    ∀ (bs rs : List (Std.Array U8 16#usize)) (V : Quad32), rs.length = bs.length →
      (∀ i < bs.length, loadBytes rs[i]!.val =
        D (loadBytes bs[i]!.val) ^^^ if i = 0 then V else loadBytes bs[i - 1]!.val) →
      (rs.flatMap (·.val)).map (·.bv) =
        cbcDecrypt alg key (leQuad32ToBytes V) ((bs.flatMap (·.val)).map (·.bv))
  | [], rs, V, hl, _ => by
    have : rs = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst this
    rw [cbcDecrypt]
    simp
  | b :: bs, rs, V, hl, h => by
    obtain ⟨r, rs', rfl⟩ : ∃ r rs', rs = r :: rs' := by
      cases rs with
      | nil => simp at hl
      | cons r rs' => exact ⟨r, rs', rfl⟩
    have h0 := h 0 (by simp)
    simp only [List.getElem!_cons_zero, ite_true] at h0
    have ih := cbc_decrypt_chain alg key D hD bs rs' (loadBytes b.val) (by simpa using hl)
      (fun i hi => by
        have := h (i + 1) (by simp; omega)
        rcases i with _ | i <;> simpa using this)
    have hbl : (b.val.map (·.bv)).length = 16 := by simp
    have hrl : (r.val.map (·.bv)).length = 16 := by simp
    have hb : b.val.map (·.bv) = leQuad32ToBytes (loadBytes b.val) := by
      rw [loadBytes, leQuad32ToBytes_leBytesToQuad32 _ hbl]
    have hr : r.val.map (·.bv) = leQuad32ToBytes (loadBytes r.val) := by
      rw [loadBytes, leQuad32ToBytes_leBytesToQuad32 _ hrl]
    have hc : List.zipWith (· ^^^ ·) (aesBlockDecrypt alg key (b.val.map (·.bv))) (leQuad32ToBytes V) =
        r.val.map (·.bv) := by
      rw [hr, h0, hD, leQuad32ToBytes_xor, aesBlockDecrypt]
      rfl
    rw [← hb] at ih
    rw [List.flatMap_cons, List.map_append, List.flatMap_cons, List.map_append, cbcDecrypt,
      ite_eq_right (by simp), List.take_left' hbl, List.drop_left' hbl, hc, ih]

/-! ## `as_chunks_mut` and `from_mut` -/

@[step]
theorem as_chunks_mut_spec {T : Type _} (N : Usize) (hN : N.val ≠ 0) (s : Slice T) :
    core.slice.Slice.as_chunks_mut N s ⦃ p back =>
      p.1.length = s.length / N.val ∧
      (∀ i (h : i < p.1.val.length), (p.1.val[i]).val = (s.val.drop (i * N.val)).take N.val) ∧
      p.2.val = s.val.drop (s.length / N.val * N.val) ∧
      ∀ c t, (c.val.flatMap (·.val) ++ t.val).length ≤ Usize.max →
        (back (c, t)).val = c.val.flatMap (·.val) ++ t.val ⦄ := by
  simp only [core.slice.Slice.as_chunks_mut, core.slice.Slice.as_chunks, hN, ite_false, bind_ok, WP.spec_ok]
  refine ⟨by simp [Slice.length], fun i h => by simp [Std.Array.from_val], by simp [Slice.from_val],
    fun c t hl => by simp only; split <;> simp_all [Slice.from_val]⟩

@[step]
theorem from_mut_spec {T : Type _} (x : T) :
    core.slice.raw.from_mut x ⦃ s back => s.val = [x] ∧ ∀ s', back s' = s'.val.headD x ⦄ := by
  simp [core.slice.raw.from_mut, Slice.from_val]

/-- Whole blocks from `as_chunks`, flattened, are the slice's leading bytes. -/
theorem flatMap_chunks (s : List U8) (bs : List (Std.Array U8 16#usize)) (hl : bs.length = s.length / 16)
    (h : ∀ i (h : i < bs.length), (bs[i]).val = (s.drop (i * 16)).take 16) :
    bs.flatMap (·.val) = s.take (s.length / 16 * 16) := by
  apply List.ext_getElem (by rw [length_flatMap16, hl, List.length_take]; omega)
  intro j h1 h2
  rw [length_flatMap16] at h1
  rw [← getElem!_pos, getElem!_flatMap16 _ h1, getElem!_pos bs (j / 16) (by omega), h (j / 16) (by omega)]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop, Nat.mod_lt,
    show j / 16 * 16 + j % 16 = j by omega, show j < s.length by simp at h2; omega]

end rind.modes
