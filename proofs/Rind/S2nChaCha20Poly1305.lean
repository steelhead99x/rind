import Rind.Bytes
open rind.spec

/-!
# rind's HOL Light ChaCha20-Poly1305 spec

The RFC 8439 spec of ChaCha20, Poly1305, and AEAD_CHACHA20_POLY1305 in
`thirdparty/s2n-bignum/common/chacha20poly1305.ml`, which rind's HOL
Light proofs of aws-lc's routines state their results against, with
s2n-bignum's `num_of_bytelist` and `bytelist_of_num` (`common/words2.ml`) and
HOL Light's `MAP2` (`lists.ml`) it uses, transliterated:
HOL Light's `EL n l` is `l[n]!`, `SUB_LIST (m,n) l` is `(l.drop m).take n`,
`list_of_seq f n` is `(List.range n).map f`, `ITLIST f l b` is `l.foldr f b`,
`REPLICATE` is `List.replicate`, `APPEND` is `++`, `word_rol` is `rotateLeft`,
`word_add`, `word_xor`, and `word_and` are `+`, `^^^`, and `&&&`, `word n` is
`BitVec.ofNat` and `val` is `toNat`, a boolean `=` is `decide`, and a
recursion on `SUC n` is one on `n + 1`. The theorems here prove each is
`Rind.Spec`'s.
-/

namespace rind.spec.s2n

/-- `num_of_bytelist`: the number little-endian bytes encode. -/
def numOfBytelist : List (BitVec 8) → Nat
  | [] => 0
  | h :: t => h.toNat + 256 * numOfBytelist t

/-- `bytelist_of_num`: `k` little-endian bytes of `n`. -/
def bytelistOfNum : Nat → Nat → List (BitVec 8)
  | 0, _ => []
  | k + 1, n => BitVec.ofNat 8 (n % 256) :: bytelistOfNum k (n / 256)

/-- `MAP2`: `f` over `l1` and the same positions of `l2`. HOL Light leaves
`HD []` and `TL []` unspecified, here `default` and `[]`; the spec runs it
only where `l2` is at least as long. -/
def map2 {α β γ : Type} [Inhabited β] (f : α → β → γ) : List α → List β → List γ
  | [], _ => []
  | h :: t, l => f h l.head! :: map2 f t l.tail

/-- `chacha20_quarter_round`. -/
def chacha20QuarterRound : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 →
    BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32
  | (a, b, c, d) =>
    let a := a + b
    let d := (d ^^^ a).rotateLeft 16
    let c := c + d
    let b := (b ^^^ c).rotateLeft 12
    let a := a + b
    let d := (d ^^^ a).rotateLeft 8
    let c := c + d
    let b := (b ^^^ c).rotateLeft 7
    (a, b, c, d)

/-- `chacha20_double_round`. -/
def chacha20DoubleRound (s : List (BitVec 32)) : List (BitVec 32) :=
  let (x0, x4, x8, x12) := chacha20QuarterRound (s[0]!, s[4]!, s[8]!, s[12]!)
  let (x1, x5, x9, x13) := chacha20QuarterRound (s[1]!, s[5]!, s[9]!, s[13]!)
  let (x2, x6, x10, x14) := chacha20QuarterRound (s[2]!, s[6]!, s[10]!, s[14]!)
  let (x3, x7, x11, x15) := chacha20QuarterRound (s[3]!, s[7]!, s[11]!, s[15]!)
  let (x0, x5, x10, x15) := chacha20QuarterRound (x0, x5, x10, x15)
  let (x1, x6, x11, x12) := chacha20QuarterRound (x1, x6, x11, x12)
  let (x2, x7, x8, x13) := chacha20QuarterRound (x2, x7, x8, x13)
  let (x3, x4, x9, x14) := chacha20QuarterRound (x3, x4, x9, x14)
  [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15]

/-- `chacha20_rounds`. -/
def chacha20Rounds : Nat → List (BitVec 32) → List (BitVec 32)
  | 0, s => s
  | n + 1, s => chacha20DoubleRound (chacha20Rounds n s)

/-- `chacha20_words`. -/
def chacha20Words (n : Nat) (b : List (BitVec 8)) : List (BitVec 32) :=
  (List.range n).map fun i => BitVec.ofNat 32 (numOfBytelist ((b.drop (4 * i)).take 4))

/-- `chacha20_state`. -/
def chacha20State (key : List (BitVec 8)) (counter : BitVec 32) (nonce : List (BitVec 8)) :
    List (BitVec 32) :=
  [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] ++
    (chacha20Words 8 key ++ (counter :: chacha20Words 3 nonce))

/-- `chacha20_block`. -/
def chacha20Block (key : List (BitVec 8)) (counter : BitVec 32) (nonce : List (BitVec 8)) :
    List (BitVec 8) :=
  let s := chacha20State key counter nonce
  (map2 (· + ·) (chacha20Rounds 10 s) s).foldr (fun w l => bytelistOfNum 4 w.toNat ++ l) []

/-- `chacha20_keystream`. -/
def chacha20Keystream (key : List (BitVec 8)) (counter : BitVec 32) (nonce : List (BitVec 8)) :
    Nat → List (BitVec 8)
  | 0 => []
  | n + 1 => chacha20Keystream key counter nonce n ++
    chacha20Block key (counter + BitVec.ofNat 32 n) nonce

/-- `chacha20_encrypt`. -/
def chacha20Encrypt (key : List (BitVec 8)) (counter : BitVec 32) (nonce msg : List (BitVec 8)) :
    List (BitVec 8) :=
  map2 (· ^^^ ·) msg (chacha20Keystream key counter nonce ((msg.length + 63) / 64))

/-- `p_1305`. -/
def p1305 : Nat := 2 ^ 130 - 5

/-- `poly1305_clamp`. -/
def poly1305Clamp (r : Nat) : Nat :=
  (BitVec.ofNat 128 r &&& BitVec.ofNat 128 0x0ffffffc0ffffffc0ffffffc0fffffff).toNat

/-- `poly1305_acc`. -/
def poly1305Acc (r : Nat) (msg : List (BitVec 8)) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let b := (msg.drop (16 * n)).take 16
    ((poly1305Acc r msg n + numOfBytelist b + 2 ^ (8 * b.length)) * r) % p1305

/-- `poly1305_mac`. -/
def poly1305Mac (key msg : List (BitVec 8)) : List (BitVec 8) :=
  let r := poly1305Clamp (numOfBytelist ((key.drop 0).take 16))
  let s := numOfBytelist ((key.drop 16).take 16)
  bytelistOfNum 16 (poly1305Acc r msg ((msg.length + 15) / 16) + s)

/-- `chacha20_poly1305_key_gen`. -/
def chacha20Poly1305KeyGen (key nonce : List (BitVec 8)) : List (BitVec 8) :=
  ((chacha20Block key 0 nonce).drop 0).take 32

/-- `chacha20_poly1305_pad16`. -/
def chacha20Poly1305Pad16 (x : List (BitVec 8)) : List (BitVec 8) :=
  List.replicate ((16 - x.length % 16) % 16) 0

/-- `chacha20_poly1305_mac_data`. -/
def chacha20Poly1305MacData (aad ct : List (BitVec 8)) : List (BitVec 8) :=
  aad ++ (chacha20Poly1305Pad16 aad ++ (ct ++ (chacha20Poly1305Pad16 ct ++
    (bytelistOfNum 8 aad.length ++ bytelistOfNum 8 ct.length))))

/-- `chacha20_poly1305_tag`. -/
def chacha20Poly1305Tag (key nonce aad ct : List (BitVec 8)) : List (BitVec 8) :=
  poly1305Mac (chacha20Poly1305KeyGen key nonce) (chacha20Poly1305MacData aad ct)

/-- `chacha20_poly1305_seal`. -/
def chacha20Poly1305Seal (key nonce aad msg : List (BitVec 8)) : List (BitVec 8) × List (BitVec 8) :=
  let ct := chacha20Encrypt key 1 nonce msg
  (ct, chacha20Poly1305Tag key nonce aad ct)

/-- `chacha20_poly1305_open`. -/
def chacha20Poly1305Open (key nonce aad ct tag : List (BitVec 8)) : List (BitVec 8) × Bool :=
  (chacha20Encrypt key 1 nonce ct, decide (chacha20Poly1305Tag key nonce aad ct = tag))

/-! ## Bytes and numbers -/

theorem numOfBytelist_eq (l : List (BitVec 8)) : numOfBytelist l = poly1305.leNum l := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [numOfBytelist, poly1305.leNum, Nat.ofDigits_cons, ih]

theorem length_bytelistOfNum (k n : Nat) : (bytelistOfNum k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [bytelistOfNum, ih]

theorem leNum_bytelistOfNum (k n : Nat) : poly1305.leNum (bytelistOfNum k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [bytelistOfNum, poly1305.leNum, Nat.mod_one]
  | succ k ih =>
    have := ih (n / 256)
    simp only [poly1305.leNum] at this
    simp only [bytelistOfNum, poly1305.leNum, List.map_cons, Nat.ofDigits_cons, this,
      BitVec.toNat_ofNat, pow_succ', Nat.mod_mul]
    omega

theorem digits_lt (l : List (BitVec 8)) : ∀ x ∈ l.map BitVec.toNat, x < 256 := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨a, -, rfl⟩ := hx
  exact a.isLt

/-- Byte lists of one length are equal when they encode the same number. -/
theorem eq_of_leNum_eq {l1 l2 : List (BitVec 8)} (hl : l1.length = l2.length)
    (h : poly1305.leNum l1 = poly1305.leNum l2) : l1 = l2 := by
  have hd := Nat.ofDigits_inj_of_len_eq (b := 256) (by norm_num) (by simpa using hl)
    (digits_lt l1) (digits_lt l2) h
  exact List.map_injective_iff.mpr (fun a b hab => BitVec.eq_of_toNat_eq hab) hd

theorem bytelistOfNum_eq (k n : Nat) : bytelistOfNum k n = (BitVec.ofNat (8 * k) n).toLEBytes := by
  apply eq_of_leNum_eq
  · simp [length_bytelistOfNum]; omega
  · rw [leNum_bytelistOfNum, poly1305.leNum, ofDigits_toLEBytes, BitVec.toNat_ofNat, pow_mul]
    norm_num

theorem length_map2 {α β γ : Type} [Inhabited β] (f : α → β → γ) (l1 : List α) (l2 : List β) :
    (map2 f l1 l2).length = l1.length := by
  induction l1 generalizing l2 with
  | nil => rfl
  | cons h t ih => simp [map2, ih]

theorem map2_eq {α β γ : Type} [Inhabited β] (f : α → β → γ) (l1 : List α) (l2 : List β)
    (h : l1.length ≤ l2.length) : map2 f l1 l2 = List.zipWith f l1 l2 := by
  induction l1 generalizing l2 with
  | nil => rfl
  | cons a t ih =>
    match l2, h with
    | b :: l2, h => simp [map2, ih l2 (by simp at h; omega)]

/-! ## The ChaCha20 block function -/

theorem chacha20QuarterRound_eq (a b c d : BitVec 32) :
    chacha20QuarterRound (a, b, c, d) = chacha20.qr a b c d := rfl

theorem chacha20DoubleRound_eq (s : List (BitVec 32)) (hs : s.length = 16) :
    chacha20DoubleRound s = chacha20.innerBlock s := by
  match s, hs with
  | [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15], _ =>
    simp only [chacha20DoubleRound, chacha20QuarterRound_eq, chacha20.innerBlock, chacha20.quarterRound,
      List.getElem!_cons_zero, List.getElem!_cons_succ, List.set_cons_zero, List.set_cons_succ]

theorem length_innerBlock (s : List (BitVec 32)) : (chacha20.innerBlock s).length = s.length := by
  simp [chacha20.innerBlock, chacha20.quarterRound]

theorem chacha20Rounds_eq (s : List (BitVec 32)) (hs : s.length = 16) (n : Nat) :
    chacha20Rounds n s = chacha20.innerBlock^[n] s ∧ (chacha20Rounds n s).length = 16 := by
  induction n with
  | zero => exact ⟨rfl, hs⟩
  | succ n ih =>
    rw [chacha20Rounds, Function.iterate_succ_apply', ← ih.1, chacha20DoubleRound_eq _ ih.2]
    exact ⟨rfl, by rw [length_innerBlock, ih.2]⟩

/-- Four bytes from `4 * i` on, where the list holds them. -/
theorem take_four {l : List (BitVec 8)} {i : Nat} (h : 4 * i + 4 ≤ l.length) :
    (l.drop (4 * i)).take 4 = [l[4 * i]!, l[4 * i + 1]!, l[4 * i + 2]!, l[4 * i + 3]!] := by
  apply List.ext_getElem (by simp; omega)
  intro j h1 _
  simp only [List.length_take, List.length_drop] at h1
  rw [getElem!_pos l (4 * i) (by omega), getElem!_pos l (4 * i + 1) (by omega),
    getElem!_pos l (4 * i + 2) (by omega), getElem!_pos l (4 * i + 3) (by omega)]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> simp

theorem le32_eq (b0 b1 b2 b3 : BitVec 8) :
    BitVec.ofNat 32 (numOfBytelist [b0, b1, b2, b3]) = chacha20.le32 b0 b1 b2 b3 := by
  apply BitVec.eq_of_toNat_eq
  have h : (chacha20.le32 b0 b1 b2 b3).toNat = poly1305.leNum [b0, b1, b2, b3] :=
    toNat_fromLEBytes [b0, b1, b2, b3]
  have hl : poly1305.leNum [b0, b1, b2, b3] < 256 ^ 4 :=
    Nat.ofDigits_lt_base_pow_length (by norm_num) (digits_lt _)
  rw [h, BitVec.toNat_ofNat, numOfBytelist_eq]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_eq hl (by norm_num))

theorem chacha20Words_eq (n : Nat) (b : List (BitVec 8)) (hb : b.length = 4 * n) :
    chacha20Words n b = chacha20.words b := by
  rw [chacha20Words, chacha20.words, show b.length / 4 = n by omega]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [take_four (by omega), le32_eq]

theorem length_chacha20State (key : List (BitVec 8)) (counter : BitVec 32) (nonce : List (BitVec 8)) :
    (chacha20State key counter nonce).length = 16 := by
  simp [chacha20State, chacha20Words]

theorem chacha20State_eq (key : List (BitVec 8)) (counter : BitVec 32) (nonce : List (BitVec 8))
    (hk : key.length = 32) (hn : nonce.length = 12) :
    chacha20State key counter nonce = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] ++
      chacha20.words key ++ [counter] ++ chacha20.words nonce := by
  rw [chacha20State, chacha20Words_eq 8 key hk, chacha20Words_eq 3 nonce hn]
  simp

theorem foldr_bytelistOfNum (ws : List (BitVec 32)) :
    ws.foldr (fun w l => bytelistOfNum 4 w.toNat ++ l) [] = ws.flatMap BitVec.toLEBytes := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.foldr_cons, ih, List.flatMap_cons, bytelistOfNum_eq]
    congr 1
    exact congrArg BitVec.toLEBytes (BitVec.ofNat_toNat 32 w |>.trans (BitVec.setWidth_eq w))

/-- `chacha20_block` is `Rind.Spec`'s, for a 32-byte key and a 12-byte nonce. -/
theorem chacha20Block_eq (key : List (BitVec 8)) (counter : BitVec 32) (nonce : List (BitVec 8))
    (hk : key.length = 32) (hn : nonce.length = 12) :
    chacha20Block key counter nonce = chacha20.block key counter nonce := by
  have hs := length_chacha20State key counter nonce
  obtain ⟨hr, hl⟩ := chacha20Rounds_eq _ hs 10
  rw [chacha20Block]
  rw [map2_eq _ _ _ (by rw [hl, hs]), foldr_bytelistOfNum, hr, chacha20State_eq _ _ _ hk hn]
  rfl

theorem length_block (key : List (BitVec 8)) (counter : BitVec 32) (nonce : List (BitVec 8))
    (hk : key.length = 32) (hn : nonce.length = 12) :
    (chacha20.block key counter nonce).length = 64 := by
  have hs := length_chacha20State key counter nonce
  rw [← chacha20Block_eq _ _ _ hk hn, chacha20Block, foldr_bytelistOfNum, List.length_flatMap]
  simp [BitVec.toLEBytes_length, length_map2, (chacha20Rounds_eq _ hs 10).2]

/-! ## ChaCha20 encryption -/

/-- The pairs of `l` with `A ++ B` are those of its first `A.length` with `A`,
then those of the rest with `B`. -/
theorem zipWith_append_right {α β γ : Type} (f : α → β → γ) (l : List α) (A B : List β) :
    List.zipWith f l (A ++ B) =
      List.zipWith f (l.take A.length) A ++ List.zipWith f (l.drop A.length) B := by
  induction A generalizing l with
  | nil => simp
  | cons a A ih =>
    match l with
    | [] => simp
    | x :: l => simp [ih]

theorem zipWith_take_left {α β γ : Type} (f : α → β → γ) (l : List α) (A : List β) :
    List.zipWith f (l.take A.length) A = List.zipWith f l A := by
  induction A generalizing l with
  | nil => simp
  | cons a A ih =>
    match l with
    | [] => simp
    | x :: l => simp [ih]

/-- A message XOR a stream of 64-byte blocks is each 64 bytes of it XOR its block. -/
theorem zipWith_flatMap (f : BitVec 8 → BitVec 8 → BitVec 8) (g : Nat → List (BitVec 8))
    (hg : ∀ j, (g j).length = 64) (msg : List (BitVec 8)) (n : Nat) :
    List.zipWith f msg ((List.range n).flatMap g) =
      (List.range n).flatMap fun j => List.zipWith f ((msg.drop (64 * j)).take 64) (g j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hl : ((List.range n).flatMap g).length = 64 * n := by
      rw [List.length_flatMap]
      simp [hg, List.sum_replicate, Nat.mul_comm]
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, zipWith_append_right, hl,
      ← hl, zipWith_take_left, ih, hl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [← zipWith_take_left f (List.drop (64 * n) msg), hg]

theorem chacha20Keystream_eq (key : List (BitVec 8)) (counter : BitVec 32) (nonce : List (BitVec 8))
    (hk : key.length = 32) (hn : nonce.length = 12) (n : Nat) :
    chacha20Keystream key counter nonce n =
      (List.range n).flatMap fun j => chacha20.block key (counter + BitVec.ofNat 32 j) nonce := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [chacha20Keystream, ih, List.range_succ, List.flatMap_append, chacha20Block_eq _ _ _ hk hn]
    simp

/-- `chacha20_encrypt` is `Rind.Spec`'s, for a 32-byte key and a 12-byte nonce. -/
theorem chacha20Encrypt_eq (key : List (BitVec 8)) (counter : BitVec 32) (nonce msg : List (BitVec 8))
    (hk : key.length = 32) (hn : nonce.length = 12) :
    chacha20Encrypt key counter nonce msg = chacha20.encrypt key counter nonce msg := by
  have hg : ∀ j, (chacha20.block key (counter + BitVec.ofNat 32 j) nonce).length = 64 :=
    fun j => length_block _ _ _ hk hn
  rw [chacha20Encrypt, chacha20Keystream_eq _ _ _ hk hn, map2_eq, zipWith_flatMap _ _ hg]
  · rfl
  · rw [List.length_flatMap]
    simp [hg, List.sum_replicate]
    omega

/-! ## Poly1305 -/

theorem poly1305Clamp_eq (r : Nat) : poly1305Clamp r = poly1305.clamp r := by
  rw [poly1305Clamp, poly1305.clamp, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases hi : i < 128
  · simp [hi]
  · have : (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat).testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num : (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat) < 2 ^ 128)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hi, this]

theorem poly1305Acc_eq (r : Nat) (msg : List (BitVec 8)) (n : Nat) :
    poly1305Acc r msg n = (List.range n).foldl (fun a i =>
      let block := (msg.drop (16 * i)).take 16
      (a + poly1305.leNum block + 2 ^ (8 * block.length)) * r % poly1305.p) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [poly1305Acc, ih, List.range_succ, List.foldl_append]
    simp [numOfBytelist_eq, p1305, poly1305.p]

/-- `poly1305_mac` is `Rind.Spec`'s, for a 32-byte key. -/
theorem poly1305Mac_eq (key msg : List (BitVec 8)) (hk : key.length = 32) :
    poly1305Mac key msg = poly1305.mac key msg := by
  simp only [poly1305Mac, poly1305.mac, poly1305Acc_eq, poly1305Clamp_eq, numOfBytelist_eq,
    bytelistOfNum_eq, List.drop_zero, List.take_of_length_le (by simp [hk] : (key.drop 16).length ≤ 16)]

/-! ## ChaCha20-Poly1305 -/

theorem chacha20Poly1305KeyGen_eq (key nonce : List (BitVec 8)) (hk : key.length = 32)
    (hn : nonce.length = 12) :
    chacha20Poly1305KeyGen key nonce = chacha20poly1305.otk key nonce := by
  rw [chacha20Poly1305KeyGen, chacha20Block_eq _ _ _ hk hn, List.drop_zero]
  rfl

theorem chacha20Poly1305MacData_eq (aad ct : List (BitVec 8)) :
    chacha20Poly1305MacData aad ct = chacha20poly1305.macData aad ct := by
  simp [chacha20Poly1305MacData, chacha20poly1305.macData, chacha20Poly1305Pad16,
    chacha20poly1305.pad16, bytelistOfNum_eq]

/-- `chacha20_poly1305_tag` is the tag `Rind.Spec`'s AEAD computes, for a
32-byte key and a 12-byte nonce. -/
theorem chacha20Poly1305Tag_eq (key nonce aad ct : List (BitVec 8)) (hk : key.length = 32)
    (hn : nonce.length = 12) :
    chacha20Poly1305Tag key nonce aad ct =
      poly1305.mac (chacha20poly1305.otk key nonce) (chacha20poly1305.macData aad ct) := by
  have hl : (chacha20poly1305.otk key nonce).length = 32 := by
    simp [chacha20poly1305.otk, length_block _ _ _ hk hn]
  rw [chacha20Poly1305Tag, chacha20Poly1305KeyGen_eq _ _ hk hn, chacha20Poly1305MacData_eq,
    poly1305Mac_eq _ _ hl]

/-- `chacha20_poly1305_seal` is `Rind.Spec`'s, for a 32-byte key and a
12-byte nonce. -/
theorem chacha20Poly1305Seal_eq (key nonce aad msg : List (BitVec 8)) (hk : key.length = 32)
    (hn : nonce.length = 12) :
    chacha20Poly1305Seal key nonce aad msg = chacha20poly1305.seal key nonce aad msg := by
  rw [chacha20Poly1305Seal, chacha20poly1305.seal, chacha20Encrypt_eq _ _ _ _ hk hn,
    chacha20Poly1305Tag_eq _ _ _ _ hk hn]

/-- `chacha20_poly1305_open` is `Rind.Spec`'s, for a 32-byte key and a
12-byte nonce. -/
theorem chacha20Poly1305Open_eq (key nonce aad ct tag : List (BitVec 8)) (hk : key.length = 32)
    (hn : nonce.length = 12) :
    chacha20Poly1305Open key nonce aad ct tag = chacha20poly1305.open key nonce aad ct tag := by
  rw [chacha20Poly1305Open, chacha20poly1305.open, chacha20Encrypt_eq _ _ _ _ hk hn,
    chacha20Poly1305Tag_eq _ _ _ _ hk hn]
  congr 1
  by_cases h : poly1305.mac (chacha20poly1305.otk key nonce) (chacha20poly1305.macData aad ct) = tag <;>
    simp [h]

end rind.spec.s2n
