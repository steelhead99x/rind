-- Adapted from pyca/verified-garbage (https://github.com/pyca/verified-garbage),
-- `lean/VerifiedGarbage/Spec/ChaCha20.lean` at 0aa40d6c21fd02943fe5b38a5b69b6213d07764d.
-- Copyright (c) Individual contributors.
-- SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
import Rind.S2nChaCha20Poly1305
import Rind.AesKw
open rind.spec

/-!
# pyca/verified-garbage's ChaCha20 spec

The RFC 8439 spec of ChaCha20 in pyca/verified-garbage's (VG's)
`Spec/ChaCha20.lean`, which VG's theorems about its streaming routines state
their results against (`Spec/ChaCha20/Contract.lean`), at the commit
`admin/import-vg` pins. `admin/import-vg-models` vendors both under
`proofs/verified-garbage/`, so a pin that changes them shows the change in its
diff, and that re-pin must review this file against the new text: no check
compares the two. VG's spec is Lean already, so the cipher's definitions
are its text. Those over memory read the streaming state's 768 bytes `st`
instead: VG's `m (p + i)`, for the state at `p`, is `st[i]!`, and its
little-endian `Mem.read` and `Mem.readW` read `st` from an offset. The
theorems here prove what rind's proof of the routines' Rust needs: that the
keystream VG's `init` sets up, XORed into a message, is `Rind.Spec`'s
`chacha20.encrypt`, and that the state holds as many bytes of keystream as
its count says.
-/

namespace rind.spec.vg

/-- A 32-bit word. -/
abbrev Word := BitVec 32

/-- The sixteen 32-bit words of a ChaCha state (§2.2), in the order of the
RFC's 4×4 matrix (row by row). -/
abbrev State := Vector Word 16

/-- §2.1's quarter round. -/
def quarterRound (a b c d : Word) : Word × Word × Word × Word :=
  let a := a + b; let d := (d ^^^ a).rotateLeft 16
  let c := c + d; let b := (b ^^^ c).rotateLeft 12
  let a := a + b; let d := (d ^^^ a).rotateLeft 8
  let c := c + d; let b := (b ^^^ c).rotateLeft 7
  (a, b, c, d)

/-- §2.2, `QUARTERROUND(x, y, z, w)`: the quarter round on the words of the
state at indices `x, y, z, w`, leaving the others alone. -/
def qround (s : State) (x y z w : Fin 16) : State :=
  let (a, b, c, d) := quarterRound s[x] s[y] s[z] s[w]
  ((((s.set x a).set y b).set z c).set w d)

/-- The four constant words `0x61707865, 0x3320646e, 0x79622d32, 0x6b206574`. -/
def constants : Vector Word 4 := #v[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

/-- §2.3.1, `inner_block`: a column round followed by a diagonal round. -/
def innerBlock (s : State) : State :=
  let s := qround s 0 4 8 12
  let s := qround s 1 5 9 13
  let s := qround s 2 6 10 14
  let s := qround s 3 7 11 15
  let s := qround s 0 5 10 15
  let s := qround s 1 6 11 12
  let s := qround s 2 7 8 13
  qround s 3 4 9 14

/-- §2.3: the ChaCha20 block function on a state: 20 rounds (10 iterations
of `innerBlock`), then the original state added word by word. -/
def block (s : State) : State :=
  Vector.zipWith (· + ·) (Nat.repeat innerBlock 10 s) s

/-- §2.3: serialize a state by sequencing its words in little-endian order. -/
def serialize (s : State) : List (BitVec 8) :=
  s.toList.flatMap fun x => [x.extractLsb' 0 8, x.extractLsb' 8 8, x.extractLsb' 16 8, x.extractLsb' 24 8]

/-- Word `j` of a byte string read as little-endian 32-bit integers. -/
def wordLE (bs : List (BitVec 8)) (j : Nat) : Word :=
  (bs.getD (4 * j + 3) 0 ++ bs.getD (4 * j + 2) 0 ++ bs.getD (4 * j + 1) 0 ++ bs.getD (4 * j) 0 : Word)

/-- §2.3: the initial state from a 256-bit key, a 32-bit block counter and a
96-bit nonce. -/
def initState (key : List (BitVec 8)) (counter : Word) (nonce : List (BitVec 8)) : State :=
  Vector.ofFn fun i =>
    if i.1 < 4 then constants.getD i.1 0
    else if i.1 < 12 then wordLE key (i.1 - 4)
    else if i.1 = 12 then counter
    else wordLE nonce (i.1 - 13)

/-- §2.3.1, `chacha20_block(key, counter, nonce)`: 64 bytes of keystream. -/
def chacha20Block (key : List (BitVec 8)) (counter : Word) (nonce : List (BitVec 8)) : List (BitVec 8) :=
  serialize (block (initState key counter nonce))

/-- The whole keystream for the 256-bit key `key` and the 16-byte `nonce`,
the initial 32-bit block counter `c` followed by the 96-bit nonce: the
blocks for the counters `c` to 2³² − 1. -/
def keystreamOf (key nonce : List (BitVec 8)) : List (BitVec 8) :=
  let c := wordLE nonce 0
  (List.range (2 ^ 32 - c.toNat)).flatMap fun j =>
    chacha20Block key (c + BitVec.ofNat 32 j) (nonce.drop 4)

/-! ## The streaming state

VG's definitions over the memory `m` and the state's address `p`, over the
state's bytes `st`. -/

/-- `Mem.read`: the little-endian read of `n` bytes from offset `a`. -/
def read (st : List (BitVec 8)) (a : Nat) : (n : Nat) → BitVec (8 * n)
  | 0 => 0#0
  | n + 1 => (read st (a + 1) n ++ st[a]! : BitVec (8 * n + 8))

/-- `Mem.readW`: the little-endian read of a `w`-bit value from offset `a`
(`w` a multiple of 8). -/
def readW (st : List (BitVec 8)) (a w : Nat) : BitVec w := (read st a (w / 8)).setWidth w

/-- `stateAt`: the 16-word state at the start of the streaming state. -/
def stateAt (st : List (BitVec 8)) : State :=
  Vector.ofFn fun j => readW st (4 * j.1) 32

/-- The first `n` bytes of the keystream from the state `s`: the serialized
blocks of `s` with the counter (word 12) advanced by `j = 0, 1, …`. -/
def keystream (s : State) (n : Nat) : List (BitVec 8) :=
  ((List.range ((n + 63) / 64)).flatMap fun j =>
    serialize (block (s.set 12 (s[12] + BitVec.ofNat 32 j)))).take n

/-- `bytesAt`: the `n` bytes from offset `a`. -/
def bytesAt (st : List (BitVec 8)) (a n : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => st[a + i]!

/-- `keyAt`: the streaming state's key, its bytes 16 to 47. -/
def keyAt (st : List (BitVec 8)) : List (BitVec 8) := bytesAt st 16 32

/-- `leftAt`: the number of bytes of keystream left, bytes 128 to 135. -/
def leftAt (st : List (BitVec 8)) : Nat := (readW st 128 64).toNat

/-- `restAt`: the keystream left, `leftAt st = n` bytes long: the last
`n % 64` bytes of the block at bytes 64 to 127, then the first
`64 * (n / 64)` bytes of the keystream of the 16-word state at bytes 0 to 63. -/
def restAt (st : List (BitVec 8)) : List (BitVec 8) :=
  let n := leftAt st
  bytesAt st (128 - n % 64) (n % 64) ++ keystream (stateAt st) (64 * (n / 64))

/-! ## The keystream is `Rind.Spec`'s -/

theorem length_serialize (s : State) : (serialize s).length = 64 := by
  simp [serialize, List.length_flatMap]

theorem length_keystream (s : State) (n : Nat) : (keystream s n).length = n := by
  rw [keystream, List.length_take, List.length_flatMap]
  simp only [length_serialize, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  omega

theorem length_bytesAt (st : List (BitVec 8)) (a n : Nat) : (bytesAt st a n).length = n := by
  simp [bytesAt]

/-- The state holds as many bytes of keystream as its count says. -/
theorem length_restAt (st : List (BitVec 8)) : (restAt st).length = leftAt st := by
  rw [restAt, List.length_append, length_bytesAt, length_keystream]
  omega

theorem qround_toList (s : State) (x y z w : Fin 16) :
    (qround s x y z w).toList = chacha20.quarterRound s.toList x y z w := by
  have hg : ∀ i : Fin 16, s.toList[i.1]! = s[i] := fun i => by
    rw [getElem!_pos _ _ (by simp)]; simp
  simp only [qround, quarterRound, chacha20.quarterRound, chacha20.qr, hg, Vector.toList_set, Fin.getElem_fin]

theorem innerBlock_toList (s : State) : (innerBlock s).toList = chacha20.innerBlock s.toList := by
  simp only [innerBlock, chacha20.innerBlock, qround_toList, Fin.isValue]
  rfl

theorem repeat_toList (s : State) (n : Nat) :
    (Nat.repeat innerBlock n s).toList = chacha20.innerBlock^[n] s.toList := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.repeat, innerBlock_toList, ih, Function.iterate_succ_apply']

/-- A word's little-endian bytes, as `serialize` writes them. -/
theorem toLEBytes_eq (x : Word) :
    x.toLEBytes = [x.extractLsb' 0 8, x.extractLsb' 8 8, x.extractLsb' 16 8, x.extractLsb' 24 8] := by
  have hl : x.toLEBytes.length = 4 := by simp [BitVec.toLEBytes_length]
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [BitVec.getElem_toLEBytes_eq_getElem _ _ _ h1 hj (by omega)]
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals (simp [BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_eq_getElem (by omega)])

theorem serialize_eq (s : State) : serialize s = s.toList.flatMap BitVec.toLEBytes := by
  rw [serialize]
  congr 1
  funext x
  exact (toLEBytes_eq x).symm

theorem getLsbD_fromLEBytes (m : List (BitVec 8)) (k : Nat) :
    (BitVec.fromLEBytes m).getLsbD k = (m[k / 8]!).getLsbD (k % 8) := by
  have := BitVec.fromLEBytes_getElem! m k
  rw [BitVec.getElem!_eq_testBit_toNat] at this
  rw [← BitVec.testBit_toNat, this]
  rfl

/-- Four bytes concatenated, most significant first, are `le32` of them. -/
theorem append4_eq (a b c d : BitVec 8) : (d ++ c ++ b ++ a : Word) = chacha20.le32 a b c d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e : (chacha20.le32 a b c d).getLsbD i = ([a, b, c, d][i / 8]!).getLsbD (i % 8) :=
    getLsbD_fromLEBytes _ _
  rw [e]
  obtain h | h | h | h : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 := by omega
  all_goals
    simp only [h, BitVec.getLsbD_append]
    simp
    split_ifs <;> first | omega | (congr 1; omega)

/-- `wordLE` is `Rind.Spec`'s `le32`. -/
theorem wordLE_eq (bs : List (BitVec 8)) (j : Nat) :
    wordLE bs j = chacha20.le32 bs[4 * j]! bs[4 * j + 1]! bs[4 * j + 2]! bs[4 * j + 3]! := by
  rw [wordLE, append4_eq]
  simp only [List.getD_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
  rfl

theorem words_getElem (bs : List (BitVec 8)) (n i : Nat) (hn : bs.length = 4 * n) (hi : i < n) :
    (chacha20.words bs)[i]! = wordLE bs i := by
  rw [wordLE_eq]
  simp [chacha20.words, hn, hi]

theorem initState_toList (key : List (BitVec 8)) (counter : Word) (nonce : List (BitVec 8))
    (hk : key.length = 32) (hn : nonce.length = 12) :
    (initState key counter nonce).toList =
      [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] ++ chacha20.words key ++ [counter] ++
        chacha20.words nonce := by
  have hwk : (chacha20.words key).length = 8 := by simp [chacha20.words, hk]
  have hwn : (chacha20.words nonce).length = 3 := by simp [chacha20.words, hn]
  apply List.ext_getElem (by simp [hwk, hwn])
  intro i h1 h2
  simp only [Vector.length_toList] at h1
  simp only [Vector.getElem_toList, initState, Vector.getElem_ofFn]
  rw [← getElem!_pos _ i h2]
  obtain h | h | h | h : i < 4 ∨ (4 ≤ i ∧ i < 12) ∨ i = 12 ∨ 12 < i := by omega
  · obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals rfl
  · simp only [show ¬ i < 4 by omega, h.2, ↓reduceIte]
    rw [List.append_assoc, List.append_assoc,
      List.getElem!_append_right _ _ _ (by simp only [List.length_cons, List.length_nil]; omega),
      List.getElem!_append_left _ _ _ (by simp only [List.length_cons, List.length_nil, hwk]; omega)]
    norm_num only [List.length_cons, List.length_nil]
    rw [words_getElem key 8 (i - 4) hk (by omega)]
  · subst h
    rw [List.getElem!_append_left _ _ _ (by simp [hwk]),
      List.getElem!_append_right _ _ _ (by simp [hwk])]
    simp [hwk]
  · simp only [show ¬ i < 4 by omega, show ¬ i < 12 by omega, show ¬ i = 12 by omega, ↓reduceIte]
    rw [List.getElem!_append_right _ _ _
      (by simp only [List.length_append, List.length_cons, List.length_nil, hwk]; omega)]
    norm_num only [List.length_append, List.length_cons, List.length_nil, hwk]
    rw [words_getElem nonce 3 _ hn (by omega)]

/-- `chacha20_block` is `Rind.Spec`'s, for a 32-byte key and a 12-byte nonce. -/
theorem chacha20Block_eq (key : List (BitVec 8)) (counter : Word) (nonce : List (BitVec 8))
    (hk : key.length = 32) (hn : nonce.length = 12) :
    chacha20Block key counter nonce = chacha20.block key counter nonce := by
  rw [chacha20Block, chacha20.block, serialize_eq, block, Vector.toList_zipWith, repeat_toList,
    initState_toList _ _ _ hk hn]

theorem zipWith_take_length {α β γ : Type} (f : α → β → γ) (l : List α) (A : List β) :
    List.zipWith f l (A.take l.length) = List.zipWith f l A := by
  induction l generalizing A with
  | nil => simp
  | cons a l ih => cases A <;> simp [ih]

/-- The keystream VG's `init` sets up, XORed into a message no longer than it,
is RFC 8439's encryption under its key, initial block counter, and nonce. -/
theorem keystreamOf_encrypt (key nonce msg : List (BitVec 8)) (hk : key.length = 32)
    (hn : nonce.length = 16) (hm : msg.length ≤ (keystreamOf key nonce).length) :
    List.zipWith (· ^^^ ·) msg ((keystreamOf key nonce).take msg.length) =
      chacha20.encrypt key (wordLE nonce 0) (nonce.drop 4) msg := by
  have hn' : (nonce.drop 4).length = 12 := by simp [hn]
  have hg : ∀ j, (chacha20.block key (wordLE nonce 0 + BitVec.ofNat 32 j) (nonce.drop 4)).length = 64 :=
    fun j => s2n.length_block _ _ _ hk hn'
  have hks : keystreamOf key nonce = (List.range (2 ^ 32 - (wordLE nonce 0).toNat)).flatMap
      fun j => chacha20.block key (wordLE nonce 0 + BitVec.ofNat 32 j) (nonce.drop 4) := by
    simp only [keystreamOf, chacha20Block_eq _ _ _ hk hn']
  have hlen : (keystreamOf key nonce).length = 64 * (2 ^ 32 - (wordLE nonce 0).toNat) := by
    rw [hks, List.length_flatMap]
    simp [hg, List.sum_replicate, Nat.mul_comm]
  rw [zipWith_take_length, hks, s2n.zipWith_flatMap _ _ hg, chacha20.encrypt]
  -- The blocks past the message's last XOR nothing.
  set M := (msg.length + 63) / 64
  set N := 2 ^ 32 - (wordLE nonce 0).toNat
  have hMN : M ≤ N := by rw [hlen] at hm; omega
  rw [show N = M + (N - M) by omega, List.range_add, List.flatMap_append]
  conv => rhs; rw [← List.append_nil (List.flatMap _ _)]
  congr 1
  rw [List.flatMap_eq_nil_iff]
  intro j hj
  simp only [List.mem_map, List.mem_range] at hj
  obtain ⟨k, -, rfl⟩ := hj
  have : msg.length ≤ 64 * (M + k) := by omega
  simp [List.drop_eq_nil_of_le this]

theorem length_keystreamOf (key nonce : List (BitVec 8)) (hk : key.length = 32) (hn : nonce.length = 16) :
    (keystreamOf key nonce).length = 64 * (2 ^ 32 - (wordLE nonce 0).toNat) := by
  have hn' : (nonce.drop 4).length = 12 := by simp [hn]
  simp only [keystreamOf, List.length_flatMap, chacha20Block_eq _ _ _ hk hn', s2n.length_block _ _ _ hk hn']
  simp [List.sum_replicate, Nat.mul_comm]

/-! ## Words as memory holds them -/

/-- A word's bytes, as `serialize` writes them, read back as a word. -/
theorem le32_extract (x : Word) :
    chacha20.le32 (x.extractLsb' 0 8) (x.extractLsb' 8 8) (x.extractLsb' 16 8) (x.extractLsb' 24 8) = x := by
  rw [← append4_eq]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  split_ifs <;> (rw [← BitVec.getLsbD_eq_getElem]; congr 1; omega)

/-- A word's little-endian bytes read back as a word. -/
theorem wordLE_toLEBytes (x : Word) : wordLE x.toLEBytes 0 = x := by
  rw [wordLE_eq, toLEBytes_eq]
  simpa using le32_extract x

/-- Byte `4 * j + k` of words written out little-endian is byte `k` of word `j`. -/
theorem flatMap_toLEBytes_getElem! (ws : List Word) (j k : Nat) (hj : j < ws.length) (hk : k < 4) :
    (ws.flatMap BitVec.toLEBytes)[4 * j + k]! = (ws[j]!.toLEBytes)[k]! := by
  induction ws generalizing j with
  | nil => simp at hj
  | cons w ws ih =>
    have hw : w.toLEBytes.length = 4 := by simp [BitVec.toLEBytes_length]
    rw [List.flatMap_cons]
    cases j with
    | zero => simp [List.getElem!_append_left _ _ k (by omega : k < w.toLEBytes.length)]
    | succ j =>
      rw [List.getElem!_append_right _ _ _ (by rw [hw]; omega), hw,
        show 4 * (j + 1) + k - 4 = 4 * j + k by omega, ih j (by simp at hj; omega)]
      simp

theorem length_flatMap_toLEBytes (ws : List Word) : (ws.flatMap BitVec.toLEBytes).length = 4 * ws.length := by
  simp [List.length_flatMap, BitVec.toLEBytes_length, List.sum_replicate, Nat.mul_comm]

/-- Words written out little-endian read back as those words. -/
theorem wordLE_flatMap (ws : List Word) (j : Nat) (hj : j < ws.length) :
    wordLE (ws.flatMap BitVec.toLEBytes) j = ws[j]! := by
  have h0 := flatMap_toLEBytes_getElem! ws j 0 hj (by omega)
  rw [Nat.add_zero] at h0
  rw [wordLE_eq, flatMap_toLEBytes_getElem! ws j 1 hj (by omega),
    flatMap_toLEBytes_getElem! ws j 2 hj (by omega), flatMap_toLEBytes_getElem! ws j 3 hj (by omega), h0,
    toLEBytes_eq]
  simpa using le32_extract ws[j]!

theorem words_flatMap (ws : List Word) : chacha20.words (ws.flatMap BitVec.toLEBytes) = ws := by
  have hl := length_flatMap_toLEBytes ws
  apply List.ext_getElem (by simp [chacha20.words, hl])
  intro i h1 h2
  rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2,
    words_getElem _ ws.length i hl h2, wordLE_flatMap ws i h2]

/-- Bytes read as words and written back out little-endian are those bytes. -/
theorem flatMap_words (b : List (BitVec 8)) (n : Nat) (hb : b.length = 4 * n) :
    (chacha20.words b).flatMap BitVec.toLEBytes = b := by
  have hw : (chacha20.words b).length = n := by simp [chacha20.words, hb]
  have hl := length_flatMap_toLEBytes (chacha20.words b)
  apply List.ext_getElem (by rw [hl, hw, hb])
  intro i h1 h2
  rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2]
  obtain ⟨j, k, hk, rfl⟩ : ∃ j k, k < 4 ∧ i = 4 * j + k := ⟨i / 4, i % 4, by omega, by omega⟩
  rw [flatMap_toLEBytes_getElem! _ j k (by rw [hw]; omega) hk, words_getElem b n j hb (by omega),
    wordLE_eq, chacha20.le32, rind.vale.toLEBytes_fromLEBytes]
  obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  all_goals simp

/-! ## RFC 8439's encryption in pieces -/

theorem length_encrypt (key : List (BitVec 8)) (counter : Word) (nonce msg : List (BitVec 8))
    (hk : key.length = 32) (hn : nonce.length = 12) :
    (chacha20.encrypt key counter nonce msg).length = msg.length := by
  rw [chacha20.encrypt, List.length_flatMap]
  have : ∀ j, (List.zipWith (· ^^^ ·) ((msg.drop (64 * j)).take 64)
      (chacha20.block key (counter + BitVec.ofNat 32 j) nonce)).length = min (msg.length - 64 * j) 64 := by
    intro j; rw [Nat.min_comm]; simp [s2n.length_block _ _ _ hk hn]
  simp only [this]
  generalize msg.length = L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    rcases Nat.lt_or_ge L 64 with h | h
    · rcases Nat.eq_zero_or_pos L with rfl | h0
      · simp
      · rw [show (L + 63) / 64 = 1 by omega]; simp; omega
    · have := ih (L - 64) (by omega)
      rw [show (L + 63) / 64 = (L - 64 + 63) / 64 + 1 by omega, List.range_succ_eq_map]
      simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
      rw [show (List.map (fun x => min (L - 64 * (x + 1)) 64) (List.range ((L - 64 + 63) / 64))) =
          List.map (fun x => min (L - 64 - 64 * x) 64) (List.range ((L - 64 + 63) / 64)) by
        apply List.map_congr_left; intro x _; congr 1; omega, this]
      omega

/-- Encrypting a message that starts with whole blocks encrypts those, then
the rest from the block counter past them. -/
theorem encrypt_append (key : List (BitVec 8)) (counter : Word) (nonce m1 m2 : List (BitVec 8))
    (q : Nat) (hq : m1.length = 64 * q) :
    chacha20.encrypt key counter nonce (m1 ++ m2) =
      chacha20.encrypt key counter nonce m1 ++
        chacha20.encrypt key (counter + BitVec.ofNat 32 q) nonce m2 := by
  simp only [chacha20.encrypt, List.length_append, hq]
  rw [show (64 * q + m2.length + 63) / 64 = q + (m2.length + 63) / 64 by omega, List.range_add,
    List.flatMap_append, show (64 * q + 63) / 64 = q by omega, List.flatMap_map]
  congr 1
  · apply List.flatMap_congr
    intro j hj
    rw [List.mem_range] at hj
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  · apply List.flatMap_congr
    intro j _
    rw [show 64 * (q + j) = m1.length + 64 * j by omega, List.drop_append,
      List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left, BitVec.ofNat_add,
      BitVec.add_assoc]

end rind.spec.vg
