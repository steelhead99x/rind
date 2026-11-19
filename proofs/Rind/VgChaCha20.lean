import Rind.S2nChaCha20Poly1305
import Rind.AesKw
import VerifiedGarbage.Spec.ChaCha20
open rind.spec VG.Spec.ChaCha20

/-!
# pyca/verified-garbage's ChaCha20 spec, against rind's

pyca/verified-garbage's (VG's) RFC 8439 spec, `VerifiedGarbage.Spec.ChaCha20`,
which VG's theorems about its streaming routines state their results against
(`Spec/ChaCha20/Contract.lean`), and which `admin/import-vg-models` vendors
byte for byte at the commit `admin/import-vg` pins. The theorems here prove
what rind's proof of the routines' Rust needs: that the keystream VG's `init`
sets up, XORed into a message, is `Rind.Spec`'s `chacha20.encrypt`; that the
state holds as many bytes of keystream as its count says; and that VG's view
of the streaming state reads only its 768 bytes, so what VG's theorems say of
the state at one address holds wherever memory holds those bytes. They are
over VG's own definitions, so a re-pin that changes those in a way these
proofs cannot absorb fails here.
-/

namespace rind.spec.vg

/-! ## The keystream is `Rind.Spec`'s -/

theorem length_serialize (s : State) : (serialize s).length = 64 := by
  simp [serialize, List.length_flatMap]

theorem length_keystream (s : State) (n : Nat) : (keystream s n).length = n := by
  rw [keystream, List.length_take, List.length_flatMap]
  simp only [length_serialize, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  omega

theorem length_bytesAt (m : VG.Mem) (p : VG.Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

/-- The state holds as many bytes of keystream as its count says. -/
theorem length_restAt (m : VG.Mem) (p : VG.Addr) : (restAt m p).length = leftAt m p := by
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

/-! ## The streaming state's 768 bytes

VG's contracts state the streaming state's key and keystream (`keyAt`,
`leftAt`, `restAt`) over all of memory `m` and the state's address `p`.
These read only the 768 bytes at `p`, the `[u64; 96]` the contracts' `state`
parameter is: memory agreeing there agrees on them. -/

/-- Memory holding the bytes `st` from address 0. -/
def mem (st : List VG.Byte) : VG.Mem := fun a => st[a.toNat]!

/-- `mem st` holds `st` from address 0. -/
theorem bytesAt_mem (st : List VG.Byte) (h : st.length < 2 ^ 64) : bytesAt (mem st) 0 st.length = st := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 h2
  have hi : (0 + BitVec.ofNat 64 i).toNat = i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (0 : VG.Addr).toNat = 0 from rfl]
    omega
  simp only [bytesAt, List.getElem_map, List.getElem_range, mem]
  rw [hi, getElem!_pos st i h2]

/-- Memory that agrees on the 768 bytes at `p` agrees on each of them. -/
theorem eq_of_bytesAt {m m' : VG.Mem} {p : VG.Addr} (h : bytesAt m p 768 = bytesAt m' p 768) (k : Nat)
    (hk : k < 768) : m (p + BitVec.ofNat 64 k) = m' (p + BitVec.ofNat 64 k) := by
  have := congrArg (·[k]?) h
  simpa [bytesAt, hk] using this

/-- Memory that agrees on the state's bytes reads the same value inside them. -/
theorem read_congr {m m' : VG.Mem} {p : VG.Addr} (h : bytesAt m p 768 = bytesAt m' p 768) (a n : Nat)
    (ha : a + n ≤ 768) : m.read (p + BitVec.ofNat 64 a) n = m'.read (p + BitVec.ofNat 64 a) n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [VG.Mem.read]
    have h1 : BitVec.ofNat 64 a + 1 = BitVec.ofNat 64 (a + 1) := by rw [BitVec.ofNat_add]; rfl
    rw [eq_of_bytesAt h a (by omega), BitVec.add_assoc, h1, ih (a + 1) (by omega)]

/-- Memory that agrees on the state's bytes reads the same bytes inside them. -/
theorem bytesAt_congr {m m' : VG.Mem} {p : VG.Addr} (h : bytesAt m p 768 = bytesAt m' p 768) (a n : Nat)
    (ha : a + n ≤ 768) : bytesAt m (p + BitVec.ofNat 64 a) n = bytesAt m' (p + BitVec.ofNat 64 a) n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, eq_of_bytesAt h _ (by omega)]

/-- The key reads only the state's 768 bytes. -/
theorem keyAt_congr {m m' : VG.Mem} {p : VG.Addr} (h : bytesAt m p 768 = bytesAt m' p 768) :
    keyAt m p = keyAt m' p :=
  bytesAt_congr h 16 32 (by omega)

/-- The count of keystream bytes left reads only the state's 768 bytes. -/
theorem leftAt_congr {m m' : VG.Mem} {p : VG.Addr} (h : bytesAt m p 768 = bytesAt m' p 768) :
    leftAt m p = leftAt m' p := by
  simp only [leftAt, VG.Mem.readW]
  rw [show (128 : VG.Addr) = BitVec.ofNat 64 128 from rfl, read_congr h 128 8 (by omega)]

/-- The keystream left reads only the state's 768 bytes. -/
theorem restAt_congr {m m' : VG.Mem} {p : VG.Addr} (h : bytesAt m p 768 = bytesAt m' p 768) :
    restAt m p = restAt m' p := by
  have hs : stateAt m p = stateAt m' p := by
    apply Vector.ext
    intro j hj
    simp only [stateAt, VG.Mem.readW, Vector.getElem_ofFn]
    rw [read_congr h (4 * j) 4 (by omega)]
  simp only [restAt, leftAt_congr h, hs]
  rw [bytesAt_congr h _ _ (by omega)]

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
