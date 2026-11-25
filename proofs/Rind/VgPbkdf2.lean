import Rind.HashSpec
import Rind.Sha2
import VerifiedGarbage.Spec.Pbkdf2.Generic
open Aeneas Aeneas.Std

/-!
# pyca/verified-garbage's SHA-1, SHA-2, HMAC, and PBKDF2 specs are rind's

VG's theorems about its PBKDF2 routines state their results against its own
FIPS 180-4, RFC 2104, and RFC 8018 specs (`Spec/Sha1.lean`, `Spec/Sha256.lean`,
`Spec/Sha512.lean`, `Spec/Hmac.lean`, `Spec/Pbkdf2.lean`), which
`admin/import-vg-models` vendors under `proofs/verified-garbage/`. This proves
each the one `Rind.HashSpec` and `Rind.Sha2` define, so a theorem of VG's is
one about rind's spec: SHA-1 and SHA-256 over spec bytes, SHA-384 and SHA-512
over `U8`s, HMAC over any hash, and PBKDF2 over any pseudorandom function,
refusing a key longer than `2^32 - 1` blocks as VG's does.
-/

namespace rind.spec.vg

/-! ## Message schedules

VG builds a block's schedule newest word first, rind's oldest first: both are
`fwd`'s words, the first reversed. -/

section
variable {α : Type}

/-- The schedule FIPS 180-4 builds from a block's words `M`: `n` more words,
the `t`-th `g` of those before it. -/
def fwd (g : List α → Nat → α) (M : List α) (n : Nat) : List α :=
  (List.range n).foldl (fun W t => W ++ [g W t]) M

theorem fwd_succ (g : List α → Nat → α) (M : List α) (n : Nat) :
    fwd g M (n + 1) = fwd g M n ++ [g (fwd g M n) n] := by
  simp only [fwd, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem fwd_length (g : List α → Nat → α) (M : List α) (n : Nat) :
    (fwd g M n).length = M.length + n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fwd_succ, List.length_append, ih]; rfl

theorem fwd_getElem!_add [Inhabited α] (g : List α → Nat → α) (M : List α) (n k j : Nat)
    (h : j < M.length + n) : (fwd g M (n + k))[j]! = (fwd g M n)[j]! := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : j < (fwd g M (n + k)).length := by rw [fwd_length]; omega
    have h2 : j < (fwd g M (n + k) ++ [g (fwd g M (n + k)) (n + k)]).length := by
      rw [List.length_append]; omega
    rw [← Nat.add_assoc, fwd_succ, getElem!_pos _ j h2, List.getElem_append_left h1,
      ← getElem!_pos _ j h1, ih]

theorem getElem!_reverse [Inhabited α] (L : List α) (i : Nat) (h : i < L.length) :
    L.reverse[i]! = L[L.length - 1 - i]! := by
  rw [getElem!_pos _ i (by simpa using h), getElem!_pos _ _ (by omega), List.getElem_reverse]

/-- A schedule built newest word first, from the block `M` and the step
`step` of the words so far, is `fwd`'s, reversed, where `step` reads the
words `g` does. -/
theorem rev_eq_fwd [Inhabited α] (g : List α → Nat → α) (Ml : List α) (hMl : Ml.length = 16)
    (S : Nat → List α) (step : List α → α) (M : Fin 16 → α) (hM : ∀ j : Fin 16, M j = Ml[j.val]!)
    (h0 : S 0 = []) (hS : ∀ t, S (t + 1) = (if h : t < 16 then M ⟨t, h⟩ else step (S t)) :: S t)
    (hstep : ∀ L : List α, 16 ≤ L.length → step L.reverse = g L (L.length - 16)) :
    ∀ t, S t = ((fwd g Ml (t - 16)).take t).reverse := by
  intro t
  induction t with
  | zero => simp [h0]
  | succ t ih =>
    rw [hS t, ih]
    by_cases ht : t < 16
    · rw [dite_eq_left ht, show t + 1 - 16 = 0 by omega, show t - 16 = 0 by omega, hM]
      simp only [fwd, List.range_zero, List.foldl_nil]
      rw [List.take_add_one, List.reverse_append, List.getElem?_eq_getElem (by omega)]
      simp [getElem!_pos Ml t (by omega)]
    · rw [dite_eq_right ht]
      have hlen : (fwd g Ml (t - 16)).length = t := by rw [fwd_length]; omega
      rw [List.take_of_length_le (by omega), show t + 1 - 16 = t - 16 + 1 by omega, fwd_succ,
        List.take_of_length_le (by simp only [List.length_append, hlen, List.length_singleton]; omega),
        List.reverse_append, hstep _ (by omega), hlen]
      rfl

/-- The `t`-th word of such a schedule, for `t` below `16 + N`. -/
theorem rev_headD [Inhabited α] (g : List α → Nat → α) (Ml : List α) (hMl : Ml.length = 16)
    (S : Nat → List α) (hS : ∀ t, S t = ((fwd g Ml (t - 16)).take t).reverse) (N t : Nat)
    (ht : t < 16 + N) (d : α) : (S (t + 1)).headD d = (fwd g Ml N)[t]! := by
  have hl : t < (fwd g Ml (t + 1 - 16)).length := by rw [fwd_length]; omega
  rw [hS, List.take_add_one, List.reverse_append, List.getElem?_eq_getElem hl]
  simp only [Option.toList_some, List.reverse_singleton, List.cons_append, List.headD_cons]
  rw [← getElem!_pos, show N = (t + 1 - 16) + (N - (t + 1 - 16)) by omega, fwd_getElem!_add _ _ _ _ _
    (by omega)]

end

/-! ## Rounds and blocks -/

/-- Rounds over a `Vector` state are rounds over its list. -/
theorem foldl_toList {α : Type} {n : Nat} (f : Vector α n → Nat → Vector α n)
    (g : List α → Nat → List α) (N : Nat) (hfg : ∀ v t, t < N → (f v t).toList = g v.toList t) :
    ∀ k ≤ N, ∀ v : Vector α n, ((List.range k).foldl f v).toList = (List.range k).foldl g v.toList := by
  intro k
  induction k with
  | zero => intro _ v; rfl
  | succ k ih =>
    intro hk v
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil, hfg _ _ (by omega), ih (by omega)]

/-- VG's hash value after `p`'s whole `B`-byte blocks, each read by index, is
rind's, over `rind.spec.blocks`. -/
theorem compressList_blocks {σ τ : Type} (B : Nat) (hB : 0 < B) (c : σ → (Nat → Byte) → σ)
    (cR : τ → List Byte → τ) (rel : σ → τ)
    (hc : ∀ H (p : List Byte), B ≤ p.length → rel (c H fun k => p.getD k 0) = cR (rel H) (p.take B)) :
    ∀ (p : List Byte) (H : σ), rel ((List.range (p.length / B)).foldl
      (fun H i => c H fun k => p.getD (B * i + k) 0) H) = (blocks B p).foldl cR (rel H) := by
  intro p
  induction h : p.length using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    intro H
    by_cases hp : B ≤ p.length
    · have hd : ∀ i k, p.getD (B * (i + 1) + k) 0 = (p.drop B).getD (B * i + k) 0 := by
        intro i k
        simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
        congr 2; ring
      rw [blocks, ite_eq_left ⟨hB, hp⟩, List.foldl_cons, ← hc H p hp, ← h, Nat.div_eq_sub_div hB hp,
        List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      simp only [Nat.mul_zero, Nat.zero_add, Nat.succ_eq_add_one, hd]
      rw [← List.length_drop]
      exact ih _ (by rw [List.length_drop]; omega) _ rfl _
    · rw [blocks, ite_eq_right (by omega), show n / B = 0 from Nat.div_eq_of_lt (by omega)]
      rfl

/-! ## Bytes and words -/

/-- A bit of the little-endian word of bytes `m`. -/
private theorem getLsbD_fromLEBytes (m : List Byte) (k : Nat) :
    (BitVec.fromLEBytes m).getLsbD k = (m[k / 8]!).getLsbD (k % 8) := by
  have := BitVec.fromLEBytes_getElem! m k
  rw [BitVec.getElem!_eq_testBit_toNat] at this
  rw [← BitVec.testBit_toNat, this]
  rfl

theorem be32_eq (a b c d : Byte) : be32 a b c d = (a ++ b ++ c ++ d : BitVec 32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show (BitVec.cast rfl (BitVec.fromLEBytes [d, c, b, a])).getLsbD i = _
  rw [BitVec.getLsbD_cast, getLsbD_fromLEBytes]
  obtain h | h | h | h : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 := by omega
  all_goals
    simp only [h, BitVec.getLsbD_append]
    simp
    split_ifs <;> first | omega | (congr 1; omega)

/-- A word's big-endian bytes are its bytes from the most significant. -/
theorem toBEBytes_extract {w : Nat} (m : Nat) (hw : w = 8 * m) (x : BitVec w) :
    x.toBEBytes = (List.range m).reverse.map fun i => x.extractLsb' (8 * i) 8 := by
  have hl : x.toLEBytes.length = m := by simp; omega
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  have hi : i < m := by simpa using h2
  apply BitVec.eq_of_getElem_eq
  intro j hj
  simp only [BitVec.toBEBytes, List.getElem_reverse, List.getElem_map, List.getElem_range,
    List.length_range, BitVec.getElem_extractLsb']
  rw [BitVec.getElem_toLEBytes_eq_getElem _ _ _ _ hj (by rw [hl]; omega)]
  congr 1
  rw [hl]

theorem toBEBytes_32 (x : BitVec 32) :
    x.toBEBytes = [x.extractLsb' 24 8, x.extractLsb' 16 8, x.extractLsb' 8 8, x.extractLsb' 0 8] := by
  rw [toBEBytes_extract 4 rfl]; rfl

theorem toBEBytes_64 (x : BitVec 64) :
    x.toBEBytes = (List.range 8).reverse.map fun i => x.extractLsb' (8 * i) 8 :=
  toBEBytes_extract 8 rfl x

theorem words_getElem! (p : List Byte) (hp : 64 ≤ p.length) (j : Fin 16) :
    (words (p.take 64))[j.val]! = (p.getD (4 * j) 0 ++ p.getD (4 * j + 1) 0 ++ p.getD (4 * j + 2) 0 ++
      p.getD (4 * j + 3) 0 : BitVec 32) := by
  have hl : (p.take 64).length = 64 := by simp; omega
  have hb : ∀ r < 4, (p.take 64)[4 * j.val + r]! = p.getD (4 * j + r) 0 := by
    intro r hr
    rw [getElem!_pos _ _ (by rw [hl]; omega), List.getElem_take, List.getD_eq_getElem _ _ (by omega)]
  rw [getElem!_pos _ _ (by simp [words, hl])]
  simp only [words, List.getElem_map, List.getElem_range, hl]
  have h0 := hb 0 (by omega)
  rw [Nat.add_zero] at h0
  rw [be32_eq, h0, hb 1 (by omega), hb 2 (by omega), hb 3 (by omega)]

theorem words_length (p : List Byte) (hp : 64 ≤ p.length) : (words (p.take 64)).length = 16 := by
  simp [words]; omega

theorem pad_eq (m : List Byte) : VG.Spec.Sha256.pad m = pad m := by
  simp only [VG.Spec.Sha256.pad, pad, toBEBytes_64]
  congr 3
  omega

/-! ## SHA-256 -/

/-- The `t`-th word of VG's VG.Spec.Sha256.schedule of a block is rind's. -/
theorem sha256_W (p : List Byte) (hp : 64 ≤ p.length) (t : Nat) (ht : t < 64) :
    VG.Spec.Sha256.W (VG.Spec.Sha256.parseBlock fun k => p.getD k 0) t = (sha256.schedule (words (p.take 64)))[t]! := by
  let g := fun (W : List (BitVec 32)) (t : Nat) =>
    sha256.smallSigma1 W[t + 14]! + W[t + 9]! + sha256.smallSigma0 W[t + 1]! + W[t]!
  have hsched : sha256.schedule (words (p.take 64)) = fwd g (words (p.take 64)) 48 := rfl
  have hrev := rev_eq_fwd g _ (words_length p hp) (VG.Spec.Sha256.schedule (VG.Spec.Sha256.parseBlock fun k => p.getD k 0))
    (fun w => VG.Spec.Sha256.ssig1 w[1]! + w[6]! + VG.Spec.Sha256.ssig0 w[14]! + w[15]!) _
    (fun j => (words_getElem! p hp j).symm) rfl (fun _ => rfl) (by
      intro L hL
      rw [getElem!_reverse L 1 (by omega), getElem!_reverse L 6 (by omega),
        getElem!_reverse L 14 (by omega), getElem!_reverse L 15 (by omega),
        show L.length - 1 - 1 = L.length - 16 + 14 by omega,
        show L.length - 1 - 6 = L.length - 16 + 9 by omega,
        show L.length - 1 - 14 = L.length - 16 + 1 by omega,
        show L.length - 1 - 15 = L.length - 16 by omega]
      rfl)
  rw [VG.Spec.Sha256.W, rev_headD g _ (words_length p hp) _ hrev 48 t (by omega), hsched]

/-- rind's SHA-256 round `t`, over the schedule `W`, as `sha256.compress` runs it. -/
def sha256Round (W s : List (BitVec 32)) (t : Nat) : List (BitVec 32) :=
  let T1 := s[7]! + sha256.bigSigma1 s[4]! + ch s[4]! s[5]! s[6]! + sha256.K[t]! + W[t]!
  let T2 := sha256.bigSigma0 s[0]! + maj s[0]! s[1]! s[2]!
  [T1 + T2, s[0]!, s[1]!, s[2]!, s[3]! + T1, s[4]!, s[5]!, s[6]!]

theorem sha256_compress (H : VG.Spec.Sha256.HashValue) (p : List Byte) (hp : 64 ≤ p.length) :
    (VG.Spec.Sha256.compress H (VG.Spec.Sha256.parseBlock fun k => p.getD k 0)).toList =
      sha256.compress H.toList (p.take 64) := by
  have hR : sha256.compress H.toList (p.take 64) = List.zipWith (· + ·)
      ((List.range 64).foldl (sha256Round (sha256.schedule (words (p.take 64)))) H.toList) H.toList := rfl
  rw [hR, VG.Spec.Sha256.compress, Vector.toList_zipWith, VG.Spec.Sha256.rounds,
    foldl_toList _ _ 64 ?_ 64 (Nat.le_refl _)]
  intro v t ht
  have hv : ∀ i (h : i < 8), v.toList[i]! = v[i] := fun i h => by
    rw [getElem!_pos _ i (by simpa using h), Vector.getElem_toList]
  have hK : VG.Spec.Sha256.K t = sha256.K[t]! := by
    rw [VG.Spec.Sha256.K, List.getD_eq_getElem?_getD, getElem!_def]; rfl
  simp only [VG.Spec.Sha256.round, sha256Round, hv 0 (by omega), hv 1 (by omega), hv 2 (by omega),
    hv 3 (by omega), hv 4 (by omega), hv 5 (by omega), hv 6 (by omega), hv 7 (by omega), hK,
    sha256_W p hp t ht]
  rfl

theorem sha256_eq (m : List Byte) : VG.Spec.Sha256.hash m = sha256.hash m := by
  have hw : VG.Spec.Sha256.wordBytes = BitVec.toBEBytes := funext fun x => (toBEBytes_32 x).symm
  rw [VG.Spec.Sha256.hash, VG.Spec.Sha256.finalHash, pad_eq, sha256.hash, hw]
  congr 1
  exact compressList_blocks 64 (by omega) (fun H b => VG.Spec.Sha256.compress H (VG.Spec.Sha256.parseBlock b)) sha256.compress
    Vector.toList (fun H p hp => sha256_compress H p hp) (pad m) VG.Spec.Sha256.H0


/-! ## SHA-1 -/

theorem sha1_pad_eq (m : List Byte) : VG.Spec.Sha1.pad m = pad m := by
  simp only [VG.Spec.Sha1.pad, pad, toBEBytes_64]
  congr 3
  omega

theorem sha1_W (p : List Byte) (hp : 64 ≤ p.length) (t : Nat) (ht : t < 80) :
    VG.Spec.Sha1.W (VG.Spec.Sha1.parseBlock fun k => p.getD k 0) t =
      (sha1.schedule (words (p.take 64)))[t]! := by
  let g := fun (W : List (BitVec 32)) (t : Nat) =>
    (W[t + 13]! ^^^ W[t + 8]! ^^^ W[t + 2]! ^^^ W[t]!).rotateLeft 1
  have hsched : sha1.schedule (words (p.take 64)) = fwd g (words (p.take 64)) 64 := rfl
  have hrev := rev_eq_fwd g _ (words_length p hp)
    (VG.Spec.Sha1.schedule (VG.Spec.Sha1.parseBlock fun k => p.getD k 0))
    (fun w => (w[2]! ^^^ w[7]! ^^^ w[13]! ^^^ w[15]!).rotateLeft 1) _
    (fun j => (words_getElem! p hp j).symm) rfl (fun _ => rfl) (by
      intro L hL
      rw [getElem!_reverse L 2 (by omega), getElem!_reverse L 7 (by omega),
        getElem!_reverse L 13 (by omega), getElem!_reverse L 15 (by omega),
        show L.length - 1 - 2 = L.length - 16 + 13 by omega,
        show L.length - 1 - 7 = L.length - 16 + 8 by omega,
        show L.length - 1 - 13 = L.length - 16 + 2 by omega,
        show L.length - 1 - 15 = L.length - 16 by omega])
  rw [VG.Spec.Sha1.W, rev_headD g _ (words_length p hp) _ hrev 64 t (by omega), hsched]

/-- rind's SHA-1 round `t`, over the schedule `W`, as `sha1.compress` runs it. -/
def sha1Round (W s : List (BitVec 32)) (t : Nat) : List (BitVec 32) :=
  [s[0]!.rotateLeft 5 + sha1.f t s[1]! s[2]! s[3]! + s[4]! + sha1.K t + W[t]!,
    s[0]!, s[1]!.rotateLeft 30, s[2]!, s[3]!]

theorem sha1_compress (H : VG.Spec.Sha1.HashValue) (p : List Byte) (hp : 64 ≤ p.length) :
    (VG.Spec.Sha1.compress H (VG.Spec.Sha1.parseBlock fun k => p.getD k 0)).toList =
      sha1.compress H.toList (p.take 64) := by
  have hR : sha1.compress H.toList (p.take 64) = List.zipWith (· + ·)
      ((List.range 80).foldl (sha1Round (sha1.schedule (words (p.take 64)))) H.toList) H.toList := rfl
  rw [hR, VG.Spec.Sha1.compress, Vector.toList_zipWith, VG.Spec.Sha1.rounds,
    foldl_toList _ _ 80 ?_ 80 (Nat.le_refl _)]
  intro v t ht
  have hv : ∀ i (h : i < 5), v.toList[i]! = v[i] := fun i h => by
    rw [getElem!_pos _ i (by simpa using h), Vector.getElem_toList]
  simp only [VG.Spec.Sha1.round, sha1Round, hv 0 (by omega), hv 1 (by omega), hv 2 (by omega),
    hv 3 (by omega), hv 4 (by omega), sha1_W p hp t ht]
  rfl

theorem sha1_eq (m : List Byte) : VG.Spec.Sha1.hash m = sha1.hash m := by
  have hw : VG.Spec.Sha1.wordBytes = BitVec.toBEBytes := funext fun x => (toBEBytes_32 x).symm
  rw [VG.Spec.Sha1.hash, sha1_pad_eq, sha1.hash, hw]
  congr 1
  exact compressList_blocks 64 (by omega) (fun H b => VG.Spec.Sha1.compress H (VG.Spec.Sha1.parseBlock b))
    sha1.compress Vector.toList (fun H p hp => sha1_compress H p hp) (pad m) VG.Spec.Sha1.H0

/-! ## SHA-384 and SHA-512

`Rind.Sha2` states these over `U8`s and `U64`s, so the theorems map each to its
`BitVec`. -/

theorem toBEBytes_128 (x : BitVec 128) :
    x.toBEBytes = (List.range 16).reverse.map fun i => x.extractLsb' (8 * i) 8 :=
  toBEBytes_extract 16 rfl x

theorem be64_eq (a0 a1 a2 a3 a4 a5 a6 a7 : Byte) :
    (BitVec.fromBEBytes [a0, a1, a2, a3, a4, a5, a6, a7]).setWidth 64 =
      (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 : BitVec 64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.fromBEBytes, BitVec.getLsbD_cast, getLsbD_fromLEBytes]
  obtain h | h | h | h | h | h | h | h : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 ∨
    i / 8 = 4 ∨ i / 8 = 5 ∨ i / 8 = 6 ∨ i / 8 = 7 := by omega
  all_goals
    simp only [h, BitVec.getLsbD_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    simp [hi]
    split_ifs <;> first | omega | (congr 1; omega)

theorem sha512Pad_map (m : List U8) :
    (sha512Pad m).map (·.bv) = VG.Spec.Sha512.pad (m.map (·.bv)) := by
  simp only [sha512Pad, VG.Spec.Sha512.pad, List.map_append, List.map_cons, List.map_replicate,
    List.length_map, List.map_map, toBEBytes_128, List.append_assoc, List.singleton_append,
    Function.comp_def]
  rfl

theorem blockWords_getElem (q : List U8) (j : Nat) (hj : j < 16) :
    (blockWords q)[j]'(by simp [blockWords]; omega) = beWord ((q.drop (8 * j)).take 8) := by
  simp [blockWords]

/-- A 128-byte block's words, as `blockWords` reads them, are VG's. -/
theorem blockWords_getElem! (p : List U8) (hp : 128 ≤ p.length) (j : Fin 16) :
    ((blockWords (p.take 128)).map (·.bv))[j.val]! =
      VG.Spec.Sha512.parseBlock (fun k => (p.map (·.bv)).getD k 0) j := by
  have hl : (p.take 128).length = 128 := by simp; omega
  have hb : ∀ r < 8, (p.map (·.bv)).getD (8 * j + r) 0 = ((p.take 128)[8 * j.val + r]!).bv := by
    intro r hr
    rw [List.getD_eq_getElem _ _ (by simp; omega), getElem!_pos _ _ (by rw [hl]; omega)]
    simp
  have h8 : ((p.take 128).drop (8 * j.val)).take 8 = (List.range 8).map fun r => (p.take 128)[8 * j.val + r]! := by
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [getElem!_pos _ _ (by rw [hl]; simp at h2; omega)]
    simp
  rw [getElem!_pos _ _ (by simp [blockWords]), List.getElem_map, blockWords_getElem _ _ j.isLt, beWord,
    h8]
  have hq : (List.map (fun r => (p.take 128)[8 * j.val + r]!) (List.range 8)).map (·.bv) =
      [((p.take 128)[8 * j.val]!).bv, ((p.take 128)[8 * j.val + 1]!).bv,
        ((p.take 128)[8 * j.val + 2]!).bv, ((p.take 128)[8 * j.val + 3]!).bv,
        ((p.take 128)[8 * j.val + 4]!).bv, ((p.take 128)[8 * j.val + 5]!).bv,
        ((p.take 128)[8 * j.val + 6]!).bv, ((p.take 128)[8 * j.val + 7]!).bv] := rfl
  have h0 := hb 0 (by omega)
  rw [Nat.add_zero] at h0
  rw [hq, be64_eq, VG.Spec.Sha512.parseBlock, h0, hb 1 (by omega), hb 2 (by omega), hb 3 (by omega),
    hb 4 (by omega), hb 5 (by omega), hb 6 (by omega), hb 7 (by omega)]

theorem sha512_W (p : List U8) (hp : 128 ≤ p.length) (t : Nat) (ht : t < 80) :
    VG.Spec.Sha512.W (VG.Spec.Sha512.parseBlock fun k => (p.map (·.bv)).getD k 0) t =
      (fips512.schedule ((blockWords (p.take 128)).map (·.bv)))[t]! := by
  have hMl : ((blockWords (p.take 128)).map (·.bv)).length = 16 := by simp [blockWords]
  let g := fun (W : List (BitVec 64)) (t : Nat) =>
    fips512.smallSigma1 W[t + 14]! + W[t + 9]! + fips512.smallSigma0 W[t + 1]! + W[t]!
  have hsched : fips512.schedule ((blockWords (p.take 128)).map (·.bv)) =
      fwd g ((blockWords (p.take 128)).map (·.bv)) 64 := rfl
  have hrev := rev_eq_fwd g _ hMl
    (VG.Spec.Sha512.schedule (VG.Spec.Sha512.parseBlock fun k => (p.map (·.bv)).getD k 0))
    (fun w => VG.Spec.Sha512.ssig1 w[1]! + w[6]! + VG.Spec.Sha512.ssig0 w[14]! + w[15]!) _
    (fun j => (blockWords_getElem! p hp j).symm) rfl (fun _ => rfl) (by
      intro L hL
      rw [getElem!_reverse L 1 (by omega), getElem!_reverse L 6 (by omega),
        getElem!_reverse L 14 (by omega), getElem!_reverse L 15 (by omega),
        show L.length - 1 - 1 = L.length - 16 + 14 by omega,
        show L.length - 1 - 6 = L.length - 16 + 9 by omega,
        show L.length - 1 - 14 = L.length - 16 + 1 by omega,
        show L.length - 1 - 15 = L.length - 16 by omega]
      rfl)
  rw [VG.Spec.Sha512.W, rev_headD g _ hMl _ hrev 64 t (by omega), hsched]

/-- rind's SHA-512 round `t`, over the schedule `W`, as `fips512.compressBlock` runs it. -/
def sha512Round (W s : List (BitVec 64)) (t : Nat) : List (BitVec 64) :=
  let T1 := s[7]! + fips512.bigSigma1 s[4]! + fips512.ch s[4]! s[5]! s[6]! + fips512.K[t]! + W[t]!
  let T2 := fips512.bigSigma0 s[0]! + fips512.maj s[0]! s[1]! s[2]!
  [T1 + T2, s[0]!, s[1]!, s[2]!, s[3]! + T1, s[4]!, s[5]!, s[6]!]

theorem sha512_compress (H : VG.Spec.Sha512.HashValue) (h : List U64) (hH : H.toList = h.map (·.bv))
    (p : List U8) (hp : 128 ≤ p.length) :
    (VG.Spec.Sha512.compress H (VG.Spec.Sha512.parseBlock fun k => (p.map (·.bv)).getD k 0)).toList =
      (processBlock h (blockWords (p.take 128))).map (·.bv) := by
  have hR : (processBlock h (blockWords (p.take 128))).map (·.bv) = List.zipWith (· + ·)
      ((List.range 80).foldl (sha512Round (fips512.schedule ((blockWords (p.take 128)).map (·.bv))))
        (h.map (·.bv))) (h.map (·.bv)) := by
    rw [processBlock, List.map_map]
    exact List.map_id _
  rw [hR, ← hH, VG.Spec.Sha512.compress, Vector.toList_zipWith, VG.Spec.Sha512.rounds,
    foldl_toList _ _ 80 ?_ 80 (Nat.le_refl _)]
  intro v t ht
  have hv : ∀ i (h : i < 8), v.toList[i]! = v[i] := fun i h => by
    rw [getElem!_pos _ i (by simpa using h), Vector.getElem_toList]
  have hK : VG.Spec.Sha512.K t = fips512.K[t]! := by
    rw [VG.Spec.Sha512.K, List.getD_eq_getElem?_getD, getElem!_def]; rfl
  simp only [VG.Spec.Sha512.round, sha512Round, hv 0 (by omega), hv 1 (by omega), hv 2 (by omega),
    hv 3 (by omega), hv 4 (by omega), hv 5 (by omega), hv 6 (by omega), hv 7 (by omega), hK,
    sha512_W p hp t ht]
  rfl

theorem sha512_compressList (bytes : List U8) : ∀ (h : List U64) (H : VG.Spec.Sha512.HashValue),
    H.toList = h.map (·.bv) →
    (VG.Spec.Sha512.compressList H (bytes.map (·.bv)) (bytes.length / 128)).toList =
      (compress h bytes).map (·.bv) := by
  induction hn : bytes.length using Nat.strong_induction_on generalizing bytes with
  | _ n ih =>
    intro h H hH
    by_cases hp : 128 ≤ bytes.length
    · have hd : ∀ i k, (bytes.map (·.bv)).getD (128 * (i + 1) + k) 0 =
          ((bytes.drop 128).map (·.bv)).getD (128 * i + k) 0 := by
        intro i k
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop]
        congr 3; ring
      rw [compress, ite_eq_left hp, VG.Spec.Sha512.compressList,
        Nat.div_eq_sub_div (a := n) (b := 128) (by omega) (by omega),
        List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      simp only [Nat.mul_zero, Nat.zero_add, Nat.succ_eq_add_one, hd]
      have := ih (bytes.drop 128).length (by rw [List.length_drop]; omega) (bytes.drop 128) rfl
        (processBlock h (blockWords (bytes.take 128))) _ (sha512_compress H h hH bytes hp)
      rw [VG.Spec.Sha512.compressList, List.length_drop, hn] at this
      exact this
    · rw [compress, ite_eq_right hp, VG.Spec.Sha512.compressList,
        show n / 128 = 0 from Nat.div_eq_of_lt (by omega)]
      exact hH

theorem sha512Words_map (iv : List U64) (H : VG.Spec.Sha512.HashValue) (hH : H.toList = iv.map (·.bv))
    (m : List U8) :
    (sha512Words iv m).map (·.bv) = VG.Spec.Sha512.finalHash H (m.map (·.bv)) := by
  have hw : ∀ x : BitVec 64, VG.Spec.Sha512.wordBytes x = x.toBEBytes := fun x => (toBEBytes_64 x).symm
  rw [VG.Spec.Sha512.finalHash, ← sha512Pad_map, List.length_map,
    sha512_compressList _ iv H hH, sha512Words, List.map_flatMap, List.flatMap_map]
  congr 1
  funext w
  rw [hw, beBytes, List.map_map]
  exact List.map_id _

theorem sha512_eq (m : List U8) :
    VG.Spec.Sha512.sha512 (m.map (·.bv)) = (sha512 m).map (·.bv) :=
  (sha512Words_map sha512Iv VG.Spec.Sha512.H0_512 rfl m).symm

theorem sha384_eq (m : List U8) :
    VG.Spec.Sha512.sha384 (m.map (·.bv)) = (sha384 m).map (·.bv) := by
  rw [VG.Spec.Sha512.sha384, sha384, List.map_take, sha512Words_map sha384Iv VG.Spec.Sha512.H0_384 rfl m]

/-! ## HMAC and PBKDF2 -/

/-- VG's HMAC over a hash of `B`-byte blocks is rind's. -/
theorem hmac_eq (B : Nat) (H : List Byte → List Byte) (key text : List Byte) :
    VG.Spec.Hmac.hmac ⟨B, H⟩ key text = hmac H B key text := by
  simp only [VG.Spec.Hmac.hmac, VG.Spec.Hmac.hmacBlockKey, VG.Spec.Hmac.blockKey,
    VG.Spec.Hmac.xorPad, VG.Spec.Hmac.ipad, VG.Spec.Hmac.opad, hmac]
  by_cases h : key.length ≤ B
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_le h]

theorem int_eq (i : Nat) : VG.Spec.Pbkdf2.int i = (BitVec.ofNat 32 i).toBEBytes := by
  rw [toBEBytes_32, VG.Spec.Pbkdf2.int]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] <;> omega

theorem iterate_eq (prf : List Byte → List Byte) (n : Nat) (u t : List Byte) :
    VG.Spec.Pbkdf2.iterate prf n u t = ((List.range n).foldl
      (fun (acc : List Byte × List Byte) _ => (prf acc.1, List.zipWith (· ^^^ ·) acc.2 (prf acc.1)))
      (u, t)).2 := by
  induction n generalizing u t with
  | zero => rfl
  | succ n ih =>
    rw [VG.Spec.Pbkdf2.iterate, ih, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    rfl

/-- VG's PBKDF2 under the password `P` is rind's, for a derived key of at most
`2^32 - 1` blocks, and refuses a longer one. -/
theorem pbkdf2_eq (prf : List Byte → List Byte → List Byte) (hLen : Nat) (P s : List Byte)
    (c L : Nat) :
    VG.Spec.Pbkdf2.pbkdf2 (prf P) hLen s c L =
      if (2 ^ 32 - 1) * hLen < L then none else some (pbkdf2 prf hLen P s c L) := by
  unfold VG.Spec.Pbkdf2.pbkdf2
  split
  · rfl
  · simp only [pbkdf2, VG.Spec.Pbkdf2.F, int_eq, iterate_eq]

end rind.spec.vg
