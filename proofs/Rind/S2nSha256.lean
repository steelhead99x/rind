import Rind.HashSpec
open rind.spec

/-!
# s2n-bignum's SHA-256 spec

s2n-bignum's FIPS 180-4 spec of SHA-256's block function, from
`x86/proofs/utils/sha256_spec.ml` in awslabs/s2n-bignum#415 at 79120e64,
which rind's fork, `thirdparty/s2n-bignum`, holds, and `arm/proofs/sha256.ml`'s round
functions it reuses, transliterated: HOL Light's `EL n l` is `l[n]!`, `word_ror`
is `rotateRight`, `word_ushr` is `>>>`, and `word_add` is `+`, each grouped as
the HOL Light is. The theorems rind's HOL Light proofs state are about these,
and `block_words` proves this block function is `Rind.HashSpec`'s.
-/

namespace rind.spec.s2n

/-- `sha_msg_sigma_0`. -/
def msgSigma0 (x : BitVec 32) : BitVec 32 := x.rotateRight 7 ^^^ (x.rotateRight 18 ^^^ x >>> 3)
/-- `sha_msg_sigma_1`. -/
def msgSigma1 (x : BitVec 32) : BitVec 32 := x.rotateRight 17 ^^^ (x.rotateRight 19 ^^^ x >>> 10)
/-- `sha_choose`. -/
def choose (x y z : BitVec 32) : BitVec 32 := ((y ^^^ z) &&& x) ^^^ z
/-- `sha_maj`. -/
def maj (x y z : BitVec 32) : BitVec 32 := (x &&& y) ||| ((x ||| y) &&& z)
/-- `sha_hash_sigma_0`. -/
def hashSigma0 (x : BitVec 32) : BitVec 32 := x.rotateRight 2 ^^^ (x.rotateRight 13 ^^^ x.rotateRight 22)
/-- `sha_hash_sigma_1`. -/
def hashSigma1 (x : BitVec 32) : BitVec 32 := x.rotateRight 6 ^^^ (x.rotateRight 11 ^^^ x.rotateRight 25)

/-- `sha256_constants`. -/
def constants : List (BitVec 32) :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- `sha256_msg_schedule`. -/
def msgSchedule (m : List (BitVec 32)) (t : Nat) : BitVec 32 :=
  if t < 16 then m[t]!
  else msgSigma1 (msgSchedule m (t - 2)) + msgSchedule m (t - 7) +
    (msgSigma0 (msgSchedule m (t - 15)) + msgSchedule m (t - 16))
termination_by t
decreasing_by all_goals omega

/-- `sha256_round`. -/
def round (hsh : List (BitVec 32)) (k w : BitVec 32) : List (BitVec 32) :=
  let a := hsh[0]!; let b := hsh[1]!; let c := hsh[2]!; let d := hsh[3]!
  let e := hsh[4]!; let f := hsh[5]!; let g := hsh[6]!; let h := hsh[7]!
  let t1 := h + (hashSigma1 e + (choose e f g + (k + w)))
  let t2 := hashSigma0 a + maj a b c
  [t1 + t2, a, b, c, d + t1, e, f, g]

/-- `sha256_compress_rounds`. -/
def compressRounds (m hsh : List (BitVec 32)) : Nat → List (BitVec 32)
  | 0 => hsh
  | n + 1 => round (compressRounds m hsh n) constants[n]! (msgSchedule m n)

/-- `sha256_block`. -/
def block (m hsh : List (BitVec 32)) : List (BitVec 32) :=
  let res := compressRounds m hsh 64
  [res[0]! + hsh[0]!, res[1]! + hsh[1]!, res[2]! + hsh[2]!, res[3]! + hsh[3]!,
   res[4]! + hsh[4]!, res[5]! + hsh[5]!, res[6]! + hsh[6]!, res[7]! + hsh[7]!]

/-- `sha256_hash_blocks`. -/
def hashBlocks (m : Nat → List (BitVec 32)) (hsh : List (BitVec 32)) : Nat → List (BitVec 32)
  | 0 => hsh
  | n + 1 => block (m n) (hashBlocks m hsh n)

/-! The bridge to `Rind.HashSpec`. -/

theorem constants_eq : constants = sha256.K := rfl

theorem choose_eq (x y z : BitVec 32) : choose x y z = ch x y z := by
  unfold choose ch; ext i hi; simp; cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem maj_eq (x y z : BitVec 32) : maj x y z = rind.spec.maj x y z := by
  unfold maj rind.spec.maj; ext i hi; simp; cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem msgSigma0_eq (x : BitVec 32) : msgSigma0 x = sha256.smallSigma0 x := by
  simp only [msgSigma0, sha256.smallSigma0, BitVec.xor_assoc]

theorem msgSigma1_eq (x : BitVec 32) : msgSigma1 x = sha256.smallSigma1 x := by
  simp only [msgSigma1, sha256.smallSigma1, BitVec.xor_assoc]

theorem hashSigma0_eq (x : BitVec 32) : hashSigma0 x = sha256.bigSigma0 x := by
  simp only [hashSigma0, sha256.bigSigma0, BitVec.xor_assoc]

theorem hashSigma1_eq (x : BitVec 32) : hashSigma1 x = sha256.bigSigma1 x := by
  simp only [hashSigma1, sha256.bigSigma1, BitVec.xor_assoc]

theorem msgSchedule_lt (m : List (BitVec 32)) {t : Nat} (ht : t < 16) : msgSchedule m t = m[t]! := by
  rw [msgSchedule]; simp [ht]

theorem msgSchedule_add16 (m : List (BitVec 32)) (t : Nat) :
    msgSchedule m (t + 16) = sha256.smallSigma1 (msgSchedule m (t + 14)) + msgSchedule m (t + 9) +
      sha256.smallSigma0 (msgSchedule m (t + 1)) + msgSchedule m t := by
  rw [msgSchedule]
  simp only [show ¬ t + 16 < 16 by omega, ite_false, show t + 16 - 2 = t + 14 by omega,
    show t + 16 - 7 = t + 9 by omega, show t + 16 - 15 = t + 1 by omega,
    show t + 16 - 16 = t by omega, msgSigma0_eq, msgSigma1_eq, BitVec.add_assoc]

/-- The first `16 + k` words of `Rind.HashSpec`'s schedule, after `k` of its
steps, are `msgSchedule`'s. -/
theorem schedule_prefix (M : List (BitVec 32)) (hM : M.length = 16) (k : Nat) (hk : k ≤ 48) :
    let W := (List.range k).foldl
      (fun W t => W ++ [sha256.smallSigma1 W[t + 14]! + W[t + 9]! + sha256.smallSigma0 W[t + 1]! + W[t]!]) M
    W.length = 16 + k ∧ ∀ t < 16 + k, W[t]! = msgSchedule M t := by
  induction k with
  | zero =>
    refine ⟨by simpa using hM, fun t ht => ?_⟩
    simp [msgSchedule_lt M (show t < 16 by omega)]
  | succ k ih =>
    obtain ⟨hl, hW⟩ := ih (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hX : (List.range k).foldl _ M = X at hl hW
    refine ⟨by simp [hl]; omega, fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (16 + k) with h | h
    · rw [← hW t h]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (show t < X.length by omega)]
    · have ht' : t = k + 16 := by omega
      subst ht'
      have last : ∀ v : BitVec 32, (X ++ [v])[k + 16]! = v := fun v => by
        simp [show k + 16 = X.length by omega]
      rw [last, msgSchedule_add16, hW _ (by omega), hW _ (by omega), hW _ (by omega), hW _ (by omega)]

theorem schedule_getElem (M : List (BitVec 32)) (hM : M.length = 16) {t : Nat} (ht : t < 64) :
    (sha256.schedule M)[t]! = msgSchedule M t :=
  (schedule_prefix M hM 48 le_rfl).2 t ht

/-- `Rind.HashSpec`'s round is `round`. -/
theorem round_eq (s : List (BitVec 32)) (k w : BitVec 32) :
    (let T1 := s[7]! + sha256.bigSigma1 s[4]! + ch s[4]! s[5]! s[6]! + k + w
     let T2 := sha256.bigSigma0 s[0]! + rind.spec.maj s[0]! s[1]! s[2]!
     [T1 + T2, s[0]!, s[1]!, s[2]!, s[3]! + T1, s[4]!, s[5]!, s[6]!]) = round s k w := by
  simp only [round, choose_eq, maj_eq, hashSigma0_eq, hashSigma1_eq, BitVec.add_assoc]

theorem rounds_eq (M H : List (BitVec 32)) (hM : M.length = 16) (n : Nat) (hn : n ≤ 64) :
    (List.range n).foldl (fun (s : List (BitVec 32)) t =>
      let T1 := s[7]! + sha256.bigSigma1 s[4]! + ch s[4]! s[5]! s[6]! + sha256.K[t]! +
        (sha256.schedule M)[t]!
      let T2 := sha256.bigSigma0 s[0]! + rind.spec.maj s[0]! s[1]! s[2]!
      [T1 + T2, s[0]!, s[1]!, s[2]!, s[3]! + T1, s[4]!, s[5]!, s[6]!]) H =
    compressRounds M H n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
      compressRounds, schedule_getElem M hM (by omega), ← constants_eq]
    exact round_eq _ _ _

theorem length_round (s : List (BitVec 32)) (k w : BitVec 32) : (round s k w).length = 8 := rfl

theorem length_compressRounds (M H : List (BitVec 32)) (hH : H.length = 8) (n : Nat) :
    (compressRounds M H n).length = 8 := by
  cases n with
  | zero => exact hH
  | succ n => exact length_round _ _ _

/-- s2n-bignum's block function is `Rind.HashSpec`'s, on a 64-byte block and
an 8-word hash value. -/
theorem block_words (H : List (BitVec 32)) (b : List Byte) (hH : H.length = 8) (hb : b.length = 64) :
    block (words b) H = sha256.compress H b := by
  have hM : (words b).length = 16 := by simp [words, hb]
  have hR := length_compressRounds (words b) H hH 64
  rw [sha256.compress]
  simp only
  rw [rounds_eq (words b) H hM 64 le_rfl, block]
  generalize compressRounds (words b) H 64 = R at *
  match R, H, hR, hH with
  | [r0, r1, r2, r3, r4, r5, r6, r7], [h0, h1, h2, h3, h4, h5, h6, h7], _, _ => rfl

/-- `Rind.HashSpec`'s blocks of `bytes`, by index. -/
theorem blocks_eq (bytes : List Byte) :
    blocks 64 bytes = (List.range (bytes.length / 64)).map fun i => (bytes.drop (64 * i)).take 64 := by
  induction h : bytes.length using Nat.strong_induction_on generalizing bytes with
  | _ n ih =>
    subst h
    rw [blocks]
    by_cases hl : 64 ≤ bytes.length
    · rw [ite_eq_left ⟨by decide, hl⟩, show bytes.length / 64 = (bytes.length - 64) / 64 + 1 by omega,
        List.range_succ_eq_map, List.map_cons, List.map_map,
        ih (bytes.length - 64) (by omega) (bytes.drop 64) (by simp)]
      simp only [Nat.mul_zero, List.drop_zero, List.cons.injEq, true_and]
      apply List.map_congr_left
      intro i _
      simp [List.drop_drop, Nat.mul_succ, Nat.add_comm]
    · rw [ite_eq_right (fun h => hl h.2), show bytes.length / 64 = 0 by omega]
      rfl

theorem length_hashBlocks (m : Nat → List (BitVec 32)) (H : List (BitVec 32)) (hH : H.length = 8)
    (n : Nat) : (hashBlocks m H n).length = 8 := by
  cases n with
  | zero => exact hH
  | succ n => rfl

/-- s2n-bignum's hash of `n` blocks, the `i`th of which is the `i`th 64 bytes
of `bytes` as big-endian words, is `Rind.HashSpec`'s. -/
theorem hashBlocks_eq (H : List (BitVec 32)) (hH : H.length = 8) (bytes : List Byte) :
    hashBlocks (fun i => words ((bytes.drop (64 * i)).take 64)) H (bytes.length / 64) =
      (blocks 64 bytes).foldl sha256.compress H := by
  rw [blocks_eq]
  suffices ∀ n ≤ bytes.length / 64,
      hashBlocks (fun i => words ((bytes.drop (64 * i)).take 64)) H n =
        ((List.range n).map fun i => (bytes.drop (64 * i)).take 64).foldl sha256.compress H from
    this _ le_rfl
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hashBlocks, ih (by omega), List.range_succ, List.map_append, List.foldl_append, List.map_cons,
      List.map_nil, List.foldl_cons, List.foldl_nil, ← ih (by omega)]
    apply block_words _ _ (length_hashBlocks _ _ hH _)
    simp only [List.length_take, List.length_drop]
    omega

end rind.spec.s2n
