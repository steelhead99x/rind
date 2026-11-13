import Rind.Sha2Lemmas
open Aeneas Aeneas.Std

/-!
# s2n-bignum's SHA-512 spec

s2n-bignum's FIPS 180-4 spec of SHA-512's block function, from
`x86/proofs/utils/sha512_spec.ml` in awslabs/s2n-bignum#420 at 7ef7ba7c,
which rind's fork, `thirdparty/s2n-bignum`, holds, transliterated: HOL Light's
`EL n l` is `l[n]!`, `word_ror` is `rotateRight`, `word_ushr` is `>>>`, and `word_add` is
`+`, each grouped as the HOL Light is. The theorems rind's HOL Light proofs
state are about these, and `hashBlocks_eq` proves this hash of blocks is
`Rind.Sha2`'s `compress`.
-/

namespace rind.spec.s2n.sha512

/-- `sha512_choose`. -/
def choose (x y z : BitVec 64) : BitVec 64 := ((y ^^^ z) &&& x) ^^^ z
/-- `sha512_maj`. -/
def maj (x y z : BitVec 64) : BitVec 64 := (x &&& y) ||| ((x ||| y) &&& z)
/-- `sha512_hash_sigma_0`. -/
def hashSigma0 (x : BitVec 64) : BitVec 64 := x.rotateRight 28 ^^^ (x.rotateRight 34 ^^^ x.rotateRight 39)
/-- `sha512_hash_sigma_1`. -/
def hashSigma1 (x : BitVec 64) : BitVec 64 := x.rotateRight 14 ^^^ (x.rotateRight 18 ^^^ x.rotateRight 41)
/-- `sha512_msg_sigma_0`. -/
def msgSigma0 (x : BitVec 64) : BitVec 64 := x.rotateRight 1 ^^^ (x.rotateRight 8 ^^^ x >>> 7)
/-- `sha512_msg_sigma_1`. -/
def msgSigma1 (x : BitVec 64) : BitVec 64 := x.rotateRight 19 ^^^ (x.rotateRight 61 ^^^ x >>> 6)

/-- `sha512_constants`. -/
def constants : List (BitVec 64) :=
  [0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
   0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
   0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
   0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
   0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
   0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
   0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
   0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
   0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
   0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
   0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
   0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
   0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
   0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
   0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
   0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
   0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
   0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
   0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
   0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

/-- `sha512_msg_schedule`. -/
def msgSchedule (m : List (BitVec 64)) (t : Nat) : BitVec 64 :=
  if t < 16 then m[t]!
  else msgSigma1 (msgSchedule m (t - 2)) + msgSchedule m (t - 7) +
    (msgSigma0 (msgSchedule m (t - 15)) + msgSchedule m (t - 16))
termination_by t
decreasing_by all_goals omega

/-- `sha512_round`. -/
def round (hsh : List (BitVec 64)) (k w : BitVec 64) : List (BitVec 64) :=
  let a := hsh[0]!; let b := hsh[1]!; let c := hsh[2]!; let d := hsh[3]!
  let e := hsh[4]!; let f := hsh[5]!; let g := hsh[6]!; let h := hsh[7]!
  let t1 := h + (hashSigma1 e + (choose e f g + (k + w)))
  let t2 := hashSigma0 a + maj a b c
  [t1 + t2, a, b, c, d + t1, e, f, g]

/-- `sha512_compress_rounds`. -/
def compressRounds (m hsh : List (BitVec 64)) : Nat → List (BitVec 64)
  | 0 => hsh
  | n + 1 => round (compressRounds m hsh n) constants[n]! (msgSchedule m n)

/-- `sha512_block`. -/
def block (m hsh : List (BitVec 64)) : List (BitVec 64) :=
  let res := compressRounds m hsh 80
  [res[0]! + hsh[0]!, res[1]! + hsh[1]!, res[2]! + hsh[2]!, res[3]! + hsh[3]!,
   res[4]! + hsh[4]!, res[5]! + hsh[5]!, res[6]! + hsh[6]!, res[7]! + hsh[7]!]

/-- `sha512_hash_blocks`. -/
def hashBlocks (m : Nat → List (BitVec 64)) (hsh : List (BitVec 64)) : Nat → List (BitVec 64)
  | 0 => hsh
  | n + 1 => block (m n) (hashBlocks m hsh n)

/-! The bridge to `Rind.Sha2`. -/

theorem constants_eq : constants = fips512.K := rfl

theorem choose_eq (x y z : BitVec 64) : choose x y z = fips512.ch x y z := by
  unfold choose fips512.ch; ext i hi; simp; cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem maj_eq (x y z : BitVec 64) : maj x y z = fips512.maj x y z := by
  unfold maj fips512.maj; ext i hi; simp; cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem msgSigma0_eq (x : BitVec 64) : msgSigma0 x = fips512.smallSigma0 x := by
  simp only [msgSigma0, fips512.smallSigma0, BitVec.xor_assoc]

theorem msgSigma1_eq (x : BitVec 64) : msgSigma1 x = fips512.smallSigma1 x := by
  simp only [msgSigma1, fips512.smallSigma1, BitVec.xor_assoc]

theorem hashSigma0_eq (x : BitVec 64) : hashSigma0 x = fips512.bigSigma0 x := by
  simp only [hashSigma0, fips512.bigSigma0, BitVec.xor_assoc]

theorem hashSigma1_eq (x : BitVec 64) : hashSigma1 x = fips512.bigSigma1 x := by
  simp only [hashSigma1, fips512.bigSigma1, BitVec.xor_assoc]

theorem msgSchedule_lt (m : List (BitVec 64)) {t : Nat} (ht : t < 16) : msgSchedule m t = m[t]! := by
  rw [msgSchedule]; simp [ht]

theorem msgSchedule_add16 (m : List (BitVec 64)) (t : Nat) :
    msgSchedule m (t + 16) = fips512.smallSigma1 (msgSchedule m (t + 14)) + msgSchedule m (t + 9) +
      fips512.smallSigma0 (msgSchedule m (t + 1)) + msgSchedule m t := by
  rw [msgSchedule]
  simp only [show ¬ t + 16 < 16 by omega, ite_false, show t + 16 - 2 = t + 14 by omega,
    show t + 16 - 7 = t + 9 by omega, show t + 16 - 15 = t + 1 by omega,
    show t + 16 - 16 = t by omega, msgSigma0_eq, msgSigma1_eq, BitVec.add_assoc]

/-- The first `16 + k` words of `Rind.Sha2`'s schedule, after `k` of its
steps, are `msgSchedule`'s. -/
theorem schedule_prefix (M : List (BitVec 64)) (hM : M.length = 16) (k : Nat) (hk : k ≤ 64) :
    let W := (List.range k).foldl
      (fun W t => W ++ [fips512.smallSigma1 W[t + 14]! + W[t + 9]! + fips512.smallSigma0 W[t + 1]! + W[t]!]) M
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
      have last : ∀ v : BitVec 64, (X ++ [v])[k + 16]! = v := fun v => by
        simp [show k + 16 = X.length by omega]
      rw [last, msgSchedule_add16, hW _ (by omega), hW _ (by omega), hW _ (by omega), hW _ (by omega)]

theorem schedule_getElem (M : List (BitVec 64)) (hM : M.length = 16) {t : Nat} (ht : t < 80) :
    (fips512.schedule M)[t]! = msgSchedule M t :=
  (schedule_prefix M hM 64 le_rfl).2 t ht

/-- `Rind.Sha2`'s round is `round`. -/
theorem round_eq (s : List (BitVec 64)) (k w : BitVec 64) :
    (let T1 := s[7]! + fips512.bigSigma1 s[4]! + fips512.ch s[4]! s[5]! s[6]! + k + w
     let T2 := fips512.bigSigma0 s[0]! + fips512.maj s[0]! s[1]! s[2]!
     [T1 + T2, s[0]!, s[1]!, s[2]!, s[3]! + T1, s[4]!, s[5]!, s[6]!]) = round s k w := by
  simp only [round, choose_eq, maj_eq, hashSigma0_eq, hashSigma1_eq, BitVec.add_assoc]

theorem rounds_eq (M H : List (BitVec 64)) (hM : M.length = 16) (n : Nat) (hn : n ≤ 80) :
    (List.range n).foldl (fun (s : List (BitVec 64)) t =>
      let T1 := s[7]! + fips512.bigSigma1 s[4]! + fips512.ch s[4]! s[5]! s[6]! + fips512.K[t]! +
        (fips512.schedule M)[t]!
      let T2 := fips512.bigSigma0 s[0]! + fips512.maj s[0]! s[1]! s[2]!
      [T1 + T2, s[0]!, s[1]!, s[2]!, s[3]! + T1, s[4]!, s[5]!, s[6]!]) H =
    compressRounds M H n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
      compressRounds, schedule_getElem M hM (by omega), ← constants_eq]
    exact round_eq _ _ _

theorem length_round (s : List (BitVec 64)) (k w : BitVec 64) : (round s k w).length = 8 := rfl

theorem length_compressRounds (M H : List (BitVec 64)) (hH : H.length = 8) (n : Nat) :
    (compressRounds M H n).length = 8 := by
  cases n with
  | zero => exact hH
  | succ n => exact length_round _ _ _

/-- s2n-bignum's block function is `Rind.Sha2`'s, on a block's 16 words and
an 8-word hash value. -/
theorem block_eq (H M : List (BitVec 64)) (hH : H.length = 8) (hM : M.length = 16) :
    block M H = fips512.compressBlock H M := by
  have hR := length_compressRounds M H hH 80
  rw [fips512.compressBlock]
  simp only
  rw [rounds_eq M H hM 80 le_rfl, block]
  generalize compressRounds M H 80 = R at *
  match R, H, hR, hH with
  | [r0, r1, r2, r3, r4, r5, r6, r7], [h0, h1, h2, h3, h4, h5, h6, h7], _, _ => rfl

theorem map_bv_injective : Function.Injective (List.map (fun x : U64 => x.bv)) :=
  List.map_injective_iff.2 fun x y h => by cases x; cases y; simp_all

theorem processBlock_eq (h w : List U64) (hh : h.length = 8) (hw : w.length = 16) :
    (processBlock h w).map (·.bv) = block (w.map (·.bv)) (h.map (·.bv)) := by
  rw [block_eq _ _ (by simp [hh]) (by simp [hw]), processBlock, List.map_map]
  exact List.map_id _

theorem length_processBlock (h w : List U64) (hh : h.length = 8) (hw : w.length = 16) :
    (processBlock h w).length = 8 := by
  rw [← List.length_map (f := fun x : U64 => x.bv), processBlock_eq h w hh hw]
  rfl

theorem length_blockWords (b : List U8) : (blockWords b).length = 16 := by
  simp [blockWords]

/-- s2n-bignum's hash of `n` blocks, the `i`th of which is the big-endian words
of the `i`th 128 bytes of `bytes`, is `Rind.Sha2`'s `compress`. -/
theorem hashBlocks_eq (H : List U64) (hH : H.length = 8) (bytes : List U8)
    (hb : bytes.length % 128 = 0) :
    hashBlocks (fun i => (blockWords ((bytes.drop (128 * i)).take 128)).map (·.bv))
        (H.map (·.bv)) (bytes.length / 128) =
      (compress H bytes).map (·.bv) := by
  suffices ∀ n ≤ bytes.length / 128,
      hashBlocks (fun i => (blockWords ((bytes.drop (128 * i)).take 128)).map (·.bv))
          (H.map (·.bv)) n = (compress H (bytes.take (128 * n))).map (·.bv) ∧
        (compress H (bytes.take (128 * n))).length = 8 by
    rw [(this _ le_rfl).1, List.take_of_length_le (by omega)]
  intro n hn
  induction n with
  | zero => simp [hashBlocks, hH]
  | succ n ih =>
    obtain ⟨ih, hl⟩ := ih (by omega)
    have hA : (bytes.take (128 * n)).length = 128 * n := by simp; omega
    have hB : ((bytes.drop (128 * n)).take 128).length = 128 := by simp; omega
    have hc : ∀ X (B : List U8), B.length = 128 → compress X B = processBlock X (blockWords B) := by
      intro X B hB
      rw [compress_block _ _ (by omega), List.take_of_length_le (by omega),
        List.drop_eq_nil_of_le (by omega), compress_nil]
    rw [show 128 * (n + 1) = 128 * n + 128 by omega, List.take_add, compress_append _ _ _ (by omega), hc _ _ hB]
    refine ⟨?_, length_processBlock _ _ hl (length_blockWords _)⟩
    rw [hashBlocks, ih, processBlock_eq _ _ hl (length_blockWords _)]

end rind.spec.s2n.sha512
