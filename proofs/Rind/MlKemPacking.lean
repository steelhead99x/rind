import Rind.MlKemCoding

/-!
# s2n-bignum's and mlkem-native's packings are FIPS 203's encodings

s2n-bignum's ML-KEM theorems state what a routine writes as a list of words
packed into a number, its `num_of_wordlist`, or read from one, its
`wordlist_of_num`; mlkem-native's compression theorems pack
`compress_d`'s words the same way. These are their transliterations, over
each word's value as a natural, with the bridges to FIPS 203:

* `byteEncode12_of_words`: the 12-bit words of `ByteEncode_12(F)`'s bits are
  `F`'s coefficients, which is what `mlkem_tobytes` writes;
* `byteEncode_compress_of_words`: the `d`-bit words of
  `ByteEncode_d(Compress_d(F))` are mlkem-native's `compress_d` of `F`'s
  coefficients, what its compression routines write.
-/

open Spec Spec.MLKEM rind.spec.mlkem

namespace rind.spec.s2n

/-- `num_of_wordlist` of `w`-bit words, from `common/wordlist.ml`: the number
whose `w`-bit digits, least significant first, are `l`'s values, each taken
modulo `2 ^ w` as the word it is. -/
def numOfWords (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | h :: t => h % 2 ^ w + 2 ^ w * numOfWords w t

/-- `wordlist_of_num n x` of `w`-bit words, from `common/wordlist.ml`: the
first `n` `w`-bit digits of `x`, least significant first. -/
def wordsOfNum (w n x : ℕ) : List ℕ := (List.range n).map fun i => x / 2 ^ (w * i) % 2 ^ w

/-- Bit `k` of a packing is bit `k % w` of word `k / w`. -/
theorem numOfWords_testBit (w : ℕ) (hw : 0 < w) : ∀ (l : List ℕ) (k : ℕ),
    (numOfWords w l).testBit k = (l[k / w]!).testBit (k % w)
  | [], k => by simp [numOfWords]
  | h :: t, k => by
    have hh : h % 2 ^ w < 2 ^ w := Nat.mod_lt _ (by positivity)
    rw [numOfWords, add_comm, Nat.testBit_two_pow_mul_add _ hh]
    split_ifs with hk
    · rw [Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk, Nat.testBit_mod_two_pow]
      simp [hk]
    · rw [numOfWords_testBit w hw t (k - w)]
      obtain ⟨c, rfl⟩ : ∃ c, k = c + w := ⟨k - w, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_div_right _ hw, Nat.add_mod_right]
      simp

/-- A byte string whose bits are those of the packing of `F`'s coefficients'
values as 12-bit words is `ByteEncode_12(F)`. -/
theorem byteEncode12_of_words (F : Polynomial) (l : List ℕ)
    (hF : ∀ p < 256, l[p]! = (F[p]!).val) (B : 𝔹 384)
    (hB : ∀ k < 3072, bit B k = (numOfWords 12 l).testBit k) :
    B = ByteEncode 12 F := by
  apply eq_of_bit
  intro k hk
  rw [hB k (by omega), ByteEncode_bit (d := 12) F (by norm_num) k (by omega),
    numOfWords_testBit 12 (by norm_num), hF _ (by omega)]

/-- mlkem-native's `compress_d`, from `proofs/hol_light/common/mlkem_specs.ml`:
`word((val x * 2^d + 1664) DIV 3329)`, as the value of that `d`-bit word. -/
def compressD (d x : ℕ) : ℕ := (x * 2 ^ d + 1664) / 3329 % 2 ^ d

/-- `compress_d` is FIPS 203's `Compress_d`. -/
theorem compress_val_eq (d : ℕ) (hd : 1 ≤ d ∧ d < 12) (x : Zq) :
    (Compress d x hd).val = compressD d x.val := by
  have hm : m d = 2 ^ d := by simp [m]; omega
  rw [Compress_val, ZMod.val_natCast, hm, compressD, mul_comm x.val]
  congr 1
  generalize 2 ^ d * x.val = y
  show (2 * y + 3329) / (2 * 3329) = (y + 1664) / 3329
  omega

/-- A byte string whose bits are those of the packing of mlkem-native's
`compress_d` of `F`'s coefficients as `d`-bit words is
`ByteEncode_d(Compress_d(F))`. -/
theorem byteEncode_compress_of_words (d : ℕ) (hd : 1 ≤ d ∧ d < 12) (F : Polynomial) (l : List ℕ)
    (hF : ∀ p < 256, l[p]! = compressD d (F[p]!).val) (B : 𝔹 (32 * d))
    (hB : ∀ k < 256 * d, bit B k = (numOfWords d l).testBit k) :
    B = ByteEncode d (Polynomial.Compress d F hd) (by omega) := by
  apply eq_of_bit
  intro k hk
  have hkd : k / d < 256 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    omega
  rw [hB k (by omega), ByteEncode_bit _ _ k (by omega), numOfWords_testBit d (by omega),
    hF _ hkd, Polynomial.Compress, Vector.getElem!_map_eq _ _ _ hkd, compress_val_eq]

end rind.spec.s2n
