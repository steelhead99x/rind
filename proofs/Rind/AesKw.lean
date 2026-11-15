import Rind.AesModes
import Rind.Bytes
open Aeneas Aeneas.Std

/-!
# SP 800-38F's AES key wrap, KW and KWP, on bytes

The wrapping function W and its inverse, as SP 800-38F's algorithms 1 and 2
state them in RFC 3394's index form (section 2.2.1 and 2.2.2): `6n` steps
over the `n` 64-bit semiblocks, step `t = nj + i` ciphering `A | R[i]` and
XORing `t`, big-endian, into the new `A`. KW (algorithms 3 and 4) wraps under
the default ICV1 `A6A6A6A6A6A6A6A6`, and KWP (algorithms 5 and 6, RFC 5649)
under ICV2 `A65959A6` and the plaintext's length, padding it with zeros to a
whole number of semiblocks and ciphering a single padded semiblock with AES
itself. Nothing here is a target's: `Rind.X86_64.AesKw` proves rind's
`key_wrap::AesKek` against it on both targets.
-/

namespace rind.vale

/-- The 8 bytes of the 64-bit big-endian integer `n`. -/
def be64 (n : Nat) : List (BitVec 8) := (be128 n).drop 8

/-- Bytewise XOR. -/
def xorBytes (a b : List (BitVec 8)) : List (BitVec 8) := List.zipWith (· ^^^ ·) a b

/-- The bytes `p` as `p.length / 8` semiblocks of 8 bytes. -/
def semiblocks (p : List (BitVec 8)) : List (List (BitVec 8)) :=
  (List.range (p.length / 8)).map fun i => (p.drop (8 * i)).take 8

/-- W's step `t = k + 1` over `n` semiblocks: `B = CIPH(A | R[i])`, then
`A = MSB64(B) ⊕ [t]64` and `R[i] = LSB64(B)`, with `i = k mod n`. -/
def wStep (alg : Algorithm) (key : List (BitVec 8)) (n : Nat)
    (s : List (BitVec 8) × List (List (BitVec 8))) (k : Nat) :
    List (BitVec 8) × List (List (BitVec 8)) :=
  let b := aesBlock alg key (s.1 ++ s.2[k % n]!)
  (xorBytes (b.take 8) (be64 (k + 1)), s.2.set (k % n) (b.drop 8))

/-- SP 800-38F's wrapping function W of the semiblocks `a | p`: its `6n`
steps for the `n` semiblocks of `p`, returning `A` and the `R[i]` in order. -/
def kwW (alg : Algorithm) (key a p : List (BitVec 8)) : List (BitVec 8) :=
  let n := p.length / 8
  let s := (List.range (6 * n)).foldl (wStep alg key n) (a, semiblocks p)
  s.1 ++ s.2.flatten

/-- W⁻¹'s step `t = k + 1`, the inverse of `wStep`: `B = CIPH⁻¹((A ⊕ [t]64) | R[i])`,
then `A = MSB64(B)` and `R[i] = LSB64(B)`. -/
def uStep (alg : Algorithm) (key : List (BitVec 8)) (n : Nat)
    (s : List (BitVec 8) × List (List (BitVec 8))) (k : Nat) :
    List (BitVec 8) × List (List (BitVec 8)) :=
  let b := aesBlockDecrypt alg key (xorBytes s.1 (be64 (k + 1)) ++ s.2[k % n]!)
  (b.take 8, s.2.set (k % n) (b.drop 8))

/-- SP 800-38F's unwrapping function W⁻¹ of the semiblocks `a | c`: its `6n`
steps from the last, returning `A` and the `R[i]` in order. -/
def kwWInv (alg : Algorithm) (key a c : List (BitVec 8)) : List (BitVec 8) × List (BitVec 8) :=
  let n := c.length / 8
  let s := (List.range (6 * n)).reverse.foldl (uStep alg key n) (a, semiblocks c)
  (s.1, s.2.flatten)

/-- KW's default ICV1. -/
def icv1 : List (BitVec 8) := List.replicate 8 0xa6

/-- KWP's ICV2, which the plaintext's 32-bit length follows. -/
def icv2 : List (BitVec 8) := [0xa6, 0x59, 0x59, 0xa6]

/-- KW-AE, for a plaintext of at least two semiblocks. -/
def kwAE (alg : Algorithm) (key p : List (BitVec 8)) : List (BitVec 8) :=
  kwW alg key icv1 p

/-- KW-AD, for a ciphertext of at least three semiblocks: the plaintext, unless
W⁻¹'s `A` is not ICV1. -/
def kwAD (alg : Algorithm) (key c : List (BitVec 8)) : Option (List (BitVec 8)) :=
  let (a, p) := kwWInv alg key (c.take 8) (c.drop 8)
  if a = icv1 then some p else none

/-- KWP's padded plaintext: `p` and the zeros that fill its last semiblock. -/
def kwpPad (p : List (BitVec 8)) : List (BitVec 8) :=
  p ++ List.replicate ((8 - p.length % 8) % 8) 0

/-- KWP-AE, for a plaintext of 1 to `2^32 - 1` bytes: one AES block of
`ICV2 | [len]32 | PAD` for a single padded semiblock, else W of it. -/
def kwpAE (alg : Algorithm) (key p : List (BitVec 8)) : List (BitVec 8) :=
  let a := icv2 ++ be32 p.length
  if p.length ≤ 8 then aesBlock alg key (a ++ kwpPad p) else kwW alg key a (kwpPad p)

/-- KWP-AD, for a ciphertext of at least two semiblocks: its `n` semiblocks of
padded plaintext, from one AES block for `n = 1` and W⁻¹ otherwise, are
returned without their padding if `A` is ICV2 and a length `m` with
`8(n - 1) < m ≤ 8n`, and the padding is zeros. -/
def kwpAD (alg : Algorithm) (key c : List (BitVec 8)) : Option (List (BitVec 8)) :=
  let n := c.length / 8 - 1
  let (a, p) :=
    if n = 1 then
      let s := aesBlockDecrypt alg key c
      (s.take 8, s.drop 8)
    else kwWInv alg key (c.take 8) (c.drop 8)
  let m := ofBe (a.drop 4)
  if a.take 4 = icv2 ∧ 8 * (n - 1) < m ∧ m ≤ 8 * n ∧ ∀ b ∈ p.drop m, b = 0 then some (p.take m)
  else none

-- RFC 3394's section 4.1 and 4.6, and RFC 5649's section 6.
private def hex (s : String) : List (BitVec 8) :=
  let d (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List (BitVec 8)
    | a :: b :: rest => BitVec.ofNat 8 (16 * d a + d b) :: go rest
    | _ => []
  go s.toList

#guard kwAE .AES_128 (hex "000102030405060708090a0b0c0d0e0f") (hex "00112233445566778899aabbccddeeff") ==
  hex "1fa68b0a8112b447aef34bd8fb5a7b829d3e862371d2cfe5"
#guard kwAD .AES_128 (hex "000102030405060708090a0b0c0d0e0f")
  (hex "1fa68b0a8112b447aef34bd8fb5a7b829d3e862371d2cfe5") == some (hex "00112233445566778899aabbccddeeff")
#guard kwAD .AES_128 (hex "000102030405060708090a0b0c0d0e0f")
  (hex "1fa68b0a8112b447aef34bd8fb5a7b829d3e862371d2cfe4") == none
#guard kwAE .AES_256 (hex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")
  (hex "00112233445566778899aabbccddeeff000102030405060708090a0b0c0d0e0f") ==
  hex "28c9f404c4b810f4cbccb35cfb87f8263f5786e2d80ed326cbc7f0e71a99f43bfb988b9b7a02dd21"
#guard kwpAE .AES_192 (hex "5840df6e29b02af1ab493b705bf16ea1ae8338f4dcc176a8")
  (hex "c37b7e6492584340bed12207808941155068f738") ==
  hex "138bdeaa9b8fa7fc61f97742e72248ee5ae6ae5360d1ae6a5f54f373fa543b6a"
#guard kwpAD .AES_192 (hex "5840df6e29b02af1ab493b705bf16ea1ae8338f4dcc176a8")
  (hex "138bdeaa9b8fa7fc61f97742e72248ee5ae6ae5360d1ae6a5f54f373fa543b6a") ==
  some (hex "c37b7e6492584340bed12207808941155068f738")
#guard kwpAE .AES_192 (hex "5840df6e29b02af1ab493b705bf16ea1ae8338f4dcc176a8") (hex "466f7250617369") ==
  hex "afbeb0f07dfbf5419200f2ccb50bb24f"
#guard kwpAD .AES_192 (hex "5840df6e29b02af1ab493b705bf16ea1ae8338f4dcc176a8")
  (hex "afbeb0f07dfbf5419200f2ccb50bb24f") == some (hex "466f7250617369")
#guard kwpAD .AES_192 (hex "5840df6e29b02af1ab493b705bf16ea1ae8338f4dcc176a8")
  (hex "afbeb0f07dfbf5419200f2ccb50bb24e") == none

/-! ## Bytes as Rust's integer conversions write them, for `Rind.X86_64.AesKw` -/

theorem toLEBytes_cast {w w' : Nat} (h : w = w') (x : BitVec w) :
    (x.cast h).toLEBytes = x.toLEBytes := by
  subst h; rfl

theorem toLEBytes_fromLEBytes (l : List (BitVec 8)) : (BitVec.fromLEBytes l).toLEBytes = l := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [BitVec.getElem_toLEBytes_eq_getElem _ _ _ h1 hj (by omega),
    BitVec.fromLEBytes_getElem _ _ (by omega)]
  have h8 : (8 * i + j) / 8 = i := by omega
  have h8' : (8 * i + j) % 8 = j := by omega
  simp only [h8, h8', Byte.testBit, BitVec.getElem_eq_testBit_toNat]

theorem toLEBytes_xor {w : Nat} (x y : BitVec w) :
    (x ^^^ y).toLEBytes = xorBytes x.toLEBytes y.toLEBytes := by
  apply List.ext_getElem (by simp [xorBytes])
  intro i h1 h2
  apply BitVec.eq_of_getElem_eq
  intro j hj
  simp only [xorBytes, List.getElem_zipWith, BitVec.getElem_xor]
  have hi : i < x.toLEBytes.length := by simp at h1 ⊢; omega
  have hi' : i < y.toLEBytes.length := by simp at h1 ⊢; omega
  by_cases hw : 8 * i + j < w
  · rw [BitVec.getElem_toLEBytes_eq_getElem _ _ _ h1 hj hw, BitVec.getElem_toLEBytes_eq_getElem _ _ _ hi hj hw,
      BitVec.getElem_toLEBytes_eq_getElem _ _ _ hi' hj hw, BitVec.getElem_xor]
  · rw [BitVec.getElem_toLEBytes_eq_false _ _ _ h1 hj (by omega), BitVec.getElem_toLEBytes_eq_false _ _ _ hi hj (by omega),
      BitVec.getElem_toLEBytes_eq_false _ _ _ hi' hj (by omega)]
    rfl

theorem be128_drop (n k : Nat) :
    (be128 n).drop k = (List.range (16 - k)).map fun i => BitVec.ofNat 8 (n / 256 ^ (15 - k - i)) := by
  apply List.ext_getElem (by simp [be128])
  intro i h1 h2
  simp only [be128, List.getElem_drop, List.getElem_map, List.getElem_range, Nat.sub_add_eq]

theorem toBEBytes_eq {w : Nat} (m : Nat) (hw : w = 8 * m) (x : BitVec w) :
    x.toBEBytes = (List.range m).map fun i => BitVec.ofNat 8 (x.toNat / 256 ^ (m - 1 - i)) := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  have hi : i < m := by simpa using h2
  have hl : x.toLEBytes.length = m := by simp; omega
  apply BitVec.eq_of_getElem_eq
  intro j hj
  simp only [BitVec.toBEBytes, List.getElem_reverse, List.getElem_map, List.getElem_range]
  rw [BitVec.getElem_toLEBytes_eq_getElem _ _ _ _ hj (by rw [hl]; omega)]
  have hp : 256 ^ (m - 1 - i) = 2 ^ (8 * (m - 1 - i)) := by rw [pow_mul]; norm_num
  simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, hp,
    Nat.testBit_div_two_pow, hj, decide_true, Bool.true_and, hl]
  congr 1; omega

theorem toBEBytes_64 (x : BitVec 64) : x.toBEBytes = be64 x.toNat := by
  rw [toBEBytes_eq 8 rfl, be64, be128_drop]

theorem toBEBytes_32 (x : BitVec 32) : x.toBEBytes = be32 x.toNat := by
  rw [toBEBytes_eq 4 rfl, be32, be128_drop]

theorem ofBe_foldl (l : List (BitVec 8)) (acc : Nat) :
    l.foldl (fun a b => 256 * a + b.toNat) acc =
      acc * 256 ^ l.length + Nat.ofDigits 256 (l.reverse.map (·.toNat)) := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ih, List.reverse_cons, List.map_append, Nat.ofDigits_append]
    simp only [List.length_cons, List.length_map, List.length_reverse, List.map_cons, List.map_nil,
      Nat.ofDigits_singleton, pow_succ]
    ring

theorem toNat_fromBEBytes (l : List (BitVec 8)) : (BitVec.fromBEBytes l).toNat = ofBe l := by
  rw [BitVec.fromBEBytes, BitVec.toNat_cast, rind.spec.toNat_fromLEBytes, ofBe, ofBe_foldl]
  simp

end rind.vale
