import Rind.X86_64.Funs
import Rind.X86_64.Blockwise
import Rind.S2nSha256
import Mathlib.Tactic.IntervalCases
open Aeneas Aeneas.Std Result rind.spec

/-!
# SHA-256 on x86_64's SHA extensions

rind's HOL Light proofs `SHA256_COMPRESS_BLOCKS_SHAEXT_CORRECT` and
`SHA256_FINISH_SHAEXT_CORRECT`, in `proofs/hol-light/x86_64/sha256_compress_blocks_shaext.ml`
and `proofs/hol-light/x86_64/sha256_finish_shaext.ml` at rind's commit, that the `asm!` blocks
in `sha256_compress_blocks_shaext` and `finish_padded`, as rind's build emits them, compute
s2n-bignum's `sha256_hash_blocks`, restated as an axiom each about the Rust function around
the block. `admin/prove` checks the HOL Light proofs against the bytes rind's release build
emits and the `K` table they read.

The theorems' hypotheses hold for every call the functions allow: `K`'s type aligns it to
16 bytes; the state is an allocation of its own, apart from the code; a slice's fewer than
2^64 bytes hold fewer than 2^58 blocks; and `finish_padded`'s safety contract bounds the lane
count by 4 and has the message hold the lanes the block reads. The restatements, that each
function passes the registers its theorem names, and that `finish_padded` stores xmm2 and
xmm1 as the digest's bytes, are trusted.

The padding around the finish's block is plain Rust, which `admin/prove` translates and this
file proves: `padded_spec` gives the lanes `padded` and `ended` build, `shaextPadded_bytes`
that the block HOL Light's `sha256_shaext_padded` makes of them is a block of bytes, and
`padded_blocks` that those bytes are FIPS 180-4's last block, or two.
`sha256_finish_shaext_spec` composes them with the axiom into FIPS 180-4's digest.
-/

namespace rind.x86_64.shaext

/-! ## HOL Light's terms

Transliterated from `sha256_finish_shaext.ml`: `word_bytereverse` is `bytereverse`,
`word_subword x (i,32)` is `x.extractLsb' i 32`, `EL j t` is `t[j]!`, and `word 0` is `0`. -/

/-- `word_bytereverse` on a 32-bit word. -/
def bytereverse (w : BitVec 32) : BitVec 32 :=
  w.extractLsb' 0 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 24 8

/-- `sha256_shaext_lane`: a lane held as two little-endian registers, as its four words. -/
def shaextLane (x y : BitVec 64) : List (BitVec 32) :=
  [bytereverse (x.extractLsb' 0 32), bytereverse (x.extractLsb' 32 32),
   bytereverse (y.extractLsb' 0 32), bytereverse (y.extractLsb' 32 32)]

/-- `sha256_shaext_padded`: `r` of `t`'s lanes, at most three, the lane `x` and `y` hold,
zeros, and `l` as the last lane's top word unless that lane is `x` and `y`. -/
def shaextPadded (r : Nat) (t : List (BitVec 32)) (x y l : BitVec 64) : List (BitVec 32) :=
  if r = 0 then
    shaextLane x y ++ (shaextLane 0 0 ++ (shaextLane 0 0 ++ shaextLane 0 l))
  else if r = 1 then
    [t[0]!, t[1]!, t[2]!, t[3]!] ++ (shaextLane x y ++ (shaextLane 0 0 ++ shaextLane 0 l))
  else if r = 2 then
    [t[0]!, t[1]!, t[2]!, t[3]!, t[4]!, t[5]!, t[6]!, t[7]!] ++ (shaextLane x y ++ shaextLane 0 l)
  else
    [t[0]!, t[1]!, t[2]!, t[3]!, t[4]!, t[5]!, t[6]!, t[7]!, t[8]!, t[9]!, t[10]!, t[11]!] ++
      shaextLane x y

/-- `sha256_shaext_finish_blocks`: the message's `n` blocks, the padded one, and, when `r` is
4, one of zeros and the length. -/
def shaextFinishBlocks (m : Nat → List (BitVec 32)) (n r : Nat) (x y l : BitVec 64) (i : Nat) :
    List (BitVec 32) :=
  if i < n then m i else if i = n then shaextPadded r (m n) x y l else shaextPadded 0 (m n) 0 0 l

/-! ## Bytes and words -/

/-- A big-endian word is its bytes, most significant first. -/
theorem be32_eq (a b c d : Byte) : be32 a b c d = a ++ b ++ c ++ d := by
  ext i hi
  rw [be32, BitVec.fromBEBytes, BitVec.getElem_cast, BitVec.fromLEBytes_getElem]
  interval_cases i <;> simp only [Byte.testBit, BitVec.testBit_toNat, Nat.reduceDiv, Nat.reduceMod,
    List.getElem_cons_zero, List.getElem_cons_succ, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] <;> bv_decide

theorem length_words (l : List Byte) : (rind.spec.words l).length = l.length / 4 := by simp [rind.spec.words]

theorem getElem_words (l : List Byte) (i : Nat) (h : i < (rind.spec.words l).length) :
    (rind.spec.words l)[i] = be32 l[4 * i]! l[4 * i + 1]! l[4 * i + 2]! l[4 * i + 3]! := by
  simp [rind.spec.words]

theorem getElem!_append_ite (a b : List Byte) (n : Nat) :
    (a ++ b)[n]! = if n < a.length then a[n]! else b[n - a.length]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append]
  split <;> rfl

/-- The words of bytes split on a word boundary are those of each part. -/
theorem words_append (a b : List Byte) (ha : a.length % 4 = 0) :
    rind.spec.words (a ++ b) = rind.spec.words a ++ rind.spec.words b := by
  apply List.ext_getElem
  · simp only [length_words, List.length_append]; omega
  · intro i h1 h2
    rw [getElem_words, List.getElem_append]
    simp only [length_words, List.length_append] at h1 h2
    split
    · rename_i hi
      rw [getElem_words]
      simp only [length_words] at hi
      simp only [getElem!_append_ite, show 4 * i < a.length by omega, show 4 * i + 1 < a.length by omega,
        show 4 * i + 2 < a.length by omega, show 4 * i + 3 < a.length by omega, ite_true]
    · rename_i hi
      rw [getElem_words]
      simp only [length_words] at hi
      simp only [getElem!_append_ite, show ¬ 4 * i < a.length by omega, show ¬ 4 * i + 1 < a.length by omega,
        show ¬ 4 * i + 2 < a.length by omega, show ¬ 4 * i + 3 < a.length by omega, ite_false]
      have hwa := length_words a
      congr 1 <;> congr 1 <;> omega

/-- `T`'s first `n` words are those of its first `4 n` bytes. -/
theorem words_take (T : List Byte) (n : Nat) (h : 4 * n ≤ T.length) :
    (List.range n).map (fun j => (rind.spec.words T)[j]!) = rind.spec.words (T.take (4 * n)) := by
  apply List.ext_getElem
  · simp [length_words]; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, getElem_words,
      getElem!_pos (rind.spec.words T) i (by simp [length_words]; omega), getElem_words]
    simp [List.getElem!_eq_getElem?_getD, show 4 * i < 4 * n by omega,
      show 4 * i + 1 < 4 * n by omega, show 4 * i + 2 < 4 * n by omega, show 4 * i + 3 < 4 * n by omega]

/-- The 64-bit word whose little-endian bytes are `l`'s first eight. -/
def le64 (l : List Byte) : BitVec 64 :=
  l[7]! ++ l[6]! ++ l[5]! ++ l[4]! ++ l[3]! ++ l[2]! ++ l[1]! ++ l[0]!

/-- A lane of two words is the words of their bytes. -/
theorem shaextLane_le64 (a b : List Byte) (ha : a.length = 8) (hb : b.length = 8) :
    shaextLane (le64 a) (le64 b) = rind.spec.words (a ++ b) := by
  match a, b, ha, hb with
  | [a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7], _, _ =>
    simp [shaextLane, bytereverse, le64, rind.spec.words, List.range_succ, be32_eq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

theorem le64_zero : le64 (List.replicate 8 0#8) = 0 := by decide

/-- `u16::from_le_bytes`. -/
theorem u16_from_le_bytes_bv (a : Std.Array U8 2#usize) :
    (core.num.U16.from_le_bytes a).bv = a.val[1]!.bv ++ a.val[0]!.bv := by
  simp only [core.num.U16.from_le_bytes]
  obtain ⟨l, hl⟩ : ∃ l, a.val = l := ⟨_, rfl⟩
  have h2 : l.length = 2 := by rw [← hl]; simp
  ext i hi
  rw [BitVec.getElem_cast, BitVec.fromLEBytes_getElem]
  match l, h2 with
  | [b0, b1], _ =>
    interval_cases i <;> simp only [Byte.testBit, BitVec.testBit_toNat, Nat.reduceDiv, Nat.reduceMod,
      List.getElem_map] <;> simp [hl] <;> bv_decide

/-- `u32::from_le_bytes`. -/
theorem u32_from_le_bytes_bv (a : Std.Array U8 4#usize) :
    (core.num.U32.from_le_bytes a).bv = a.val[3]!.bv ++ a.val[2]!.bv ++ a.val[1]!.bv ++ a.val[0]!.bv := by
  simp only [core.num.U32.from_le_bytes]
  obtain ⟨l, hl⟩ : ∃ l, a.val = l := ⟨_, rfl⟩
  have h2 : l.length = 4 := by rw [← hl]; simp
  ext i hi
  rw [BitVec.getElem_cast, BitVec.fromLEBytes_getElem]
  match l, h2 with
  | [b0, b1, b2, b3], _ =>
    interval_cases i <;> simp only [Byte.testBit, BitVec.testBit_toNat, Nat.reduceDiv, Nat.reduceMod,
      List.getElem_map] <;> simp [hl] <;> bv_decide

/-- `u64::from_le_bytes`. -/
theorem u64_from_le_bytes_bv (a : Std.Array U8 8#usize) :
    (core.num.U64.from_le_bytes a).bv = le64 (bv a.val) := by
  simp only [core.num.U64.from_le_bytes]
  obtain ⟨l, hl⟩ : ∃ l, a.val = l := ⟨_, rfl⟩
  have h2 : l.length = 8 := by rw [← hl]; simp
  ext i hi
  rw [BitVec.getElem_cast, BitVec.fromLEBytes_getElem]
  match l, h2 with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    interval_cases i <;> simp only [Byte.testBit, BitVec.testBit_toNat, Nat.reduceDiv, Nat.reduceMod,
      List.getElem_map] <;> simp [hl, le64, bv] <;> bv_decide

/-! ## The padding, `padded` and `ended` -/

/-- `ended`'s word for a part of one to seven bytes, bit by bit. -/
macro "ended_bits" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append]
  interval_cases i <;> simp))

theorem ended_bits1 (p0 : BitVec 8) : 32768#64 ||| p0.setWidth 64 = 128#56 ++ p0 := by ended_bits

theorem ended_bits2 (p0 p1 : BitVec 8) :
    8388608#64 ||| (p1 ++ p0).setWidth 64 = 128#48 ++ p1 ++ p0 := by ended_bits

theorem ended_bits3 (p0 p1 p2 : BitVec 8) :
    2147483648#64 ||| (p1 ++ p0).setWidth 64 ||| p2.setWidth 64 <<< 16 =
      128#40 ++ p2 ++ p1 ++ p0 := by ended_bits

theorem ended_bits4 (p0 p1 p2 p3 : BitVec 8) :
    549755813888#64 ||| (p3 ++ p2 ++ p1 ++ p0).setWidth 64 = 128#32 ++ p3 ++ p2 ++ p1 ++ p0 := by
  ended_bits

theorem ended_bits5 (p0 p1 p2 p3 p4 : BitVec 8) :
    140737488355328#64 ||| (p3 ++ p2 ++ p1 ++ p0).setWidth 64 ||| p4.setWidth 64 <<< 32 =
      128#24 ++ p4 ++ p3 ++ p2 ++ p1 ++ p0 := by ended_bits

theorem ended_bits6 (p0 p1 p2 p3 p4 p5 : BitVec 8) :
    36028797018963968#64 ||| (p3 ++ p2 ++ p1 ++ p0).setWidth 64 ||| (p5 ++ p4).setWidth 64 <<< 32 =
      128#16 ++ p5 ++ p4 ++ p3 ++ p2 ++ p1 ++ p0 := by ended_bits

theorem ended_bits7 (p0 p1 p2 p3 p4 p5 p6 : BitVec 8) :
    9223372036854775808#64 ||| (p3 ++ p2 ++ p1 ++ p0).setWidth 64 |||
      (p5 ++ p4).setWidth 64 <<< 32 ||| p6.setWidth 64 <<< 48 =
      128#8 ++ p6 ++ p5 ++ p4 ++ p3 ++ p2 ++ p1 ++ p0 := by ended_bits

/-- `ended`: the part, then the 0x80, then zeros, as a little-endian word. -/
theorem ended_spec (part : Slice U8) (h : part.length < 8) :
    low.x86_64.sha256.ended part ⦃ w =>
      w.bv = le64 (bv part.val ++ 128#8 :: List.replicate (7 - part.length) 0#8) ⦄ := by
  obtain ⟨l, hl⟩ : ∃ l, part.val = l := ⟨_, rfl⟩
  have hlen : l.length < 8 := by simpa [Slice.length, hl] using h
  have hpl : part.length = l.length := by simp [Slice.length, hl]
  unfold low.x86_64.sha256.ended
  simp only [Slice.len, hpl, hl]
  rcases l with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨p6, _ | ⟨p7, l⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals simp at hlen
  all_goals
    try simp [core.slice.Slice.split_first_chunk, core.slice.Slice.first, Slice.length, hl, bv, le64]
    try simp only [lift, core.convert.num.FromU64U32.from, core.convert.num.FromU64U8.from,
      core.convert.num.FromU64U16.from, bind_ok]
    try step*
  all_goals
    simp_all only [UScalar.bv_or, u16_from_le_bytes_bv, u32_from_le_bytes_bv]
    try simp
    try first
      | exact ended_bits1 _ | exact ended_bits2 _ _ | exact ended_bits3 _ _ _
      | exact ended_bits4 _ _ _ _ | exact ended_bits5 _ _ _ _ _ | exact ended_bits6 _ _ _ _ _ _
      | exact ended_bits7 _ _ _ _ _ _ _

/-- The end lane of a part `P` under 8 bytes: its first eight bytes are `P` and the 0x80, and
its last eight zeros. -/
theorem endLane_take_short (P : List Byte) (h : P.length < 8) :
    (P ++ 128#8 :: List.replicate (15 - P.length) 0#8).take 8 =
      P ++ 128#8 :: List.replicate (7 - P.length) 0#8 := by
  rw [List.take_append, List.take_of_length_le (by omega), List.take_cons (by omega), List.take_replicate]
  congr 3; omega

theorem endLane_drop_short (P : List Byte) (h : P.length < 8) :
    (P ++ 128#8 :: List.replicate (15 - P.length) 0#8).drop 8 = List.replicate 8 0#8 := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    show 8 - P.length = (7 - P.length) + 1 by omega, List.drop_succ_cons, List.drop_replicate]
  congr 1; omega

/-- The end lane of a part `P` of 8 bytes or more: its first eight bytes are `P`'s, and its
last eight the rest of `P`, the 0x80, and zeros. -/
theorem endLane_take_long (P : List Byte) (h : 8 ≤ P.length) :
    (P ++ 128#8 :: List.replicate (15 - P.length) 0#8).take 8 = P.take 8 := by
  rw [List.take_append, show 8 - P.length = 0 by omega, List.take_zero, List.append_nil]

theorem endLane_drop_long (P : List Byte) (h : 8 ≤ P.length) :
    (P ++ 128#8 :: List.replicate (15 - P.length) 0#8).drop 8 =
      P.drop 8 ++ 128#8 :: List.replicate (7 - (P.drop 8).length) 0#8 := by
  rw [List.drop_append, show 8 - P.length = 0 by omega, List.drop_zero, List.length_drop]
  congr 3; omega

/-- `padded`: the count of whole lanes, or 4 when the length takes a block of its own; the
length; and the end lane's two words, the part past the whole lanes, the 0x80, and zeros, with
the length as the second when that is the block's last lane. -/
theorem padded_spec (tail : Slice U8) (length : Std.Array U8 8#usize) (ht : tail.length < 64) :
    low.x86_64.sha256.padded tail length ⦃ p =>
      p.lanes.val = (if tail.length + 9 ≤ 64 then tail.length / 16 else 4) ∧
      p.length.bv = le64 (bv length.val) ∧
      p.«end».val[0]!.bv = le64 (((bv tail.val).drop (16 * (tail.length / 16)) ++
        128#8 :: List.replicate (15 - tail.length % 16) 0#8).take 8) ∧
      p.«end».val[1]!.bv = (if tail.length + 9 ≤ 64 ∧ tail.length / 16 = 3 then le64 (bv length.val)
        else le64 (((bv tail.val).drop (16 * (tail.length / 16)) ++
          128#8 :: List.replicate (15 - tail.length % 16) 0#8).drop 8)) ⦄ := by
  unfold low.x86_64.sha256.padded
  step*
  have hlanes : lanes.val = tail.length / 16 := by simp [lanes_post, Slice.len, Slice.length]
  have hpart : part.length = tail.length % 16 := by rw [part_post1, i1_post, hlanes]; omega
  have hP : bv part.val = (bv tail.val).drop (16 * (tail.length / 16)) := by
    rw [part_post, i1_post, hlanes]; simp [bv, List.map_drop]
  have hPl : (bv part.val).length = tail.length % 16 := by simp [bv, ← hpart, Slice.length]
  have hL : (core.num.U64.from_le_bytes length).bv = le64 (bv length.val) := u64_from_le_bytes_bv length
  split
  · rename_i hge
    have hge' : 8 ≤ part.length := by simpa [Slice.len, Slice.length] using hge
    step as ⟨s0, hs0, hs0l⟩
    step as ⟨r, hr⟩
    step as ⟨a, ha⟩
    · rcases r with v | e
      · exact ⟨v, rfl⟩
      · simp_all
    step as ⟨e0, he0⟩
    step as ⟨s1, hs1, hs1l⟩
    step with ended_spec s1 (by rw [hs1l]; omega) as ⟨e1, he1⟩
    step*
    all_goals
      have hlen1 : length1.bv = le64 (bv length.val) := by rw [length1_post]; exact hL
      have hav : a.val = part.val.take 8 := by
        subst ha; simp only at hr; rw [hr.1, hs0]; simp [List.slice]
      have he0' : e0.bv = le64 ((bv part.val).take 8) := by
        rw [he0, show (bv part.val).take 8 = bv a.val by simp [bv, hav, List.map_take]]
        exact u64_from_le_bytes_bv a
      have he1' : e1.bv = le64 ((bv part.val).drop 8 ++
          128#8 :: List.replicate (7 - ((bv part.val).drop 8).length) 0#8) := by
        rw [he1, show bv s1.val = (bv part.val).drop 8 by simp [bv, hs1, List.map_drop],
          show s1.length = ((bv part.val).drop 8).length by simp [bv, hs1l, Slice.length]]
      have hPk : 8 ≤ (bv part.val).length := by simp [bv, Slice.length] at hge' ⊢; omega
      have htl : tail.len.val = tail.length := rfl
      have hi5 : i5.val = tail.length + 9 := by rw [i5_post, i4_post, htl]
      simp only [Array.make_val, gt_iff_lt] at *
      rw [← hP, ← hPl, endLane_take_long _ hPk, endLane_drop_long _ hPk]
      have hc : ¬(tail.length + 9 ≤ 64 ∧ tail.length / 16 = 3) := by omega
      simp only [hc, ite_false]
      refine ⟨?_, hlen1, by simpa using he0', by simpa using he1'⟩
      split <;> scalar_tac
  · rename_i hge
    have hge' : part.length < 8 := by simp [Slice.len, Slice.length] at hge ⊢; omega
    step with ended_spec as ⟨w, hw⟩
    step*
    all_goals
      have hlen1 : length1.bv = le64 (bv length.val) := by rw [length1_post]; exact hL
      have hPk : (bv part.val).length < 8 := by simp [bv, Slice.length] at hge' ⊢; omega
      have hw' : w.bv = le64 (bv part.val ++ 128#8 :: List.replicate (7 - (bv part.val).length) 0#8) := by
        rw [hw]; simp [bv, Slice.length]
      have htl : tail.len.val = tail.length := rfl
      have hi5 : i5.val = tail.length + 9 := by rw [i5_post, i4_post, htl]
      simp only [Array.make_val, gt_iff_lt] at *
      rw [← hP, ← hPl, endLane_take_short _ hPk, endLane_drop_short _ hPk, le64_zero]
      first
      | (refine ⟨?_, hlen1, by simpa using hw', ?_⟩
         · split <;> scalar_tac
         · split
           · exfalso; scalar_tac
           · simp)
      | (refine ⟨by scalar_tac, hlen1, by simp [end1_post, Array.set_val_eq, hw'], ?_⟩
         split
         · simp [end1_post, Array.set_val_eq, i7_post1, i6_post, hlen1]
         · exfalso; scalar_tac)

/-! ## The padded blocks -/

/-- The block `sha256_shaext_padded` makes of a tail `T`'s words and lanes `A`, `B`, and `L` is
a block of bytes. -/
theorem shaextPadded_bytes (r : Nat) (T A B L : List Byte) (hA : A.length = 8) (hB : B.length = 8)
    (hL : L.length = 8) (hT : 16 * min r 3 ≤ T.length) :
    shaextPadded r (rind.spec.words T) (le64 A) (le64 B) (le64 L) =
      if r < 3 then rind.spec.words (T.take (16 * r) ++ A ++ B ++ List.replicate (40 - 16 * r) 0#8 ++ L)
      else rind.spec.words (T.take 48 ++ A ++ B) := by
  have hz : (0 : BitVec 64) = le64 (List.replicate 8 0#8) := le64_zero.symm
  have hZ : (List.replicate 8 0#8).length = 8 := by simp
  unfold shaextPadded
  rw [hz]
  simp only [shaextLane_le64 _ _ hA hB, shaextLane_le64 _ _ hZ hZ, shaextLane_le64 _ _ hZ hL]
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ 3 ≤ r by omega) with rfl | rfl | rfl | hr
  · simp only [ite_true, Nat.mul_zero, List.take_zero, List.nil_append, show (0 : Nat) < 3 by decide]
    simp (disch := simp [hA, hB, hL]) only [← words_append]
    congr 1
    simp [List.append_assoc]
  all_goals
    have hT' := hT
    simp only [Nat.min_def] at hT'
    have h4 := words_take T 4 (by split at hT' <;> omega)
    have h8 := fun h => words_take T 8 h
    have h12 := fun h => words_take T 12 h
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.reduceMul] at h4 h8 h12
  · simp only [show (1 : Nat) ≠ 0 by decide, show (1 : Nat) < 3 by decide, ite_false, ite_true, h4]
    simp (disch := simp [hA, hB, hL, List.length_take] <;> omega) only [← words_append]
    congr 1
    simp [List.append_assoc]
  · simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, show (2 : Nat) < 3 by decide,
      ite_false, ite_true, h8 (by omega)]
    simp (disch := simp [hA, hB, hL, List.length_take] <;> omega) only [← words_append]
    congr 1
    simp [List.append_assoc]
  · simp only [show r ≠ 0 by omega, show r ≠ 1 by omega, show r ≠ 2 by omega, show ¬ r < 3 by omega,
      ite_false, h12 (by split at hT' <;> omega)]
    simp (disch := simp [hA, hB, hL, List.length_take] <;> omega) only [← words_append]
    simp [List.append_assoc]

theorem hashBlocks_prefix (m m' : Nat → List (BitVec 32)) (H : List (BitVec 32)) (n : Nat)
    (h : ∀ i < n, m' i = m i) : s2n.hashBlocks m' H n = s2n.hashBlocks m H n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [s2n.hashBlocks, s2n.hashBlocks, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- `SHA256_SHAEXT_FINISH_BLOCKS`. -/
theorem hashBlocks_finish (m : Nat → List (BitVec 32)) (n r : Nat) (x y l : BitVec 64)
    (H : List (BitVec 32)) :
    s2n.hashBlocks (shaextFinishBlocks m n r x y l) H (if r = 4 then n + 2 else n + 1) =
      if r = 4 then s2n.block (shaextPadded 0 (m n) 0 0 l) (s2n.block (shaextPadded r (m n) x y l)
        (s2n.hashBlocks m H n))
      else s2n.block (shaextPadded r (m n) x y l) (s2n.hashBlocks m H n) := by
  have hp : s2n.hashBlocks (shaextFinishBlocks m n r x y l) H n = s2n.hashBlocks m H n :=
    hashBlocks_prefix _ _ _ _ fun i hi => by simp [shaextFinishBlocks, hi]
  split <;> simp [s2n.hashBlocks, hp, shaextFinishBlocks]

/-- The block or two the lanes `padded_spec` gives describe, compressed from `S`, are FIPS
180-4's last blocks of a message whose bytes past its whole blocks are `T`, closed by `L`. -/
theorem padded_blocks (T L : List Byte) (S : List (BitVec 32)) (hT : T.length < 64)
    (hL : L.length = 8) (hS : S.length = 8) :
    let E := T.drop (16 * (T.length / 16)) ++ 128#8 :: List.replicate (15 - T.length % 16) 0#8
    let r := if T.length + 9 ≤ 64 then T.length / 16 else 4
    let y := if T.length + 9 ≤ 64 ∧ T.length / 16 = 3 then le64 L else le64 (E.drop 8)
    (if r = 4 then s2n.block (shaextPadded 0 (rind.spec.words T) 0 0 (le64 L))
        (s2n.block (shaextPadded r (rind.spec.words T) (le64 (E.take 8)) y (le64 L)) S)
      else s2n.block (shaextPadded r (rind.spec.words T) (le64 (E.take 8)) y (le64 L)) S) =
      (blocks 64 (T ++ [128#8] ++ List.replicate (padZeros 64 8 T.length) 0#8 ++ L)).foldl
        sha256.compress S := by
  intro E r y
  have hP : (T.drop (16 * (T.length / 16))).length = T.length % 16 := by simp; omega
  have hTE : T.take (16 * (T.length / 16)) ++ E = T ++ 128#8 :: List.replicate (15 - T.length % 16) 0#8 := by
    simp only [E, ← List.append_assoc, List.take_append_drop]
  have hZ : (List.replicate 8 0#8).length = 8 := by simp
  have hE8 : (E.take 8).length = 8 := by simp [E]; omega
  have hD8 : (E.drop 8).length = 8 := by simp [E]; omega
  have hTr : T.take (16 * (T.length / 16)) ++ E.take 8 ++ E.drop 8 =
      T ++ 128#8 :: List.replicate (15 - T.length % 16) 0#8 := by
    rw [List.append_assoc, List.take_append_drop, hTE]
  have single : ∀ B : List Byte, B.length = 64 → blocks 64 B = [B] := fun B hB => by
    rw [blocks, ite_eq_left ⟨by decide, by omega⟩, List.take_of_length_le (by omega),
      List.drop_eq_nil_of_le (by omega), blocks_nil]
  by_cases hfit : T.length + 9 ≤ 64
  · have hr : r = T.length / 16 := by simp [r, hfit]
    have hr4 : r ≠ 4 := by omega
    have hpz : padZeros 64 8 T.length = 55 - T.length := by unfold padZeros; omega
    simp only [hr4, ite_false, hpz]
    have hB : (T ++ [128#8] ++ List.replicate (55 - T.length) 0#8 ++ L).length = 64 := by simp [hL]; omega
    rw [single _ hB, List.foldl_cons, List.foldl_nil, ← s2n.block_words _ _ hS hB]
    congr 1
    by_cases h3 : T.length / 16 = 3
    · have hy : y = le64 L := by simp [y, hfit, h3]
      rw [hy, hr, shaextPadded_bytes _ _ _ _ _ hE8 hL hL (by omega), ite_eq_right (by omega)]
      have hE' : E = T.drop (16 * (T.length / 16)) ++
          128#8 :: List.replicate (15 - (T.drop (16 * (T.length / 16))).length) 0#8 := by simp only [E, hP]
      rw [hE', endLane_take_short _ (by omega), show 48 = 16 * (T.length / 16) by omega,
        ← List.append_assoc (List.take _ T) (List.drop _ T), List.take_append_drop]
      congr 1
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      congr 2
      simp only [List.length_drop]
      congr 2; omega
    · have hy : y = le64 (E.drop 8) := by simp [y, h3]
      rw [hy, hr, shaextPadded_bytes _ _ _ _ _ hE8 hD8 hL (by omega), ite_eq_left (by omega), hTr]
      congr 1
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      congr 2
      rw [← List.append_assoc, List.replicate_append_replicate]
      congr 2; omega
  · have hr : r = 4 := by simp [r, hfit]
    have hy : y = le64 (E.drop 8) := by simp [y, hfit]
    have hpz : padZeros 64 8 T.length = 119 - T.length := by unfold padZeros; omega
    have hB1 : (T ++ 128#8 :: List.replicate (63 - T.length) 0#8).length = 64 := by simp; omega
    have hB2 : (List.replicate 56 0#8 ++ L).length = 64 := by simp [hL]
    have hsplit : T ++ [128#8] ++ List.replicate (119 - T.length) 0#8 ++ L =
        (T ++ 128#8 :: List.replicate (63 - T.length) 0#8) ++ (List.replicate 56 0#8 ++ L) := by
      rw [show 119 - T.length = (63 - T.length) + 56 by omega, ← List.replicate_append_replicate]
      simp
    simp only [hr, ite_true, hpz, hsplit]
    rw [blocks_append (by decide) _ _ (by rw [hB1]), single _ hB1, single _ hB2, List.singleton_append,
      List.foldl_cons, List.foldl_cons, List.foldl_nil, hy,
      shaextPadded_bytes _ _ _ _ _ hE8 hD8 hL (by omega), ite_eq_right (by omega),
      show (48 : Nat) = 16 * (T.length / 16) by omega, hTr,
      show (0 : BitVec 64) = le64 (List.replicate 8 0#8) from le64_zero.symm,
      shaextPadded_bytes _ _ _ _ _ hZ hZ hL (by omega), ite_eq_left (by omega)]
    have hB2' : (List.take 0 T ++ List.replicate 8 0#8 ++ List.replicate 8 0#8 ++
        List.replicate 40 0#8 ++ L) = List.replicate 56 0#8 ++ L := by simp
    rw [hB2', s2n.block_words _ _ (by simp [s2n.block]) hB2,
      show 15 - T.length % 16 = 63 - T.length by omega, s2n.block_words _ _ hS hB1]

end rind.x86_64.shaext

namespace rind.x86_64
open shaext

/-- `SHA256_COMPRESS_BLOCKS_SHAEXT_CORRECT`: for `n` blocks, none included, whose `i`th block's
`j`th word, read big-endian, is the `j`th word of `m i`, the state's eight words, read
little-endian, become `sha256_hash_blocks m state n`. -/
axiom sha256_compress_blocks_shaext_spec (t : low.x86_64.cpu.HaveSha256)
    (state : Std.Array U32 8#usize) (blocks : Slice U8) (hm : blocks.length % 64 = 0) :
    low.x86_64.sha256.sha256_compress_blocks_shaext state blocks t ⦃ r =>
      words r.val = s2n.hashBlocks (fun i => rind.spec.words (((bv blocks.val).drop (64 * i)).take 64))
        (words state.val) (blocks.length / 64) ⦄

/-- `SHA256_FINISH_SHAEXT_CORRECT`: for the message's `n` whole blocks, a lane count `r` of at
most 4 whose lanes the message holds after them, the end lane's words `x` and `y`, and the
length's word `l`, xmm2 and xmm1 hold the big-endian bytes of `sha256_hash_blocks` of
`sha256_shaext_finish_blocks`, over `n + 1` blocks, or `n + 2` when `r` is 4. -/
axiom finish_padded_spec (state : Std.Array U32 8#usize) (message : Slice U8)
    (p : low.x86_64.sha256.Padded) (t : low.x86_64.cpu.HaveSha256) (hr : p.lanes.val ≤ 4)
    (hl : 16 * min p.lanes.val 3 ≤ message.length % 64) :
    low.x86_64.sha256.finish_padded state message p t ⦃ r =>
      bv r.val = (s2n.hashBlocks
        (shaextFinishBlocks (fun i => rind.spec.words (((bv message.val).drop (64 * i)).take 64))
          (message.length / 64) p.lanes.val p.«end».val[0]!.bv p.«end».val[1]!.bv p.length.bv)
        (words state.val)
        (if p.lanes.val = 4 then message.length / 64 + 2 else message.length / 64 + 1)).flatMap
          BitVec.toBEBytes ⦄

/-- The SHA extensions' block function compresses every whole block. -/
theorem sha256_compress_blocks_shaext_compresses (t : low.x86_64.cpu.HaveSha256) :
    Compresses sha256.compress fun h b => low.x86_64.sha256.sha256_compress_blocks_shaext h b t := by
  intro h b hl
  apply WP.spec_mono (sha256_compress_blocks_shaext_spec t h b hl)
  intro r hr
  rw [hr]
  simpa [bv] using s2n.hashBlocks_eq (words h.val) (by simp [words]) (bv b.val)

/-- The SHA extensions' finish: the message padded and closed by `length`, its result's words
big-endian. -/
theorem sha256_finish_shaext_spec (t : low.x86_64.cpu.HaveSha256) (h : Std.Array U32 8#usize)
    (m : Slice U8) (length : Std.Array U8 8#usize) :
    low.x86_64.sha256.sha256_finish_shaext h m length t ⦃ r =>
      bv r.val = ((blocks 64 (bv (m.val ++ [128#u8] ++ List.replicate (padZeros 64 8 m.length) 0#u8 ++
        length.val))).foldl sha256.compress (words h.val)).flatMap BitVec.toBEBytes ⦄ := by
  unfold low.x86_64.sha256.sha256_finish_shaext
  simp only [core.slice.Slice.as_chunks, show (64#usize).val = 64 from rfl, show (64 : Nat) ≠ 0 by decide,
    ite_false, bind_ok]
  generalize htail : Slice.from (List.drop (m.length / 64 * 64) m.val) _ = tail
  have hTv : tail.val = m.val.drop (64 * (m.length / 64)) := by
    rw [← htail, Slice.from_val, Nat.mul_comm]
  have hTl : tail.length = m.length % 64 := by
    simp only [Slice.length, hTv, List.length_drop]; omega
  step with padded_spec tail length (by omega) as ⟨p, hl, hlen, he0, he1⟩
  step with finish_padded_spec h m p t (by rw [hl]; split <;> omega)
    (by rw [hl, hTl]; split <;> omega) as ⟨r, hr⟩
  rw [hr]
  congr 1
  have hH : (words h.val).length = 8 := by simp [words]
  have hTlen : (bv tail.val).length = tail.length := by simp [bv, Slice.length]
  have hT : bv tail.val = (bv m.val).drop (64 * (m.length / 64)) := by simp [bv, hTv, List.map_drop]
  have hmn : ((bv m.val).drop (64 * (m.length / 64))).take 64 = bv tail.val := by
    rw [← hT, List.take_of_length_le (by omega)]
  rw [hashBlocks_finish]
  simp only [hmn]
  rw [← hTlen] at hl he0 he1
  rw [hl, he0, he1, hlen]
  have key := padded_blocks (bv tail.val) (bv length.val)
    (s2n.hashBlocks (fun i => rind.spec.words (((bv m.val).drop (64 * i)).take 64)) (words h.val)
      (m.length / 64)) (by omega) (by simp [bv]) (s2n.length_hashBlocks _ _ hH _)
  simp only at key
  rw [key]
  generalize hW : (bv m.val).take (64 * (m.length / 64)) = W
  have hWl : W.length = 64 * (m.length / 64) := by
    rw [← hW]; simp only [List.length_take, bv, List.length_map, Slice.length] at *; omega
  have hpre := s2n.hashBlocks_eq (words h.val) hH W
  rw [show W.length / 64 = m.length / 64 by omega] at hpre
  rw [hashBlocks_prefix (fun i => rind.spec.words ((W.drop (64 * i)).take 64)) _ _ _ (fun i hi => by
    simp only [← hW, List.drop_take, List.take_take]
    congr 2; omega), hpre]
  have hpz : padZeros 64 8 (bv tail.val).length = padZeros 64 8 m.length := by
    rw [hTlen, hTl]; unfold padZeros; omega
  have hbv : bv (m.val ++ [128#u8] ++ List.replicate (padZeros 64 8 m.length) 0#u8 ++ length.val) =
      W ++ (bv tail.val ++ [128#8] ++ List.replicate (padZeros 64 8 (bv tail.val).length) 0#8 ++
        bv length.val) := by
    rw [hpz, hT, ← hW]
    simp only [bv, List.map_append, List.map_cons, List.map_nil, List.map_replicate, ← List.append_assoc,
      List.take_append_drop]
    rfl
  rw [hbv, blocks_append (by decide) W _ (by rw [hWl]; omega), List.foldl_append]

end rind.x86_64
