import Rind.Armv7.AesNohwBlock
open Aeneas Aeneas.Std Result rind.vale rind.simd

/-!
# The bitsliced AES's key schedule

`setup_key_128`, `setup_key_192`, and `setup_key_256` expand a key into
FIPS 197's round keys, each in compact form.
-/

namespace rind.armv7

open low.portable.aes_nohw

/-! ## The word operations -/

/-- `rcon_slice`: bits `2j` and `2j + 1` of the round constant. -/
def rconSlice (rc : BitVec 8) (j : Nat) : BitVec 32 := ((rc >>> (2 * j)) &&& 3#8).setWidth 32

@[step]
theorem rcon_slice_spec (rc : U8) (j : Usize) (hj : j.val < 4) :
    word.rcon_slice rc j ⦃ r => r.bv = rconSlice rc.bv j.val ⦄ := by
  unfold word.rcon_slice
  simp only [word.BATCH_SIZE, lift, bind_ok]
  step*
  have h3 : i4.bv = 3#8 := by
    apply BitVec.eq_of_toNat_eq; rw [← UScalar.val, i4_post, i3_post]; simp [U8.size, U8.numBits]
  have h1 : i1.val = 2 * j.val := by rw [i1_post]; ring
  simp only [core.convert.num.FromU32U8.from_bv_eq, UScalar.bv_and, i2_post1, h3, h1, rconSlice]

/-- `propagate` on a word's bits. -/
def propagateW (v : BitVec 32) : BitVec 32 := v ^^^ v <<< 8 ^^^ (v <<< 16 ^^^ v <<< 24)

@[step]
theorem propagate_spec (v : U32) : propagate v ⦃ r => r.bv = propagateW v.bv ⦄ := by
  unfold propagate
  step*
  simp_all [propagateW]

/-- `sub_block` applies the S-box to each byte of a compact block. -/
@[step]
theorem sub_block_spec (input : Std.Array U32 4#usize) :
    sub_block input ⦃ r => ∀ m < 16,
      cByte r.val[0]!.bv r.val[1]!.bv r.val[2]!.bv r.val[3]!.bv m =
        sbox (cByte input.val[0]!.bv input.val[1]!.bv input.val[2]!.bv input.val[3]!.bv m) ⦄ := by
  unfold sub_block
  step with set_spec EMPTY input 0#usize (by decide) as ⟨b, hb⟩
  step with transpose_block b as ⟨b1, hb1⟩
  step with sub_bytes_spec b1 as ⟨b2, hb2⟩
  step with transpose_block b2 as ⟨b3, hb3⟩
  apply WP.spec_mono (get_spec b3 0#usize (by decide))
  intro r hr m hm
  have e : ∀ k < 4, (r.val[k]!).bv = b3.bv (2 * k) := by
    intro k hk; rw [hr k hk]; rfl
  have e' : ∀ k < 4, (input.val[k]!).bv = b.bv (2 * k) := by
    intro k hk; simp only [Batch.bv, hb (2 * k) (by omega)]; simp
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e' 0 (by decide),
    e' 1 (by decide), e' 2 (by decide), e' 3 (by decide)]
  have h3 := (hb3 0 (by decide) m hm).2
  have h1 := (hb1 0 (by decide) m hm).1
  simp only [Batch.cblock, Nat.add_zero] at h3 h1
  rw [h3, hb2 _ (by omega), h1]

/-! ## A round key from the one before -/

/-- The block four compact words hold. -/
def cQ (c0 c1 c2 c3 : BitVec 32) : Quad32 := ofBytes (cByte c0 c1 c2 c3)

theorem compactQ_eq (c : Std.Array U32 4#usize) :
    compactQ c = cQ c.val[0]!.bv c.val[1]!.bv c.val[2]!.bv c.val[3]!.bv := rfl

/-- `rotate_rows_down` on a word's bits. -/
def rotRowsDown (v : BitVec 32) : BitVec 32 := (v >>> 2 &&& 0x3f3f3f3f#32) ||| (v <<< 6 &&& 0xc0c0c0c0#32)

/-- A word of the round key after `b`, whose first word adds the round
constant `rc` and `RotWord` and `SubWord` of the last of the key `s` is the
S-box of. -/
def rotStepW (b s : BitVec 32) (rc : BitVec 8) (j : Nat) : BitVec 32 :=
  propagateW (b ^^^ rconSlice rc j ^^^ rotRowsDown s >>> 24)

/-- A word of the round key after `b`, whose first word adds `SubWord` of the
last of the key `s` is the S-box of. -/
def subStepW (b s : BitVec 32) : BitVec 32 := propagateW (b ^^^ s >>> 24)

theorem rot_step (b0 b1 b2 b3 s0 s1 s2 s3 : BitVec 32) (u : Quad32) (rc : BitVec 8)
    (hs : ∀ m < 16, sbox (byte u m) = cByte s0 s1 s2 s3 m) :
    cQ (rotStepW b0 s0 rc 0) (rotStepW b1 s1 rc 1) (rotStepW b2 s2 rc 2) (rotStepW b3 s3 rc 3) =
      nextKey (cQ b0 b1 b2 b3) (subWord (rotWord (lane32 u 3)) ^^^ rc.setWidth 32) := by
  apply eq_of_byte_eq; intro m hm
  simp only [cQ, byte_ofBytes _ hm]
  interval_cases m <;>
    simp (disch := decide) only [nextKey, byte_mkfour, wbyte_xor, wbyte_lane32, byte_ofBytes, wbyte_subWord,
      wbyte_rotWord, hs, Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, ite_true, ite_false] <;>
    simp only [cByte, rotStepW, rconSlice, propagateW, rotRowsDown, wbyte] <;>
    bv_decide

theorem sub_step (b0 b1 b2 b3 s0 s1 s2 s3 : BitVec 32) (u : Quad32)
    (hs : ∀ m < 16, sbox (byte u m) = cByte s0 s1 s2 s3 m) :
    cQ (subStepW b0 s0) (subStepW b1 s1) (subStepW b2 s2) (subStepW b3 s3) =
      nextKey (cQ b0 b1 b2 b3) (subWord (lane32 u 3)) := by
  apply eq_of_byte_eq; intro m hm
  simp only [cQ, byte_ofBytes _ hm]
  interval_cases m <;>
    simp (disch := decide) only [nextKey, byte_mkfour, wbyte_xor, wbyte_lane32, byte_ofBytes, wbyte_subWord,
      hs, Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, ite_true, ite_false] <;>
    simp only [cByte, subStepW, propagateW] <;>
    bv_decide

/-! ## AES-192's two steps

`setup_key_192` holds six words of the schedule a step, four in one block and
two in the first half of another, as `Rind.Aes`'s `key192` does. -/

/-- The second block's word after the first step: the two words it held, then
the next step's first two. -/
def step192A2 (b1 b2 s : BitVec 32) (rc : BitVec 8) (j : Nat) : BitVec 32 :=
  let x := b2 ||| (b1 ^^^ rconSlice rc j) <<< 16
  let x := x ^^^ (rotRowsDown s <<< 8 &&& 0x00ff0000#32)
  x ^^^ (x <<< 8 &&& 0xff000000#32)

/-- The first block's word after the first step: the next step's last four. -/
def step192A1 (b1 b2' : BitVec 32) : BitVec 32 := propagateW ((b1 >>> 16 ||| b2' <<< 16) ^^^ b2' >>> 24)

/-- The second block's word after the second step: the next step's first four. -/
def step192B2 (b1 b2 s : BitVec 32) (rc : BitVec 8) (j : Nat) : BitVec 32 :=
  propagateW ((b2 >>> 16 ||| b1 <<< 16) ^^^ rconSlice rc j ^^^ rotRowsDown s >>> 24)

/-- The first block's word after the second step: the next step's last two. -/
def step192B1 (b1 b2' : BitVec 32) : BitVec 32 :=
  let t := b1 >>> 16 ^^^ b2' >>> 24
  (t ^^^ t <<< 8) &&& 0x0000ffff#32

theorem step192_a (a0 a1 a2 a3 x0 x1 x2 x3 s0 s1 s2 s3 : BitVec 32) (u : Quad32) (rc : BitVec 8)
    (hs : ∀ m < 16, sbox (byte u m) = cByte s0 s1 s2 s3 m)
    (hz : ∀ m, 8 ≤ m → m < 16 → cByte x0 x1 x2 x3 m = 0) :
    let X := cQ x0 x1 x2 x3
    let N := nextKey (cQ a0 a1 a2 a3) (subWord (rotWord (lane32 u 1)) ^^^ rc.setWidth 32)
    cQ (step192A2 a0 x0 s0 rc 0) (step192A2 a1 x1 s1 rc 1) (step192A2 a2 x2 s2 rc 2) (step192A2 a3 x3 s3 rc 3) =
        mkfour (lane32 X 0) (lane32 X 1) (lane32 N 0) (lane32 N 1) ∧
      cQ (step192A1 a0 (step192A2 a0 x0 s0 rc 0)) (step192A1 a1 (step192A2 a1 x1 s1 rc 1))
          (step192A1 a2 (step192A2 a2 x2 s2 rc 2)) (step192A1 a3 (step192A2 a3 x3 s3 rc 3)) =
        mkfour (lane32 N 2) (lane32 N 3) (lane32 X 0 ^^^ lane32 N 3) (lane32 X 1 ^^^ (lane32 X 0 ^^^ lane32 N 3)) := by
  intro X N
  have z8 := hz 8 (by decide) (by decide)
  have z9 := hz 9 (by decide) (by decide)
  have z10 := hz 10 (by decide) (by decide)
  have z11 := hz 11 (by decide) (by decide)
  have z12 := hz 12 (by decide) (by decide)
  have z13 := hz 13 (by decide) (by decide)
  have z14 := hz 14 (by decide) (by decide)
  have z15 := hz 15 (by decide) (by decide)
  simp only [cByte] at z8 z9 z10 z11 z12 z13 z14 z15
  constructor <;> apply eq_of_byte_eq <;> intro m hm <;> simp only [cQ, byte_ofBytes _ hm] <;>
    interval_cases m <;>
    simp (disch := decide) only [X, N, cQ, nextKey, byte_mkfour, wbyte_xor, wbyte_lane32, byte_ofBytes,
      wbyte_subWord, wbyte_rotWord, hs, Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, ite_true,
      ite_false] <;>
    simp only [cByte, step192A2, step192A1, rconSlice, propagateW, rotRowsDown, wbyte] <;>
    bv_decide

theorem step192_b (y0 y1 y2 y3 x0 x1 x2 x3 s0 s1 s2 s3 : BitVec 32) (u : Quad32) (rc : BitVec 8)
    (hs : ∀ m < 16, sbox (byte u m) = cByte s0 s1 s2 s3 m) :
    let X := cQ x0 x1 x2 x3
    let Y := cQ y0 y1 y2 y3
    let O := cQ (step192B2 y0 x0 s0 rc 0) (step192B2 y1 x1 s1 rc 1) (step192B2 y2 x2 s2 rc 2)
      (step192B2 y3 x3 s3 rc 3)
    O = nextKey (mkfour (lane32 X 2) (lane32 X 3) (lane32 Y 0) (lane32 Y 1))
        (subWord (rotWord (lane32 u 3)) ^^^ rc.setWidth 32) ∧
      cQ (step192B1 y0 (step192B2 y0 x0 s0 rc 0)) (step192B1 y1 (step192B2 y1 x1 s1 rc 1))
          (step192B1 y2 (step192B2 y2 x2 s2 rc 2)) (step192B1 y3 (step192B2 y3 x3 s3 rc 3)) =
        mkfour (lane32 Y 2 ^^^ lane32 O 3) (lane32 Y 3 ^^^ (lane32 Y 2 ^^^ lane32 O 3)) 0 0 := by
  intro X Y O
  constructor <;> apply eq_of_byte_eq <;> intro m hm <;> simp only [O, cQ, byte_ofBytes _ hm] <;>
    interval_cases m <;>
    simp (disch := decide) only [X, Y, cQ, nextKey, byte_mkfour, wbyte_xor, wbyte_lane32, byte_ofBytes,
      wbyte_subWord, wbyte_rotWord, hs, Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, ite_true,
      ite_false] <;>
    simp only [cByte, step192B2, step192B1, rconSlice, propagateW, rotRowsDown, wbyte] <;>
    bv_decide

/-! ## The loops over a block's words -/

/-- `setup_key_128`'s inner loop: words `iter.start` on of the next round key. -/
theorem setup_key_128_inner_spec (b0 : Std.Array U32 4#usize) (i : Usize) (sub : Std.Array U32 4#usize)
    (hi1 : 1 ≤ i.val) (hi : i.val ≤ 10) (iter : core.ops.range.Range Usize) (b : Std.Array U32 4#usize)
    (hs : iter.start.val ≤ 4) (he : iter.end.val = 4)
    (hb : ∀ j < 4, (b.val[j]!).bv =
      if j < iter.start.val then rotStepW (b0.val[j]!).bv (sub.val[j]!).bv (RCON.val[i.val - 1]!).bv j
      else (b0.val[j]!).bv) :
    setup_key_128_loop0_loop0 iter b i sub ⦃ r => ∀ j < 4,
      (r.val[j]!).bv = rotStepW (b0.val[j]!).bv (sub.val[j]!).bv (RCON.val[i.val - 1]!).bv j ⦄ := by
  unfold setup_key_128_loop0_loop0
  apply loop.spec_decr_nat (fun x => 4 - x.1.start.val)
    (fun x => x.1.start.val ≤ 4 ∧ x.1.end.val = 4 ∧ ∀ j < 4, (x.2.val[j]!).bv =
      if j < x.1.start.val then rotStepW (b0.val[j]!).bv (sub.val[j]!).bv (RCON.val[i.val - 1]!).bv j
      else (b0.val[j]!).bv)
  · rintro ⟨it, st⟩ ⟨hs, he, hst⟩
    simp only at hs he hst ⊢
    unfold setup_key_128_loop0_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step*
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro j hj
      rw [a_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
      split_ifs with h1 h2 h2
      · subst h1
        have hb0 := hst it.start.val hj
        rw [ite_eq_right (by omega)] at hb0
        have h3 : i3 = RCON.val[i.val - 1]! := by rw [i3_post, ← getElem!_pos, i2_post]
        rw [i8_post, w1_post, w_post, i4_post, i7_post, i6_post, i1_post, h3, i5_post,
          ← getElem!_pos, ← getElem!_pos, hb0, rotStepW, rotRowsDown]
      · omega
      · rw [hst j hj, ite_eq_left (by omega)]
      · rw [hst j hj, ite_eq_right (by omega)]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      intro j hj
      rw [hst j hj, ite_eq_left (by omega)]
  · exact ⟨hs, he, hb⟩

/-- `setup_key_256`'s first inner loop. -/
theorem setup_key_256_inner_a_spec (b0 : Std.Array U32 4#usize) (half : Usize) (sub : Std.Array U32 4#usize)
    (hi1 : 1 ≤ half.val) (hi : half.val ≤ 7) (iter : core.ops.range.Range Usize) (b : Std.Array U32 4#usize)
    (hs : iter.start.val ≤ 4) (he : iter.end.val = 4)
    (hb : ∀ j < 4, (b.val[j]!).bv =
      if j < iter.start.val then rotStepW (b0.val[j]!).bv (sub.val[j]!).bv (RCON.val[half.val - 1]!).bv j
      else (b0.val[j]!).bv) :
    setup_key_256_loop0_loop0 iter b half sub ⦃ r => ∀ j < 4,
      (r.val[j]!).bv = rotStepW (b0.val[j]!).bv (sub.val[j]!).bv (RCON.val[half.val - 1]!).bv j ⦄ := by
  unfold setup_key_256_loop0_loop0
  apply loop.spec_decr_nat (fun x => 4 - x.1.start.val)
    (fun x => x.1.start.val ≤ 4 ∧ x.1.end.val = 4 ∧ ∀ j < 4, (x.2.val[j]!).bv =
      if j < x.1.start.val then rotStepW (b0.val[j]!).bv (sub.val[j]!).bv (RCON.val[half.val - 1]!).bv j
      else (b0.val[j]!).bv)
  · rintro ⟨it, st⟩ ⟨hs, he, hst⟩
    simp only at hs he hst ⊢
    unfold setup_key_256_loop0_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step*
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro j hj
      rw [a_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
      split_ifs with h1 h2 h2
      · subst h1
        have hb0 := hst it.start.val hj
        rw [ite_eq_right (by omega)] at hb0
        have h3 : i2 = RCON.val[half.val - 1]! := by rw [i2_post, ← getElem!_pos, i1_post]
        rw [i8_post, i7_post, w_post, i3_post, i6_post, i5_post, i_post, h3, i4_post,
          ← getElem!_pos, ← getElem!_pos, hb0, rotStepW, rotRowsDown]
      · omega
      · rw [hst j hj, ite_eq_left (by omega)]
      · rw [hst j hj, ite_eq_right (by omega)]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      intro j hj
      rw [hst j hj, ite_eq_left (by omega)]
  · exact ⟨hs, he, hb⟩

/-- `setup_key_256`'s second inner loop. -/
theorem setup_key_256_inner_b_spec (b0 : Std.Array U32 4#usize) (sub : Std.Array U32 4#usize)
    (iter : core.ops.range.Range Usize) (b : Std.Array U32 4#usize)
    (hs : iter.start.val ≤ 4) (he : iter.end.val = 4)
    (hb : ∀ j < 4, (b.val[j]!).bv =
      if j < iter.start.val then subStepW (b0.val[j]!).bv (sub.val[j]!).bv
      else (b0.val[j]!).bv) :
    setup_key_256_loop0_loop1 iter b sub ⦃ r => ∀ j < 4,
      (r.val[j]!).bv = subStepW (b0.val[j]!).bv (sub.val[j]!).bv ⦄ := by
  unfold setup_key_256_loop0_loop1
  apply loop.spec_decr_nat (fun x => 4 - x.1.start.val)
    (fun x => x.1.start.val ≤ 4 ∧ x.1.end.val = 4 ∧ ∀ j < 4, (x.2.val[j]!).bv =
      if j < x.1.start.val then subStepW (b0.val[j]!).bv (sub.val[j]!).bv
      else (b0.val[j]!).bv)
  · rintro ⟨it, st⟩ ⟨hs, he, hst⟩
    simp only at hs he hst ⊢
    unfold setup_key_256_loop0_loop1.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step*
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro j hj
      rw [a_post, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
      split_ifs with h1 h2 h2
      · subst h1
        have hb0 := hst it.start.val hj
        rw [ite_eq_right (by omega)] at hb0
        rw [i4_post, i3_post, i2_post, i_post, i1_post, ← getElem!_pos, ← getElem!_pos, hb0, subStepW]
      · omega
      · rw [hst j hj, ite_eq_left (by omega)]
      · rw [hst j hj, ite_eq_right (by omega)]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      intro j hj
      rw [hst j hj, ite_eq_left (by omega)]
  · exact ⟨hs, he, hb⟩

/-- `setup_key_192`'s first inner loop. -/
theorem setup_key_192_inner_a_spec (B1 B2 : Std.Array U32 4#usize) (i : Usize) (sub : Std.Array U32 4#usize)
    (hi : i.val < 4) (iter : core.ops.range.Range Usize) (b1 b2 : Std.Array U32 4#usize)
    (hs : iter.start.val ≤ 4) (he : iter.end.val = 4)
    (hb1 : ∀ j < 4, (b1.val[j]!).bv = if j < iter.start.val then
      step192A1 (B1.val[j]!).bv (step192A2 (B1.val[j]!).bv (B2.val[j]!).bv (sub.val[j]!).bv
        (RCON.val[2 * i.val]!).bv j) else (B1.val[j]!).bv)
    (hb2 : ∀ j < 4, (b2.val[j]!).bv = if j < iter.start.val then
      step192A2 (B1.val[j]!).bv (B2.val[j]!).bv (sub.val[j]!).bv (RCON.val[2 * i.val]!).bv j
      else (B2.val[j]!).bv) :
    setup_key_192_loop0_loop0 iter b1 b2 i sub ⦃ r => ∀ j < 4,
      (r.1.val[j]!).bv = step192A1 (B1.val[j]!).bv (step192A2 (B1.val[j]!).bv (B2.val[j]!).bv (sub.val[j]!).bv
        (RCON.val[2 * i.val]!).bv j) ∧
      (r.2.val[j]!).bv = step192A2 (B1.val[j]!).bv (B2.val[j]!).bv (sub.val[j]!).bv (RCON.val[2 * i.val]!).bv j ⦄ := by
  unfold setup_key_192_loop0_loop0
  apply loop.spec_decr_nat (fun x => 4 - x.1.start.val)
    (fun x => x.1.start.val ≤ 4 ∧ x.1.end.val = 4 ∧
      (∀ j < 4, (x.2.1.val[j]!).bv = if j < x.1.start.val then
        step192A1 (B1.val[j]!).bv (step192A2 (B1.val[j]!).bv (B2.val[j]!).bv (sub.val[j]!).bv
          (RCON.val[2 * i.val]!).bv j) else (B1.val[j]!).bv) ∧
      ∀ j < 4, (x.2.2.val[j]!).bv = if j < x.1.start.val then
        step192A2 (B1.val[j]!).bv (B2.val[j]!).bv (sub.val[j]!).bv (RCON.val[2 * i.val]!).bv j
        else (B2.val[j]!).bv)
  · rintro ⟨it, st1, st2⟩ ⟨hs, he, hst1, hst2⟩
    simp only at hs he hst1 hst2 ⊢
    unfold setup_key_192_loop0_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step*
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, ?_, ?_, by omega⟩ <;> intro j hj <;>
        simp only [index_mut_back_post, index_mut_back1_post, Std.Array.set_val_eq] <;>
        rw [getElem!_set _ _ _ (by simp; omega)] <;> split_ifs with h1 h2 h2 <;> try omega
      all_goals try first
        | rw [hst1 j hj, ite_eq_left (by omega)] | rw [hst1 j hj, ite_eq_right (by omega)]
        | rw [hst2 j hj, ite_eq_left (by omega)] | rw [hst2 j hj, ite_eq_right (by omega)]
      all_goals subst h1
      all_goals
        have hv1 : b1.bv = (B1.val[it.start.val]!).bv := by
          have := hst1 it.start.val hj; rw [ite_eq_right (by omega)] at this; rw [b1_post, ← getElem!_pos, this]
        have hv2 : b2.bv = (B2.val[it.start.val]!).bv := by
          have := hst2 it.start.val hj; rw [ite_eq_right (by omega)] at this; rw [b2_post, ← getElem!_pos, this]
        have hrc : i2 = RCON.val[2 * i.val]! := by rw [i2_post, ← getElem!_pos, i1_post]
        have hsv : i6 = sub.val[it.start.val]! := by rw [i6_post, ← getElem!_pos]
        have hc2 : word.COL2.bv = 0x00ff0000#32 := by unfold word.COL2; rfl
        have hc3 : word.COL3.bv = 0xff000000#32 := by unfold word.COL3; rfl
        simp only [b12_post, i15_post, b11_post, i12_post, i13_post, i14_post, b23_post, b22_post, b21_post,
          i5_post, i4_post, i3_post, i9_post, i8_post, i7_post, i11_post, i10_post, hv1, hv2, hsv, hrc, hc2, hc3,
          step192A1, step192A2, rotRowsDown]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      intro j hj
      rw [hst1 j hj, hst2 j hj, ite_eq_left (by omega), ite_eq_left (by omega)]
      exact ⟨rfl, rfl⟩
  · exact ⟨hs, he, hb1, hb2⟩

/-- `setup_key_192`'s second inner loop. -/
theorem setup_key_192_inner_b_spec (B1 B2 : Std.Array U32 4#usize) (i : Usize) (sub : Std.Array U32 4#usize)
    (hi : i.val < 4) (iter : core.ops.range.Range Usize) (b1 b2 : Std.Array U32 4#usize)
    (hs : iter.start.val ≤ 4) (he : iter.end.val = 4)
    (hb1 : ∀ j < 4, (b1.val[j]!).bv = if j < iter.start.val then
      step192B1 (B1.val[j]!).bv (step192B2 (B1.val[j]!).bv (B2.val[j]!).bv (sub.val[j]!).bv
        (RCON.val[2 * i.val + 1]!).bv j) else (B1.val[j]!).bv)
    (hb2 : ∀ j < 4, (b2.val[j]!).bv = if j < iter.start.val then
      step192B2 (B1.val[j]!).bv (B2.val[j]!).bv (sub.val[j]!).bv (RCON.val[2 * i.val + 1]!).bv j
      else (B2.val[j]!).bv) :
    setup_key_192_loop0_loop1 iter b1 b2 i sub ⦃ r => ∀ j < 4,
      (r.1.val[j]!).bv = step192B1 (B1.val[j]!).bv (step192B2 (B1.val[j]!).bv (B2.val[j]!).bv (sub.val[j]!).bv
        (RCON.val[2 * i.val + 1]!).bv j) ∧
      (r.2.val[j]!).bv = step192B2 (B1.val[j]!).bv (B2.val[j]!).bv (sub.val[j]!).bv (RCON.val[2 * i.val + 1]!).bv j ⦄ := by
  unfold setup_key_192_loop0_loop1
  apply loop.spec_decr_nat (fun x => 4 - x.1.start.val)
    (fun x => x.1.start.val ≤ 4 ∧ x.1.end.val = 4 ∧
      (∀ j < 4, (x.2.1.val[j]!).bv = if j < x.1.start.val then
        step192B1 (B1.val[j]!).bv (step192B2 (B1.val[j]!).bv (B2.val[j]!).bv (sub.val[j]!).bv
          (RCON.val[2 * i.val + 1]!).bv j) else (B1.val[j]!).bv) ∧
      ∀ j < 4, (x.2.2.val[j]!).bv = if j < x.1.start.val then
        step192B2 (B1.val[j]!).bv (B2.val[j]!).bv (sub.val[j]!).bv (RCON.val[2 * i.val + 1]!).bv j
        else (B2.val[j]!).bv)
  · rintro ⟨it, st1, st2⟩ ⟨hs, he, hst1, hst2⟩
    simp only at hs he hst1 hst2 ⊢
    unfold setup_key_192_loop0_loop1.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step*
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, ?_, ?_, by omega⟩ <;> intro j hj <;>
        simp only [index_mut_back_post, index_mut_back1_post, Std.Array.set_val_eq] <;>
        rw [getElem!_set _ _ _ (by simp; omega)] <;> split_ifs with h1 h2 h2 <;> try omega
      all_goals try first
        | rw [hst1 j hj, ite_eq_left (by omega)] | rw [hst1 j hj, ite_eq_right (by omega)]
        | rw [hst2 j hj, ite_eq_left (by omega)] | rw [hst2 j hj, ite_eq_right (by omega)]
      all_goals subst h1
      all_goals
        have hv1 : b1.bv = (B1.val[it.start.val]!).bv := by
          have := hst1 it.start.val hj; rw [ite_eq_right (by omega)] at this; rw [b1_post, ← getElem!_pos, this]
        have hv2 : b2.bv = (B2.val[it.start.val]!).bv := by
          have := hst2 it.start.val hj; rw [ite_eq_right (by omega)] at this; rw [b2_post, ← getElem!_pos, this]
        have hrc : i5 = RCON.val[2 * i.val + 1]! := by rw [i5_post, ← getElem!_pos, i4_post, i3_post]
        have hsv : i7 = sub.val[it.start.val]! := by rw [i7_post, ← getElem!_pos]
        have hc : word.COL01.bv = 0x0000ffff#32 := by unfold word.COL01; rfl
        simp only [b14_post, b13_post, i12_post, b12_post, i11_post, b11_post, b23_post, i10_post, i9_post,
          i8_post, b22_post, i6_post, b21_post, i1_post, i2_post, hv1, hv2, hsv, hrc, hc, step192B1, step192B2,
          rotRowsDown]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      intro j hj
      rw [hst1 j hj, hst2 j hj, ite_eq_left (by omega), ite_eq_left (by omega)]
      exact ⟨rfl, rfl⟩
  · exact ⟨hs, he, hb1, hb2⟩

/-! ## The schedules -/

theorem rcon_eq {r : Nat} (hr : r < 10) : (RCON.val[r]!).bv.setWidth 32 = aesRcon r := by
  interval_cases r <;> (unfold RCON; decide)

/-- A compact block from its words' bits. -/
theorem compactQ_of (c : Std.Array U32 4#usize) (f : Nat → BitVec 32) (h : ∀ j < 4, (c.val[j]!).bv = f j) :
    compactQ c = cQ (f 0) (f 1) (f 2) (f 3) := by
  rw [compactQ_eq, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

/-- `sub_block_spec`, as the S-box of a compact block's bytes. -/
theorem sbox_compactQ (b s : Std.Array U32 4#usize)
    (h : ∀ m < 16, cByte s.val[0]!.bv s.val[1]!.bv s.val[2]!.bv s.val[3]!.bv m =
      sbox (cByte b.val[0]!.bv b.val[1]!.bv b.val[2]!.bv b.val[3]!.bv m)) :
    ∀ m < 16, sbox (byte (compactQ b) m) = cByte s.val[0]!.bv s.val[1]!.bv s.val[2]!.bv s.val[3]!.bv m := by
  intro m hm
  rw [h m hm, compactQ, byte_ofBytes _ hm]

/-- The words of a key, as Vale takes them. -/
def keyWords {n : Usize} (key : Std.Array U8 n) : List (BitVec 32) := seqNat8ToSeqNat32LE (key.val.map (·.bv))

/-- `setup_key_128`'s outer loop: from round key `n - 1`, held in `block`, it
writes the rest. -/
theorem setup_key_128_loop_spec (kw : List (BitVec 32)) (iter : core.ops.range.RangeInclusive Usize)
    (rd : Std.Array (Std.Array U32 4#usize) 15#usize) (block : Std.Array U32 4#usize)
    (he : iter.end.val = 10) (hs1 : 1 ≤ iter.start.val) (hs : iter.start.val ≤ 10) (hx : iter.exhausted = false)
    (hb : compactQ block = roundKey .AES_128 kw (iter.start.val - 1))
    (hr : ∀ k < iter.start.val, compactQ rd.val[k]! = roundKey .AES_128 kw k) :
    setup_key_128_loop0 iter rd block ⦃ r => ∀ k ≤ 10, compactQ r.val[k]! = roundKey .AES_128 kw k ⦄ := by
  unfold setup_key_128_loop0
  apply loop.spec_decr_nat (fun x => if x.1.exhausted then 0 else 11 - x.1.start.val)
    (fun x => x.1.end.val = 10 ∧ 1 ≤ x.1.start.val ∧ x.1.start.val ≤ 10 ∧
      compactQ x.2.2 = roundKey .AES_128 kw ((if x.1.exhausted then 11 else x.1.start.val) - 1) ∧
      ∀ k < (if x.1.exhausted then 11 else x.1.start.val), compactQ x.2.1.val[k]! = roundKey .AES_128 kw k)
  · rintro ⟨it, rd, b⟩ ⟨he, hs1, hs, hb, hr⟩
    simp only at he hs1 hs hb hr ⊢
    unfold setup_key_128_loop0.body
    step with core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec as ⟨o, it', ho⟩
    split_ifs at ho with h1 h2
    · obtain ⟨rfl, -⟩ := ho
      simp only [WP.spec_ok]
      intro k hk
      by_cases hx : it.exhausted
      · simp only [hx, ↓reduceIte] at hr; exact hr k (by omega)
      · have : it.end.val < it.start.val := by simpa [hx] using h1
        omega
    all_goals
      obtain ⟨rfl, hst', hen, hex⟩ := ho
      have hx : it.exhausted = false := by simpa using (not_or.mp h1).1
      simp only [hx, Bool.false_eq_true, ↓reduceIte] at hb hr
      step with sub_block_spec b as ⟨sub, hsub⟩
      step with setup_key_128_inner_spec b it.start sub hs1 hs { start := 0#usize, «end» := word.BLOCK_WORDS } b
        (by simp) (by simp [word.BLOCK_WORDS])
        (by intro j hj; simp) as ⟨b1, hb1⟩
      step as ⟨a, ha⟩
      have hq : compactQ b1 = roundKey .AES_128 kw it.start.val := by
        rw [compactQ_of b1 _ hb1, rot_step _ _ _ _ _ _ _ _ (compactQ b) _ (sbox_compactQ b sub hsub), ← compactQ_eq,
          hb, rcon_eq (by omega)]
        obtain ⟨n, hn⟩ : ∃ n, it.start.val = n + 1 := ⟨it.start.val - 1, by omega⟩
        rw [hn, Nat.add_sub_cancel, roundKey128_succ]
        simp only [roundKey, (lane32_mkfour _ _ _ _).2.2.2]
      have hn' : (if it'.exhausted then 11 else it'.start.val) = it.start.val + 1 := by
        rw [hex]; simp only [Bool.false_eq_true, ↓reduceIte]
        omega
      have hs' : 1 ≤ it'.start.val ∧ it'.start.val ≤ 10 := by first | omega | (rw [hst']; omega)
      refine ⟨by rw [hen]; exact he, hs'.1, hs'.2, ?_, ?_, ?_⟩
      · rw [hn', Nat.add_sub_cancel]; exact hq
      · rw [hn']
        intro k hk
        rw [ha, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
        split_ifs with h
        · rw [← h]; exact hq
        · exact hr k (by omega)
      · rw [hx, hex]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
  · refine ⟨he, hs1, hs, ?_, ?_⟩ <;> simp only [hx, Bool.false_eq_true, ↓reduceIte] <;> assumption

/-- `compact_block` holds the block's bytes. -/
theorem compact_block_q (input : Std.Array U8 16#usize) :
    word.compact_block input ⦃ r => compactQ r = blockQ input ⦄ := by
  apply WP.spec_mono (compact_block_spec input)
  intro r hr
  apply eq_of_byte_eq; intro m hm
  rw [compactQ, blockQ, byte_ofBytes _ hm, byte_ofBytes _ hm, hr m hm]

theorem blockQ_eq (a : Std.Array U8 16#usize) : blockQ a = leBytesToQuad32 (a.val.map (·.bv)) := by
  apply eq_of_byte_eq; intro m hm
  rw [blockQ, byte_ofBytes _ hm, byte_leBytesToQuad32 _ hm]
  simp [List.getElem!_eq_getElem?_getD]; rfl

/-- Block `q` of a key, as its words. -/
theorem blockQ_words {n : Usize} (input : Std.Array U8 n) (a : Std.Array U8 16#usize) (q : Nat)
    (hq : 16 * q + 16 ≤ n.val) (h : ∀ i < 16, a.val[i]! = input.val[16 * q + i]!) :
    blockQ a = mkfour (keyWords input)[4 * q]! (keyWords input)[4 * q + 1]! (keyWords input)[4 * q + 2]!
      (keyWords input)[4 * q + 3]! := by
  rw [blockQ_eq, keyWords]
  refine load_words _ _ q (by simp; omega) ?_
  intro i hi
  have hk : 16 * q + i < input.val.length := by simp; omega
  have hk' : i < a.val.length := by simp; omega
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk']
  have := h i hi
  rw [getElem!_pos a.val i hk', getElem!_pos input.val (16 * q + i) hk] at this
  simp [this]

/-- `setup_key_128` writes the AES-128 key `input`'s round keys. -/
theorem setup_key_128_spec (rd : Std.Array (Std.Array U32 4#usize) 15#usize) (input : Std.Array U8 16#usize) :
    setup_key_128 rd input ⦃ r => ∀ k ≤ 10, compactQ r.val[k]! = roundKey .AES_128 (keyWords input) k ⦄ := by
  have h0 : blockQ input = roundKey .AES_128 (keyWords input) 0 := by
    simp only [roundKey, keyWord_key .AES_128 _ (show 0 < 4 by decide),
      keyWord_key .AES_128 _ (show 1 < 4 by decide), keyWord_key .AES_128 _ (show 2 < 4 by decide),
      keyWord_key .AES_128 _ (show 3 < 4 by decide), Nat.mul_zero, Nat.zero_add, blockQ_eq, keyWords]
    exact load_eq_mkfour _ (by simp)
  unfold setup_key_128
  step with compact_block_q input as ⟨b, hb⟩
  step as ⟨a, ha⟩
  step as ⟨it, hs, he, hx⟩
  apply setup_key_128_loop_spec _ it a b (by simp [he]) (by simp [hs]) (by simp [hs]) hx (by simp [hs, hb, h0])
  intro k hk
  have : k = 0 := by simp [hs] at hk; omega
  subst this
  simp [ha, hb, h0]

/-- `setup_key_256`'s outer loop: from round keys `2 * (half - 1)` and the
one after, held in `block1` and `block2`, it writes the rest. -/
theorem setup_key_256_loop_spec (kw : List (BitVec 32)) (iter : core.ops.range.Range Usize)
    (rd : Std.Array (Std.Array U32 4#usize) 15#usize) (block1 block2 : Std.Array U32 4#usize)
    (he : iter.end.val = 8) (hs1 : 1 ≤ iter.start.val) (hs : iter.start.val ≤ 8)
    (hb1 : compactQ block1 = roundKey .AES_256 kw (2 * (iter.start.val - 1)))
    (hb2 : compactQ block2 = roundKey .AES_256 kw (2 * (iter.start.val - 1) + 1))
    (hr : ∀ k < 2 * iter.start.val, compactQ rd.val[k]! = roundKey .AES_256 kw k) :
    setup_key_256_loop0 iter rd block1 block2 ⦃ r => ∀ k ≤ 14, compactQ r.val[k]! = roundKey .AES_256 kw k ⦄ := by
  unfold setup_key_256_loop0
  apply loop.spec_decr_nat (fun x => 8 - x.1.start.val)
    (fun x => x.1.end.val = 8 ∧ 1 ≤ x.1.start.val ∧ x.1.start.val ≤ 8 ∧
      compactQ x.2.2.1 = roundKey .AES_256 kw (2 * (x.1.start.val - 1)) ∧
      compactQ x.2.2.2 = roundKey .AES_256 kw (2 * (x.1.start.val - 1) + 1) ∧
      ∀ k < 2 * x.1.start.val, compactQ x.2.1.val[k]! = roundKey .AES_256 kw k)
  · rintro ⟨it, rd, b1, b2⟩ ⟨he, hs1, hs, hb1, hb2, hr⟩
    simp only at he hs1 hs hb1 hb2 hr ⊢
    unfold setup_key_256_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step as ⟨i, hi⟩
      step with sub_block_spec b2 as ⟨sub, hsub⟩
      step with setup_key_256_inner_a_spec b1 it.start sub hs1 (by omega)
        { start := 0#usize, «end» := word.BLOCK_WORDS } b1 (by simp) (by simp [word.BLOCK_WORDS])
        (by intro j hj; simp) as ⟨c1, hc1⟩
      obtain ⟨n, hn⟩ : ∃ n, it.start.val = n + 1 := ⟨it.start.val - 1, by omega⟩
      have hq1 : compactQ c1 = roundKey .AES_256 kw (2 * it.start.val) := by
        rw [compactQ_of c1 _ hc1, rot_step _ _ _ _ _ _ _ _ (compactQ b2) _ (sbox_compactQ b2 sub hsub),
          ← compactQ_eq, hb1, hb2, rcon_eq (by omega), hn, Nat.add_sub_cancel,
          show 2 * (n + 1) = 2 * n + 2 by ring, roundKey256_even]
      step as ⟨x, back, hx, hback⟩
      split
      · rename_i h14
        have h14' : it.start.val = 7 := by
          have : i.val = 14 := by simp [h14]
          omega
        simp only [WP.spec_ok]
        intro k hk
        rw [hback, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega)]
        split_ifs with h
        · rw [← h, hi, hq1]
        · exact hr k (by omega)
      · rename_i h14
        have h14' : it.start.val ≠ 7 := by
          intro h; apply h14; apply UScalar.eq_of_val_eq; simp only [hi, h]; rfl
        step with sub_block_spec c1 as ⟨sub1, hsub1⟩
        step with setup_key_256_inner_b_spec b2 sub1
          { start := 0#usize, «end» := word.BLOCK_WORDS } b2 (by simp) (by simp [word.BLOCK_WORDS])
          (by intro j hj; simp) as ⟨c2, hc2⟩
        have hq2 : compactQ c2 = roundKey .AES_256 kw (2 * it.start.val + 1) := by
          rw [compactQ_of c2 _ hc2, sub_step _ _ _ _ _ _ _ _ (compactQ c1) (sbox_compactQ c1 sub1 hsub1),
            ← compactQ_eq, hb2, hq1, hn, Nat.add_sub_cancel, show 2 * (n + 1) + 1 = 2 * n + 3 by ring,
            show 2 * (n + 1) = 2 * n + 2 by ring, roundKey256_odd]
        step as ⟨i1, hi1⟩
        step as ⟨a, ha⟩
        have hen' : it'.end.val = it.end.val := by rw [hen]
        refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, by omega⟩
        · rw [hst', Nat.add_sub_cancel]; exact hq1
        · rw [hst', Nat.add_sub_cancel]; exact hq2
        · intro k hk
          rw [ha, hback, Std.Array.set_val_eq, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega),
            getElem!_set _ _ _ (by simp; omega)]
          split_ifs with h h'
          · rw [← h, hi1, hi, hq2]
          · rw [← h', hi, hq1]
          · exact hr k (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      intro k hk
      exact hr k (by omega)
  · exact ⟨he, hs1, hs, hb1, hb2, hr⟩

theorem lane32_mkfour0 (w0 w1 w2 w3 : BitVec 32) : lane32 (mkfour w0 w1 w2 w3) 0 = w0 := (lane32_mkfour _ _ _ _).1
theorem lane32_mkfour1 (w0 w1 w2 w3 : BitVec 32) : lane32 (mkfour w0 w1 w2 w3) 1 = w1 := (lane32_mkfour _ _ _ _).2.1
theorem lane32_mkfour2 (w0 w1 w2 w3 : BitVec 32) : lane32 (mkfour w0 w1 w2 w3) 2 = w2 := (lane32_mkfour _ _ _ _).2.2.1
theorem lane32_mkfour3 (w0 w1 w2 w3 : BitVec 32) : lane32 (mkfour w0 w1 w2 w3) 3 = w3 := (lane32_mkfour _ _ _ _).2.2.2

/-- `setup_key_192`'s loop: from words `12 * iter.start` to `12 * iter.start + 5`
of the schedule, held in `block1` and the first half of `block2`, it writes
the rest. -/
theorem setup_key_192_loop_spec (kw : List (BitVec 32)) (iter : core.ops.range.Range Usize)
    (rd : Std.Array (Std.Array U32 4#usize) 15#usize) (block1 block2 : Std.Array U32 4#usize)
    (he : iter.end.val = 4) (hs : iter.start.val ≤ 4)
    (hb1 : compactQ block1 = key192 kw (2 * iter.start.val))
    (hb2 : compactQ block2 = mkfour (keyWord .AES_192 kw (6 * (2 * iter.start.val) + 4))
      (keyWord .AES_192 kw (6 * (2 * iter.start.val) + 5)) 0 0)
    (hr : ∀ k < 3 * iter.start.val + 1, compactQ rd.val[k]! = roundKey .AES_192 kw k) :
    setup_key_192_loop0 iter rd block1 block2 ⦃ r => ∀ k ≤ 12, compactQ r.val[k]! = roundKey .AES_192 kw k ⦄ := by
  unfold setup_key_192_loop0
  apply loop.spec_decr_nat (fun x => 4 - x.1.start.val)
    (fun x => x.1.end.val = 4 ∧ x.1.start.val ≤ 4 ∧
      compactQ x.2.2.1 = key192 kw (2 * x.1.start.val) ∧
      compactQ x.2.2.2 = mkfour (keyWord .AES_192 kw (6 * (2 * x.1.start.val) + 4))
        (keyWord .AES_192 kw (6 * (2 * x.1.start.val) + 5)) 0 0 ∧
      ∀ k < 3 * x.1.start.val + 1, compactQ x.2.1.val[k]! = roundKey .AES_192 kw k)
  · rintro ⟨it, rd, B1, B2⟩ ⟨he, hs, hB1, hB2, hr⟩
    simp only at he hs hB1 hB2 hr ⊢
    unfold setup_key_192_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      set i := it.start.val with hi
      step with sub_block_spec B2 as ⟨sub, hsub⟩
      step with setup_key_192_inner_a_spec B1 B2 it.start sub (by omega)
        { start := 0#usize, «end» := word.BLOCK_WORDS } B1 B2 (by simp) (by simp [word.BLOCK_WORDS])
        (by intro j hj; simp) (by intro j hj; simp) as ⟨c1, c2, hc⟩
      have hz : ∀ m, 8 ≤ m → m < 16 → cByte B2.val[0]!.bv B2.val[1]!.bv B2.val[2]!.bv B2.val[3]!.bv m = 0 := by
        intro m h8 hm
        have := congrArg (byte · m) hB2
        simp only [compactQ, byte_ofBytes _ hm, byte_mkfour _ _ _ _ hm] at this
        rw [this, ite_eq_right (by omega), ite_eq_right (by omega)]
        split_ifs <;> simp [wbyte]
      have hA := step192_a B1.val[0]!.bv B1.val[1]!.bv B1.val[2]!.bv B1.val[3]!.bv B2.val[0]!.bv B2.val[1]!.bv
        B2.val[2]!.bv B2.val[3]!.bv sub.val[0]!.bv sub.val[1]!.bv sub.val[2]!.bv sub.val[3]!.bv (compactQ B2)
        (RCON.val[2 * i]!).bv (sbox_compactQ B2 sub hsub) hz
      simp only [← compactQ_eq] at hA
      have hN : nextKey (compactQ B1) (subWord (rotWord (lane32 (compactQ B2) 1)) ^^^
          (RCON.val[2 * i]!).bv.setWidth 32) = key192 kw (2 * i + 1) := by
        rw [hB1, hB2, (lane32_mkfour _ _ _ _).2.1, rcon_eq (by omega), key192_succ]
      rw [hN, hB2] at hA
      obtain ⟨hA2, hA1⟩ := hA
      have l0 := (lane32_mkfour (keyWord .AES_192 kw (6 * (2 * i) + 4)) (keyWord .AES_192 kw (6 * (2 * i) + 5)) 0 0).1
      have l1 := (lane32_mkfour (keyWord .AES_192 kw (6 * (2 * i) + 4)) (keyWord .AES_192 kw (6 * (2 * i) + 5)) 0 0).2.1
      have k3 : lane32 (key192 kw (2 * i + 1)) 3 = keyWord .AES_192 kw (6 * (2 * i) + 9) := by
        rw [key192, (lane32_mkfour _ _ _ _).2.2.2, show 6 * (2 * i + 1) + 3 = 6 * (2 * i) + 9 by ring]
      have hq2 : compactQ c2 = roundKey .AES_192 kw (3 * i + 1) := by
        rw [compactQ_of c2 _ (fun j hj => (hc j hj).2), hA2, l0, l1, roundKey192_odd1]
      have hq1 : compactQ c1 = roundKey .AES_192 kw (3 * i + 2) := by
        rw [compactQ_of c1 _ (fun j hj => (hc j hj).1), hA1, l0, l1, roundKey192_odd2, k3,
          show 6 * (2 * i + 1) + 4 = 6 * (2 * i) + 10 by ring, show 6 * (2 * i + 1) + 5 = 6 * (2 * i) + 11 by ring,
          keyWord192_5, keyWord192_4]
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step as ⟨rd1, hrd1⟩
      step as ⟨i3, hi3⟩
      step as ⟨rd2, hrd2⟩
      step with sub_block_spec c1 as ⟨sub1, hsub1⟩
      step with setup_key_192_inner_b_spec c1 c2 it.start sub1 (by omega)
        { start := 0#usize, «end» := word.BLOCK_WORDS } c1 c2 (by simp) (by simp [word.BLOCK_WORDS])
        (by intro j hj; simp) (by intro j hj; simp) as ⟨d1, d2, hd⟩
      have hB := step192_b c1.val[0]!.bv c1.val[1]!.bv c1.val[2]!.bv c1.val[3]!.bv c2.val[0]!.bv c2.val[1]!.bv
        c2.val[2]!.bv c2.val[3]!.bv sub1.val[0]!.bv sub1.val[1]!.bv sub1.val[2]!.bv sub1.val[3]!.bv (compactQ c1)
        (RCON.val[2 * i + 1]!).bv (sbox_compactQ c1 sub1 hsub1)
      simp only [← hi] at hd
      simp only [← compactQ_eq] at hB
      rw [← compactQ_of d2 _ (fun j hj => (hd j hj).2), ← compactQ_of d1 _ (fun j hj => (hd j hj).1)] at hB
      obtain ⟨hB2, hB1⟩ := hB
      have hq3 : compactQ d2 = key192 kw (2 * (i + 1)) := by
        rw [hB2, hq2, hq1, roundKey192_odd1, roundKey192_odd2, show 2 * (i + 1) = 2 * i + 1 + 1 by ring,
          rcon_eq (by omega)]
        conv_rhs => rw [key192_succ]
        simp only [key192, lane32_mkfour0, lane32_mkfour1, lane32_mkfour2, lane32_mkfour3]
      have hq4 : compactQ d1 = mkfour (keyWord .AES_192 kw (6 * (2 * (i + 1)) + 4))
          (keyWord .AES_192 kw (6 * (2 * (i + 1)) + 5)) 0 0 := by
        rw [hB1, hq1, hq3, roundKey192_odd2]
        simp only [key192, lane32_mkfour2, lane32_mkfour3]
        rw [show 6 * (2 * (i + 1)) + 4 = 6 * (2 * i + 1) + 10 by ring,
          show 6 * (2 * (i + 1)) + 5 = 6 * (2 * i + 1) + 11 by ring,
          show 6 * (2 * (i + 1)) + 3 = 6 * (2 * i + 1) + 9 by ring, keyWord192_5, keyWord192_4]
      step as ⟨i4, hi4⟩
      step as ⟨i5, hi5⟩
      step as ⟨a, ha⟩
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, ?_, ?_, ?_, by omega⟩
      · rw [hst']; exact hq3
      · rw [hst']; exact hq4
      · intro k hk
        rw [ha, hrd2, hrd1, Std.Array.set_val_eq, Std.Array.set_val_eq, Std.Array.set_val_eq,
          getElem!_set _ _ _ (by simp; omega), getElem!_set _ _ _ (by simp; omega), getElem!_set _ _ _ (by simp; omega)]
        split_ifs with h h' h''
        · rw [← h, hi5, hi4, ← hi, hq3, show 3 * i + 3 = 3 * i + 3 from rfl, roundKey192_even,
            show 2 * (i + 1) = 2 * i + 2 by ring]
        · rw [← h', hi3, hi1, ← hi]; exact hq1
        · rw [← h'', hi2, hi1, ← hi]; exact hq2
        · exact hr k (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      intro k hk
      exact hr k (by omega)
  · exact ⟨he, hs, hb1, hb2, hr⟩

/-- `setup_key_192` writes the AES-192 key `input`'s round keys. -/
theorem setup_key_192_spec (rd : Std.Array (Std.Array U32 4#usize) 15#usize) (input : Std.Array U8 24#usize) :
    setup_key_192 rd input ⦃ r => ∀ k ≤ 12, compactQ r.val[k]! = roundKey .AES_192 (keyWords input) k ⦄ := by
  set kw := keyWords input
  unfold setup_key_192
  step*
  have hsl : lo.len = 16#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, hsl, ↓reduceDIte, core.result.Result.unwrap, bind_ok]
  step with compact_block_q as ⟨b1, hb1⟩
  step as ⟨a1, ha1⟩
  step*
  step with compact_block_q as ⟨b2, hb2⟩
  have hl : (input.val.map (·.bv)).length = 24 := by simp
  have h0 : compactQ b1 = key192 kw 0 := by
    rw [hb1, blockQ_words input _ 0 (by simp) ?_]
    · simp only [key192, keyWord_key .AES_192 kw (show 0 < 6 by decide),
        keyWord_key .AES_192 kw (show 1 < 6 by decide), keyWord_key .AES_192 kw (show 2 < 6 by decide),
        keyWord_key .AES_192 kw (show 3 < 6 by decide), kw]
    · intro i h16
      simp [lo_post2, s_post, Array.to_slice, h16, List.getElem!_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by simp; omega)]; rfl
  have h2 : compactQ b2 = mkfour (keyWord .AES_192 kw (6 * (2 * 0) + 4)) (keyWord .AES_192 kw (6 * (2 * 0) + 5)) 0 0 := by
    rw [hb2, keyWord_key .AES_192 kw (show 6 * (2 * 0) + 4 < 6 by decide),
      keyWord_key .AES_192 kw (show 6 * (2 * 0) + 5 < 6 by decide)]
    apply eq_of_byte_eq; intro m hm
    rw [blockQ, byte_ofBytes _ hm, byte_mkfour _ _ _ _ hm, s1_post2, s2_post]
    have hhl : hi.val.length = 8 := by simp [lo_post3, s_post, Array.to_slice]
    by_cases h8 : m < 8
    · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by omega, by simp; omega⟩]
      have hb : m % 4 < 4 := Nat.mod_lt _ (by decide)
      rw [show (if m < 4 then (kw[6 * (2 * 0) + 4]!) else if m < 8 then kw[6 * (2 * 0) + 5]! else if m < 12 then 0 else 0)
          = kw[4 + m / 4]! by split_ifs <;> first | omega | (congr 1; omega)]
      rw [show kw = seqNat8ToSeqNat32LE (input.val.map (·.bv)) from rfl,
        wbyte_seqNat8ToSeqNat32LE _ (by rw [hl]; omega) hb, lo_post3, s_post]
      simp [Array.to_slice, List.getElem!_eq_getElem?_getD]
      rw [show 4 * (4 + m / 4) + m % 4 = 16 + m by omega]
      rfl
    · rw [List.getElem!_setSlice!_suffix _ _ _ _ (by omega)]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp [Std.Array.repeat_val, hm, wbyte]
      interval_cases m <;> rfl
  apply setup_key_192_loop_spec kw _ a1 b1 b2 (by simp) (by simp) (by simpa using h0) (by simpa using h2)
  intro k hk
  have : k = 0 := by simpa using hk
  subst this
  rw [ha1, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp), ite_eq_left (show (0#usize).val = 0 from rfl), h0,
    roundKey192_zero]

/-- `setup_key_256` writes the AES-256 key `input`'s round keys. -/
theorem setup_key_256_spec (rd : Std.Array (Std.Array U32 4#usize) 15#usize) (input : Std.Array U8 32#usize) :
    setup_key_256 rd input ⦃ r => ∀ k ≤ 14, compactQ r.val[k]! = roundKey .AES_256 (keyWords input) k ⦄ := by
  set l := input.val.map (·.bv)
  set kw := keyWords input
  have hl : l.length = 32 := by simp [l]
  unfold setup_key_256
  step*
  have hsl : lo.len = 16#usize := by scalar_tac
  have hsl1 : hi.len = 16#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, hsl, hsl1, ↓reduceDIte, core.result.Result.unwrap,
    bind_ok]
  step with compact_block_q as ⟨b1, hb1⟩
  step as ⟨a1, ha1⟩
  step with compact_block_q as ⟨b2, hb2⟩
  step as ⟨a2, ha2⟩
  have h0 : compactQ b1 = roundKey .AES_256 kw 0 := by
    rw [hb1, blockQ_words input _ 0 (by simp) ?_]
    · simp only [roundKey, keyWord_key .AES_256 kw (show 0 < 8 by decide),
        keyWord_key .AES_256 kw (show 1 < 8 by decide), keyWord_key .AES_256 kw (show 2 < 8 by decide),
        keyWord_key .AES_256 kw (show 3 < 8 by decide), kw]
    · intro i h16
      simp [lo_post2, s_post, Array.to_slice, h16, List.getElem!_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by simp; omega)]; rfl
  have h1 : compactQ b2 = roundKey .AES_256 kw 1 := by
    rw [hb2, blockQ_words input _ 1 (by simp) ?_]
    · simp only [roundKey, keyWord_key .AES_256 kw (show 4 < 8 by decide),
        keyWord_key .AES_256 kw (show 5 < 8 by decide), keyWord_key .AES_256 kw (show 6 < 8 by decide),
        keyWord_key .AES_256 kw (show 7 < 8 by decide), kw]
    · intro i h16
      simp [lo_post3, s_post, Array.to_slice, List.getElem!_eq_getElem?_getD]
  apply setup_key_256_loop_spec kw _ a2 b1 b2 (by simp) (by simp) (by simp) (by simpa using h0)
    (by simpa using h1)
  intro k hk
  have : k < 2 := by simpa using hk
  rw [ha2, ha1, Std.Array.set_val_eq, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp),
    getElem!_set _ _ _ (by simp)]
  split_ifs with h h'
  · rw [← h]; exact h1
  · rw [← h']; exact h0
  · simp at h h'; omega

/-! ## The bitsliced round keys -/

/-- `schedule`'s inner loop: copies `iter.start` on of round key `r` into its batch. -/
theorem schedule_inner_spec (a : Std.Array (Std.Array U32 4#usize) 15#usize) (r : Usize) (hr : r.val < 15)
    (keys0 : Std.Array Batch 15#usize) (iter : core.ops.range.Range Usize) (keys : Std.Array Batch 15#usize)
    (hs : iter.start.val ≤ 2) (he : iter.end.val = 2)
    (hk : ∀ q < 15, q ≠ r.val → keys.val[q]! = keys0.val[q]!)
    (hb : ∀ j < 8, (keys.val[r.val]!).w.val[j]! =
      if j % 2 < iter.start.val then (a.val[r.val]!).val[j / 2]! else (keys0.val[r.val]!).w.val[j]!) :
    NohwKey.schedule_loop0_loop0 iter a keys r ⦃ ks =>
      (∀ q < 15, q ≠ r.val → ks.val[q]! = keys0.val[q]!) ∧
      ∀ j < 8, (ks.val[r.val]!).w.val[j]! = (a.val[r.val]!).val[j / 2]! ⦄ := by
  unfold NohwKey.schedule_loop0_loop0
  apply loop.spec_decr_nat (fun x => 2 - x.1.start.val)
    (fun x => x.1.start.val ≤ 2 ∧ x.1.end.val = 2 ∧ (∀ q < 15, q ≠ r.val → x.2.val[q]! = keys0.val[q]!) ∧
      ∀ j < 8, (x.2.val[r.val]!).w.val[j]! =
        if j % 2 < x.1.start.val then (a.val[r.val]!).val[j / 2]! else (keys0.val[r.val]!).w.val[j]!)
  · rintro ⟨it, st⟩ ⟨hs, he, hk, hb⟩
    simp only at hs he hk hb ⊢
    unfold NohwKey.schedule_loop0_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step as ⟨b, back, hbv, hback⟩
      step as ⟨a1, ha1⟩
      step with set_spec b a1 it.start (by omega) as ⟨b1, hb1⟩
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, ?_, ?_, by omega⟩
      · intro q hq hqr
        rw [hback, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega), ite_eq_right (by omega)]
        exact hk q hq hqr
      · intro j hj
        rw [hback, Std.Array.set_val_eq, getElem!_set _ _ _ (by simp; omega), ite_eq_left rfl, hb1 j hj]
        have hb' := hb j hj
        rw [hbv, ← getElem!_pos] at *
        split_ifs with h1 h2 h2
        · rw [ha1]
        · omega
        · rw [hb', ite_eq_left (by omega)]
        · rw [hb', ite_eq_right (by omega)]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      refine ⟨hk, ?_⟩
      intro j hj
      rw [hb j hj, ite_eq_left (by omega)]
  · exact ⟨hs, he, hk, hb⟩

/-- `schedule`'s outer loop: bitslices round keys `iter.start` to `n - 1`. -/
theorem schedule_loop_spec (a : Std.Array (Std.Array U32 4#usize) 15#usize) (n : Nat) (hn : n ≤ 15)
    (iter : core.ops.range.Range Usize) (keys : Std.Array Batch 15#usize)
    (hs : iter.start.val ≤ n) (he : iter.end.val = n)
    (hk : ∀ q < iter.start.val, ∀ i < 2, (keys.val[q]!).block i = compactQ a.val[q]!) :
    NohwKey.schedule_loop0 iter a keys ⦃ ks => ∀ q < n, ∀ i < 2, (ks.val[q]!).block i = compactQ a.val[q]! ⦄ := by
  unfold NohwKey.schedule_loop0
  apply loop.spec_decr_nat (fun x => n - x.1.start.val)
    (fun x => x.1.start.val ≤ n ∧ x.1.end.val = n ∧
      ∀ q < x.1.start.val, ∀ i < 2, (x.2.val[q]!).block i = compactQ a.val[q]!)
  · rintro ⟨it, st⟩ ⟨hs, he, hk⟩
    simp only at hs he hk ⊢
    unfold NohwKey.schedule_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst', hen⟩
      subst ho
      step with schedule_inner_spec a it.start (by omega) st { start := 0#usize, «end» := word.BATCH_SIZE } st
        (by simp) (by simp [word.BATCH_SIZE]) (by intro q _ _; rfl) (by intro j hj; simp) as ⟨k1, hk1, hk1'⟩
      step as ⟨b, back, hbv, hback⟩
      step with transpose_block b as ⟨b1, hb1⟩
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro q hq i hi
      simp only [hback, Std.Array.set_val_eq]
      rw [getElem!_set _ _ _ (by simp; omega)]
      split_ifs with h
      · subst h
        apply eq_of_byte_eq; intro m hm
        rw [byte_block _ _ hm, (hb1 i hi m hm).1, compactQ, byte_ofBytes _ hm, Batch.cblock]
        have hw : ∀ k < 8, b.bv k = (a.val[it.start.val]!).val[k / 2]!.bv := by
          intro k hk; rw [Batch.bv, hbv, ← getElem!_pos, hk1' k hk]
        rw [hw _ (by omega), hw _ (by omega), hw _ (by omega), hw _ (by omega)]
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> rfl
      · rw [hk1 q (by omega) (Ne.symm h)]
        exact hk q (by omega) i hi
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho, hit⟩
      subst ho
      simp only [WP.spec_ok]
      intro q hq
      exact hk q (by omega)
  · exact ⟨hs, he, hk⟩

/-- `schedule` bitslices the round keys, two copies of each. -/
theorem schedule_spec (k : NohwKey) (hr : k.rounds.val ≤ 14) :
    k.schedule ⦃ s => s.rounds = k.rounds ∧
      ∀ q ≤ k.rounds.val, ∀ i < 2, (s.keys.val[q]!).block i = compactQ k.rd_key.val[q]! ⦄ := by
  unfold NohwKey.schedule
  step as ⟨n, hn⟩
  step with schedule_loop_spec k.rd_key (k.rounds.val + 1) (by omega) { start := 0#usize, «end» := n } _
    (by simp) (by simp [hn]) (by intro q hq; simp at hq) as ⟨ks, hks⟩
  exact fun q hq => hks q (by omega)

/-- `NohwKey::new` expands a key of a length AES takes into its round keys. -/
theorem new_spec (alg : Algorithm) (key : Slice U8) (h : KeyLen alg key.length) :
    NohwKey.new key ⦃ k => k.rounds.val = nr alg ∧
      ∀ q ≤ nr alg, compactQ k.rd_key.val[q]! = roundKey alg (seqNat8ToSeqNat32LE (key.val.map (·.bv))) q ⦄ := by
  unfold NohwKey.new
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  all_goals
    have hl : key.len.val = key.length := by simp
    simp only [hl, h, core.array.TryFromSharedArraySlice.try_from, core.result.Result.unwrap]
  · have hl' : key.len = 16#usize := by scalar_tac
    simp only [hl', ↓reduceDIte, bind_ok]
    step with setup_key_128_spec as ⟨r, hr⟩
    refine ⟨by simp [nr], fun q hq => ?_⟩
    simpa [keyWords] using hr q (by simpa [nr] using hq)
  · have hl' : key.len = 24#usize := by scalar_tac
    simp only [hl', ↓reduceDIte, bind_ok]
    step with setup_key_192_spec as ⟨r, hr⟩
    refine ⟨by simp [nr], fun q hq => ?_⟩
    simpa [keyWords] using hr q (by simpa [nr] using hq)
  · have hl' : key.len = 32#usize := by scalar_tac
    simp only [hl', ↓reduceDIte, bind_ok]
    step with setup_key_256_spec as ⟨r, hr⟩
    refine ⟨by simp [nr], fun q hq => ?_⟩
    simpa [keyWords] using hr q (by simpa [nr] using hq)

/-! ## The cipher on the key -/

theorem evalRounds_congr (init : Quad32) {rk rk' : List Quad32} (n : Nat) (h : ∀ r ≤ n, rk[r]! = rk'[r]!) :
    evalRounds init rk n = evalRounds init rk' n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [evalRounds, evalRounds, ih (fun r hr => h r (by omega)), h (n + 1) le_rfl]

theorem cipherRounds_congr (n : Nat) (input : Quad32) {rk rk' : List Quad32} (h : ∀ r ≤ n, rk[r]! = rk'[r]!) :
    cipherRounds n input rk = cipherRounds n input rk' := by
  rw [cipherRounds, cipherRounds, h 0 (by omega), h n le_rfl, evalRounds_congr _ _ (fun r hr => h r (by omega))]

/-- A schedule holding key `kw`'s round keys encrypts a block as FIPS 197's
cipher does under `kw`. -/
theorem schedule_encrypt_block (alg : Algorithm) (kw : List (BitVec 32)) (s : Schedule)
    (hr : s.rounds.val = nr alg) (hs : ∀ q ≤ nr alg, (s.keys.val[q]!).block 0 = roundKey alg kw q)
    (block : Std.Array U8 16#usize) :
    s.encrypt_block block ⦃ r => blockQ r = aesEncrypt alg kw (blockQ block) ⦄ := by
  have hn : 1 ≤ nr alg ∧ nr alg ≤ 14 := by cases alg <;> decide
  apply WP.spec_mono (encrypt_block_spec s block (by omega) (by omega))
  intro r h
  rw [h, aesEncrypt, evalCipher_eq, hr]
  apply cipherRounds_congr
  intro q hq
  rw [roundKeys_get s 0 q (by omega), hs q hq, keyToRoundKeys_eq, getElem!_range_map _ (by omega)]

/-- The schedule of a key of a length AES takes holds its round keys. -/
theorem new_schedule_spec (alg : Algorithm) (key : Slice U8) (h : KeyLen alg key.length) :
    (do let k ← NohwKey.new key; k.schedule) ⦃ s => s.rounds.val = nr alg ∧
      ∀ q ≤ nr alg, ∀ i < 2,
        (s.keys.val[q]!).block i = roundKey alg (seqNat8ToSeqNat32LE (key.val.map (·.bv))) q ⦄ := by
  have hn : nr alg ≤ 14 := by cases alg <;> decide
  step with new_spec alg key h as ⟨k, hk, hkq⟩
  step with schedule_spec k (by omega) as ⟨s, hs, hsq⟩
  refine ⟨by rw [hs, hk], fun q hq i hi => ?_⟩
  rw [hsq q (by omega) i hi, hkq q hq]

end rind.armv7
