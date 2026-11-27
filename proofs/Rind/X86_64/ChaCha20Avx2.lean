import Rind.X86_64.VgChaCha20
import Rind.X86_64.AesGcmBy8
open Aeneas Aeneas.Std Result rind.spec rind.simd rind.vale rind.x86_64

/-!
# The two-block AVX2 kernel, proven to RFC 8439

`low::x86_64::chacha20::cipher_avx2` XORs ChaCha20's keystream into a buffer
128 bytes at a time with `core_2x`, which holds two consecutive blocks' states
in four 256-bit vectors, a row of the state each, the first block's in the
low 128-bit halves. `kernel` proves `Rind.X86_64.VgChaCha20`'s `Kernel`, the
kernel's contract, over `Rind.X86_64.Simd`'s models of the AVX2 intrinsics.
-/

namespace rind.x86_64.avx2

/-! ## Vectors as eight 32-bit lanes -/

local notation "V" => ofLanes32x8

theorem getLsbD_V (f : Nat → BitVec 32) (k : Nat) :
    (V f).getLsbD k = (decide (k < 256) && (f (k / 32)).getLsbD (k % 32)) := by
  by_cases hk : k < 256
  · simp only [ofLanes32x8, BitVec.getLsbD_append]
    interval_cases k <;> simp
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp [hk]

theorem getLsbD_ofHalves (g : Nat → BitVec 128) (k : Nat) :
    (ofHalves g).getLsbD k = (decide (k < 256) && (g (k / 128)).getLsbD (k % 128)) := by
  by_cases hk : k < 256
  · simp only [ofHalves, BitVec.getLsbD_append]
    by_cases h0 : k < 128
    · simp [h0, hk, Nat.div_eq_of_lt h0, Nat.mod_eq_of_lt h0]
    · simp [h0, hk, show k / 128 = 1 by omega, show k % 128 = k - 128 by omega]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp [hk]

theorem getLsbD_half (x : BitVec 256) (j m : Nat) :
    (half x j).getLsbD m = (decide (m < 128) && x.getLsbD (128 * j + m)) := by
  simp [half, BitVec.getLsbD_extractLsb']

theorem lane_V (f : Nat → BitVec 32) (i : Nat) (h : i < 8) : lane32x8 (V f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [lane32x8, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, getLsbD_V]
  simp [show 32 * i + k < 256 by omega, show (32 * i + k) / 32 = i by omega,
    show (32 * i + k) % 32 = k by omega]

theorem V_lane (x : BitVec 256) : V (lane32x8 x) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [getLsbD_V, hk, decide_true, Bool.true_and, lane32x8, BitVec.getLsbD_extractLsb']
  simp [show k % 32 < 32 by omega, show 32 * (k / 32) + k % 32 = k by omega]

theorem V_congr {f g : Nat → BitVec 32} (h : ∀ i < 8, f i = g i) : V f = V g := by
  simp only [ofLanes32x8, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

theorem add_V (f g : Nat → BitVec 32) :
    core.core_arch.x86.avx2._mm256_add_epi32 (V f) (V g) = ok (V fun i => f i + g i) := by
  simp only [core.core_arch.x86.avx2._mm256_add_epi32, ok.injEq]
  exact V_congr fun i hi => by rw [lane_V _ _ hi, lane_V _ _ hi]

theorem xor_V (f g : Nat → BitVec 32) :
    core.core_arch.x86.avx2._mm256_xor_si256 (V f) (V g) = ok (V fun i => f i ^^^ g i) := by
  simp only [core.core_arch.x86.avx2._mm256_xor_si256, ok.injEq]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_xor, getLsbD_V, hk, decide_true, Bool.true_and]

theorem or_V (f g : Nat → BitVec 32) :
    core.core_arch.x86.avx2._mm256_or_si256 (V f) (V g) = ok (V fun i => f i ||| g i) := by
  simp only [core.core_arch.x86.avx2._mm256_or_si256, ok.injEq]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_or, getLsbD_V, hk, decide_true, Bool.true_and]

theorem slli12_V (f : Nat → BitVec 32) :
    core.core_arch.x86.avx2._mm256_slli_epi32 12#i32 (V f) = ok (V fun i => f i <<< 12) := by
  simp only [core.core_arch.x86.avx2._mm256_slli_epi32, ok.injEq]
  exact V_congr fun i hi => by simp [lane_V _ _ hi]

theorem srli20_V (f : Nat → BitVec 32) :
    core.core_arch.x86.avx2._mm256_srli_epi32 20#i32 (V f) = ok (V fun i => f i >>> 20) := by
  simp only [core.core_arch.x86.avx2._mm256_srli_epi32, ok.injEq]
  exact V_congr fun i hi => by simp [lane_V _ _ hi]

theorem slli7_V (f : Nat → BitVec 32) :
    core.core_arch.x86.avx2._mm256_slli_epi32 7#i32 (V f) = ok (V fun i => f i <<< 7) := by
  simp only [core.core_arch.x86.avx2._mm256_slli_epi32, ok.injEq]
  exact V_congr fun i hi => by simp [lane_V _ _ hi]

theorem srli25_V (f : Nat → BitVec 32) :
    core.core_arch.x86.avx2._mm256_srli_epi32 25#i32 (V f) = ok (V fun i => f i >>> 25) := by
  simp only [core.core_arch.x86.avx2._mm256_srli_epi32, ok.injEq]
  exact V_congr fun i hi => by simp [lane_V _ _ hi]

theorem rotl12 (x : BitVec 32) : x <<< 12 ||| x >>> 20 = x.rotateLeft 12 := rotl x 12 (by decide)
theorem rotl7 (x : BitVec 32) : x <<< 7 ||| x >>> 25 = x.rotateLeft 7 := rotl x 7 (by decide)

/-- Lane `i` of `PSHUFD` in each half, by `k` lanes. -/
def rotLane (k i : Nat) : Nat := 4 * (i / 4) + (i % 4 + k) % 4

theorem shuffle_V (imm : Std.I32) (m : Nat) (hm : imm.bv.toNat = m) (f : Nat → BitVec 32) :
    core.core_arch.x86.avx2._mm256_shuffle_epi32 imm (V f) =
      ok (V fun i => f (4 * (i / 4) + m / 4 ^ (i % 4) % 4)) := by
  simp only [core.core_arch.x86.avx2._mm256_shuffle_epi32, ok.injEq, hm]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [getLsbD_ofHalves, getLsbD_V, hk, decide_true, Bool.true_and, getLsbD_ofLanes32,
    getLsbD_lane32, getLsbD_half, show k % 128 < 128 by omega, Nat.mod_lt _ (by omega : 32 > 0)]
  rw [show k % 128 / 32 = k / 32 % 4 by omega]
  generalize hs : m / 4 ^ (k / 32 % 4) % 4 = s
  have h4 : s < 4 := hs ▸ Nat.mod_lt _ (by omega)
  rw [show (128 * (k / 128) + (32 * s + k % 128 % 32)) / 32 = 4 * (k / 32 / 4) + s by omega,
    show (128 * (k / 128) + (32 * s + k % 128 % 32)) % 32 = k % 32 by omega]
  simp [show 32 * s + k % 32 < 128 by omega, show 128 * (k / 128) + (32 * s + k % 32) < 256 by omega]

theorem shuffle57_V (f : Nat → BitVec 32) :
    core.core_arch.x86.avx2._mm256_shuffle_epi32 57#i32 (V f) = ok (V fun i => f (rotLane 1 i)) := by
  rw [shuffle_V _ 57 rfl]
  exact congrArg ok (V_congr fun i hi => by interval_cases i <;> rfl)

theorem shuffle78_V (f : Nat → BitVec 32) :
    core.core_arch.x86.avx2._mm256_shuffle_epi32 78#i32 (V f) = ok (V fun i => f (rotLane 2 i)) := by
  rw [shuffle_V _ 78 rfl]
  exact congrArg ok (V_congr fun i hi => by interval_cases i <;> rfl)

theorem shuffle147_V (f : Nat → BitVec 32) :
    core.core_arch.x86.avx2._mm256_shuffle_epi32 147#i32 (V f) = ok (V fun i => f (rotLane 3 i)) := by
  rw [shuffle_V _ 147 rfl]
  exact congrArg ok (V_congr fun i hi => by interval_cases i <;> rfl)

/-- The rotate-by-16 mask. -/
theorem m16_eq : core.core_arch.x86.avx._mm256_set_epi8 13#i8 12#i8 15#i8 14#i8 9#i8 8#i8
        11#i8 10#i8 5#i8 4#i8 7#i8 6#i8 1#i8 0#i8 3#i8 2#i8 13#i8 12#i8 15#i8
        14#i8 9#i8 8#i8 11#i8 10#i8 5#i8 4#i8 7#i8 6#i8 1#i8 0#i8 3#i8 2#i8 =
    ok 0x0d0c0f0e09080b0a0504070601000302_0d0c0f0e09080b0a0504070601000302#256 := by
  rfl

/-- The rotate-by-8 mask. -/
theorem m8_eq : core.core_arch.x86.avx._mm256_set_epi8 14#i8 13#i8 12#i8 15#i8 10#i8 9#i8
        8#i8 11#i8 6#i8 5#i8 4#i8 7#i8 2#i8 1#i8 0#i8 3#i8 14#i8 13#i8 12#i8
        15#i8 10#i8 9#i8 8#i8 11#i8 6#i8 5#i8 4#i8 7#i8 2#i8 1#i8 0#i8 3#i8 =
    ok 0x0e0d0c0f0a09080b0605040702010003_0e0d0c0f0a09080b0605040702010003#256 := by
  rfl

/-- `VPSHUFB` by a mask that moves each 32-bit lane's bytes within it. -/
theorem shuffle_bits (f : Nat → BitVec 32) (m : BitVec 256) (k : Nat) (hk : k < 256) :
    (ofHalves fun j => ofBytes fun i =>
      if (byte (half m j) i).msb then 0 else byte (half (V f) j) ((byte (half m j) i).toNat % 16)).getLsbD k =
      if (byte (half m (k / 128)) (k % 128 / 8)).msb then false else
        (f ((128 * (k / 128) + 8 * ((byte (half m (k / 128)) (k % 128 / 8)).toNat % 16) + k % 8) / 32)).getLsbD
          ((128 * (k / 128) + 8 * ((byte (half m (k / 128)) (k % 128 / 8)).toNat % 16) + k % 8) % 32) := by
  rw [getLsbD_ofHalves]
  simp only [hk, decide_true, Bool.true_and]
  rw [getLsbD_ofBytes _ (Nat.mod_lt _ (by omega))]
  split
  · simp
  · rw [getLsbD_byte _ _ (by omega), getLsbD_half, getLsbD_V]
    generalize (byte (half m (k / 128)) (k % 128 / 8)).toNat = t
    have h16 : t % 16 < 16 := Nat.mod_lt _ (by omega)
    rw [show k % 128 % 8 = k % 8 by omega]
    simp [show 8 * (t % 16) + k % 8 < 128 by omega, show 128 * (k / 128) + (8 * (t % 16) + k % 8) < 256 by omega,
      Nat.add_assoc]

theorem rot16_V (f : Nat → BitVec 32) :
    core.core_arch.x86.avx2._mm256_shuffle_epi8 (V f)
      0x0d0c0f0e09080b0a0504070601000302_0d0c0f0e09080b0a0504070601000302#256 =
    ok (V fun i => (f i).rotateLeft 16) := by
  simp only [core.core_arch.x86.avx2._mm256_shuffle_epi8, ok.injEq]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [shuffle_bits _ _ _ hk, getLsbD_V]
  simp only [hk, decide_true, Bool.true_and, BitVec.getLsbD_rotateLeft]
  interval_cases k <;> simp +decide [byte, half]

theorem rot8_V (f : Nat → BitVec 32) :
    core.core_arch.x86.avx2._mm256_shuffle_epi8 (V f)
      0x0e0d0c0f0a09080b0605040702010003_0e0d0c0f0a09080b0605040702010003#256 =
    ok (V fun i => (f i).rotateLeft 8) := by
  simp only [core.core_arch.x86.avx2._mm256_shuffle_epi8, ok.injEq]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [shuffle_bits _ _ _ hk, getLsbD_V]
  simp only [hk, decide_true, Bool.true_and, BitVec.getLsbD_rotateLeft]
  interval_cases k <;> simp +decide [byte, half]

/-! ## The double round -/

/-- The state of the block in half `h` of the four row vectors. -/
def rows (a b c d : BitVec 256) (h : Nat) : List (BitVec 32) :=
  [a, b, c, d].flatMap fun r => (List.range 4).map fun i => lane32x8 r (4 * h + i)

theorem body_V (it : core.ops.range.Range Usize) (hlt : it.start.val < it.end.val)
    (fa fb fc fd : Nat → BitVec 32) :
    low.x86_64.chacha20.core_2x_loop0.body it (V fa) (V fb) (V fc) (V fd) ⦃ r =>
      ∃ it' a b c d, r = .cont (it', a, b, c, d) ∧ it'.start.val = it.start.val + 1 ∧
        it'.end = it.end ∧
        ∀ h < 2, rows a b c d h = chacha20.innerBlock (rows (V fa) (V fb) (V fc) (V fd) h) ⦄ := by
  unfold low.x86_64.chacha20.core_2x_loop0.body
  step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho, hst, hen⟩
  subst ho
  simp only [add_V, xor_V, m16_eq, m8_eq, rot16_V, rot8_V, slli12_V, srli20_V, slli7_V, srli25_V,
    or_V, shuffle57_V, shuffle78_V, shuffle147_V, bind_ok, WP.spec_ok]
  refine ⟨_, _, _, _, _, rfl, hst, hen, ?_⟩
  intro h hh
  interval_cases h <;>
  · simp only [rows, List.flatMap_cons, List.flatMap_nil,
      show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.append_nil]
    simp (disch := omega) only [lane_V, Nat.reduceMul, Nat.reduceAdd]
    simp [chacha20.innerBlock, chacha20.quarterRound, chacha20.qr, rotLane, rotl12, rotl7]

/-- Ten double rounds, on both blocks' states at once. -/
@[step]
theorem loop0_spec (it : core.ops.range.Range Usize) (hle : it.start.val ≤ it.end.val)
    (a b c d : BitVec 256) :
    low.x86_64.chacha20.core_2x_loop0 it a b c d ⦃ r =>
      ∀ h < 2, rows r.1 r.2.1 r.2.2.1 r.2.2.2 h =
        chacha20.innerBlock^[it.end.val - it.start.val] (rows a b c d h) ⦄ := by
  unfold low.x86_64.chacha20.core_2x_loop0
  apply loop.spec_decr_nat (fun x => x.1.end.val - x.1.start.val)
    (fun x => it.start.val ≤ x.1.start.val ∧ x.1.start.val ≤ x.1.end.val ∧ x.1.end = it.end ∧
      ∀ h < 2, rows x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 h =
        chacha20.innerBlock^[x.1.start.val - it.start.val] (rows a b c d h))
  · rintro ⟨it1, a1, b1, c1, d1⟩ ⟨h0, h1, h2, h3⟩
    simp only at h0 h1 h2 h3 ⊢
    by_cases hlt : it1.start.val < it1.end.val
    · have hb := body_V it1 hlt (lane32x8 a1) (lane32x8 b1) (lane32x8 c1) (lane32x8 d1)
      simp only [V_lane] at hb
      apply WP.spec_mono hb
      rintro r ⟨it', a', b', c', d', rfl, hs, he, hr⟩
      have he' : it'.end.val = it1.end.val := by rw [he]
      simp only
      refine ⟨⟨by omega, by omega, by rw [he, h2], fun h hh => ?_⟩, by omega⟩
      rw [hr h hh, h3 h hh, show it'.start.val - it.start.val = (it1.start.val - it.start.val) + 1 by omega,
        Function.iterate_succ_apply']
    · unfold low.x86_64.chacha20.core_2x_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho', hit⟩
      subst ho'
      have : it1.start.val = it.end.val := by rw [← h2]; omega
      simp only [WP.spec_ok]
      intro h hh
      rw [h3 h hh, this]
  · exact ⟨le_refl _, hle, rfl, fun h _ => by simp⟩

/-! ## Storing and XORing the keystream -/

@[step]
theorem extract_spec (k : Std.I32) (v : BitVec 256) :
    core.core_arch.x86.avx._mm256_extract_epi32 k v ⦃ x => x.bv = lane32x8 v (k.bv.toNat % 8) ⦄ := by
  simp [core.core_arch.x86.avx._mm256_extract_epi32]

/-- A vector's eight lanes, stored little-endian. -/
@[step]
theorem store_256_spec (v : BitVec 256) :
    low.x86_64.chacha20.store_256 v ⦃ r =>
      r.val.map (·.bv) = ((List.range 8).map (lane32x8 v)).flatMap BitVec.toLEBytes ⦄ := by
  unfold low.x86_64.chacha20.store_256
  step*
  all_goals try scalar_tac
  simp only [s21_post2, s18_post2, s15_post2, s12_post2, s9_post2, s6_post2, s3_post2, s_post2,
    s23_post, s22_post, s20_post, s19_post, s17_post, s16_post, s14_post, s13_post, s11_post, s10_post,
    s8_post, s7_post, s5_post, s4_post, s2_post, s1_post, Array.val_to_slice, a_post, a1_post, a2_post,
    a3_post, a4_post, a5_post, a6_post, a7_post, i1_post, i3_post, i5_post, i7_post, i9_post,
      i11_post,
    i13_post, i15_post, IScalar.hcast_bv_eq, i_post, i2_post, i4_post, i6_post, i8_post, i10_post,
    i12_post, i14_post]
  simp [List.setSlice!, vg.toLEBytes_eq, List.range_succ]

/-- The XOR loop, from `it.start` on. -/
theorem loop1_spec (it : core.ops.range.Range Usize) (xs ks : Slice U8) (hlen : ks.length = xs.length)
    (he : it.end.val = ks.length) (hs : it.start.val ≤ it.end.val) :
    low.x86_64.chacha20.core_2x_loop1 it xs ks ⦃ r => r.length = xs.length ∧
      ∀ j < xs.length, r.val[j]!.bv =
        if it.start.val ≤ j then xs.val[j]!.bv ^^^ ks.val[j]!.bv else xs.val[j]!.bv ⦄ := by
  unfold low.x86_64.chacha20.core_2x_loop1
  apply loop.spec_decr_nat (fun x => x.1.end.val - x.1.start.val)
    (fun x => x.2.length = xs.length ∧ it.start.val ≤ x.1.start.val ∧ x.1.start.val ≤ x.1.end.val ∧
      x.1.end = it.end ∧ ∀ j < xs.length, x.2.val[j]!.bv =
        if it.start.val ≤ j ∧ j < x.1.start.val then xs.val[j]!.bv ^^^ ks.val[j]!.bv else xs.val[j]!.bv)
  · rintro ⟨it1, x⟩ ⟨h0, h1, h2, h3, h4⟩
    simp only at h0 h1 h2 h3 h4 ⊢
    unfold low.x86_64.chacha20.core_2x_loop1.body
    by_cases hlt : it1.start.val < it1.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst, hen⟩
      subst ho'
      have hi : it1.start.val < xs.length := by rw [h3] at hlt; omega
      step*
      have he' : it'.end.val = it1.end.val := by rw [hen]
      refine ⟨?_, by omega, by omega, by rw [hen, h3], fun j hj => ?_, by omega⟩
      · simp [s_post, h0]
      · have hx := h4 it1.start.val hi
        simp only [s_post, Slice.set_val_eq]
        by_cases hj' : j = it1.start.val
        · subst hj'
          have hxl : it1.start.val < x.val.length := by simp [h0, hi]
          have e1 : i1.bv = ks.val[it1.start.val]!.bv := by
            rw [i1_post, getElem!_pos ks.val it1.start.val (by rw [← Slice.length, hlen]; exact hi)]
          have e2 : i2.bv = xs.val[it1.start.val]!.bv := by
            rw [i2_post, ← getElem!_pos x.val it1.start.val hxl, hx]; simp
          simp [getElem!_def, List.getElem?_set_self hxl, i3_post1, e1, e2, hst, h1]
        · have hne : x.val[j]! = (x.val.set it1.start.val i3)[j]! := by
            simp [getElem!_def, List.getElem?_set_ne (Ne.symm hj')]
          rw [← hne, h4 j hj]
          simp only [hst]
          split_ifs <;> first | rfl | (exfalso; omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho', hit⟩
      subst ho'
      have : it1.start.val = it.end.val := by rw [← h3]; omega
      simp only [WP.spec_ok]
      refine ⟨h0, fun j hj => ?_⟩
      rw [h4 j hj]
      have : j < it1.start.val := by omega
      simp [this]
  · exact ⟨rfl, le_refl _, hs, rfl, fun j _ => by simp⟩

/-- The XOR loop, from the start: the bytes XORed with the keystream's. -/
@[step]
theorem xor_loop_spec (it : core.ops.range.Range Usize) (xs ks : Slice U8) (hlen : ks.length = xs.length)
    (hs : it.start.val = 0) (he : it.end.val = ks.length) :
    low.x86_64.chacha20.core_2x_loop1 it xs ks ⦃ r => r.length = xs.length ∧
      bvs r.val = List.zipWith (· ^^^ ·) (bvs xs.val) (bvs ks.val) ⦄ := by
  apply WP.spec_mono (loop1_spec it xs ks hlen he (by omega))
  rintro r ⟨hr, h⟩
  refine ⟨hr, List.ext_getElem (by simp [bvs, hr, hlen]) fun j hj1 hj2 => ?_⟩
  have hrl : r.val.length = xs.length := hr
  have hxl : xs.val.length = xs.length := rfl
  have hkl : ks.val.length = xs.length := hlen
  have hjr : j < r.val.length := by simpa [bvs] using hj1
  have hj : j < xs.length := by omega
  have hjk : j < ks.val.length := by omega
  simp only [bvs, List.getElem_map, List.getElem_zipWith]
  rw [← getElem!_pos r.val j hjr, ← getElem!_pos xs.val j (by omega),
    ← getElem!_pos ks.val j hjk, h j hj, hs]
  simp

/-! ## Setting up and finishing the state -/

theorem setr_eq (e0 e1 e2 e3 e4 e5 e6 e7 : Std.I32) :
    core.core_arch.x86.avx._mm256_setr_epi32 e0 e1 e2 e3 e4 e5 e6 e7 =
      ok (V fun i => [e0.bv, e1.bv, e2.bv, e3.bv, e4.bv, e5.bv, e6.bv, e7.bv][i]!) := rfl

theorem add_eq (x y : BitVec 256) :
    core.core_arch.x86.avx2._mm256_add_epi32 x y = ok (V fun i => lane32x8 x i + lane32x8 y i) := rfl

theorem perm32_eq (x y : BitVec 256) :
    core.core_arch.x86.avx2._mm256_permute2x128_si256 32#i32 x y =
      ok (V fun i => if i < 4 then lane32x8 x i else lane32x8 y (i - 4)) := by
  simp only [core.core_arch.x86.avx2._mm256_permute2x128_si256, ok.injEq,
    show (32#i32).bv.toNat = 32 from rfl]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_ofHalves, getLsbD_V]
  simp only [hk, decide_true, Bool.true_and]
  interval_cases k <;> simp [lane32x8, half]

theorem perm49_eq (x y : BitVec 256) :
    core.core_arch.x86.avx2._mm256_permute2x128_si256 49#i32 x y =
      ok (V fun i => if i < 4 then lane32x8 x (i + 4) else lane32x8 y i) := by
  simp only [core.core_arch.x86.avx2._mm256_permute2x128_si256, ok.injEq,
    show (49#i32).bv.toNat = 49 from rfl]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_ofHalves, getLsbD_V]
  simp only [hk, decide_true, Bool.true_and]
  interval_cases k <;> simp [lane32x8, half]

/-! ## Lists -/

theorem list8 {α : Type} (l : List α) (h : l.length = 8) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7, l = [a0, a1, a2, a3, a4, a5, a6, a7] := by
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, l⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at h
  exact ⟨_, _, _, _, _, _, _, _, rfl⟩

theorem list4 {α : Type} (l : List α) (h : l.length = 4) : ∃ a0 a1 a2 a3, l = [a0, a1, a2, a3] := by
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, l⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨_, _, _, _, rfl⟩

theorem setSlice!_split {α : Type} (s s' : List α) (i : Nat) (h : i + s'.length ≤ s.length) :
    s.setSlice! i s' = s.take i ++ s' ++ s.drop (i + s'.length) := by
  simp only [List.setSlice!]
  rw [Nat.min_eq_left (by omega), List.take_length]

theorem length_setSlice! {α : Type} (s s' : List α) (i : Nat) : (s.setSlice! i s').length = s.length := by
  simp only [List.setSlice!, List.length_append, List.length_take, List.length_drop]
  omega

theorem setSlice4 {α : Type} (z l0 l1 l2 l3 : List α) (hz : z.length = 128) (h0 : l0.length = 32)
    (h1 : l1.length = 32) (h2 : l2.length = 32) (h3 : l3.length = 32) :
    (((z.setSlice! 0 l0).setSlice! 32 l1).setSlice! 64 l2).setSlice! 96 l3 = l0 ++ l1 ++ l2 ++ l3 := by
  rw [setSlice!_split _ _ _ (by simp only [length_setSlice!, hz, h3]; omega),
    setSlice!_split _ _ _ (by simp only [length_setSlice!, hz, h2]; omega),
    setSlice!_split _ _ _ (by simp only [length_setSlice!, hz, h1]; omega),
    setSlice!_split _ _ _ (by simp only [hz, h0]; omega)]
  simp [List.take_append, List.drop_append, h0, h1, h2, h3, hz, List.take_of_length_le]

/-- `chacha20.encrypt` of up to two blocks: the message XOR their keystream,
the second block's counter wrapping as the model's 32-bit counter does, which
RFC 8439 forbids and `Kernel`'s bound rules out. -/
theorem encrypt_two (key nonce msg : List (BitVec 8)) (c : BitVec 32) (hk : key.length = 32)
    (hn : nonce.length = 12) (hm : msg.length ≤ 128) :
    chacha20.encrypt key c nonce msg =
      List.zipWith (· ^^^ ·) msg (chacha20.block key c nonce ++ chacha20.block key (c + 1) nonce) := by
  have hg : ∀ j, (chacha20.block key (c + BitVec.ofNat 32 j) nonce).length = 64 :=
    fun j => s2n.length_block _ _ _ hk hn
  have h2 : chacha20.block key c nonce ++ chacha20.block key (c + 1) nonce =
      (List.range 2).flatMap fun j => chacha20.block key (c + BitVec.ofNat 32 j) nonce := by
    rw [show List.range 2 = [0, 1] from rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, BitVec.add_zero,
      show BitVec.ofNat 32 1 = 1 from rfl]
  rw [h2, s2n.zipWith_flatMap _ _ hg, chacha20.encrypt]
  set M := (msg.length + 63) / 64
  have hr : List.range 2 = List.range (M + (2 - M)) := by rw [Nat.add_sub_cancel' (by omega : M ≤ 2)]
  rw [hr, List.range_add, List.flatMap_append]
  conv => lhs; rw [← List.append_nil (List.flatMap _ _)]
  refine congrArg _ ?_
  symm
  rw [List.flatMap_eq_nil_iff]
  intro j hj
  simp only [List.mem_map, List.mem_range] at hj
  obtain ⟨k, -, rfl⟩ := hj
  have : msg.length ≤ 64 * (M + k) := by omega
  simp [List.drop_eq_nil_of_le this]

/-! ## `core_2x` and `cipher_avx2` -/

/-- `core_2x` encrypts up to 128 bytes from block `counter`. -/
@[step]
theorem core_2x_spec (key : Std.Array U32 8#usize) (cn : Std.Array U32 4#usize) (counter : U32)
    (xs : Slice U8) (hx : xs.length ≤ 128) :
    low.x86_64.chacha20.core_2x key cn counter xs ⦃ r => r.length = xs.length ∧
      bvs r.val = chacha20.encrypt (wordBytes key.val) counter.bv (wordBytes (cn.val.drop 1)) (bvs xs.val) ⦄ := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, hk⟩ := list8 key.val (by simp)
  obtain ⟨n0, n1, n2, n3, hn⟩ := list4 cn.val (by simp)
  unfold low.x86_64.chacha20.core_2x
  simp only [setr_eq, add_eq, perm32_eq, perm49_eq, bind_ok]
  step*
  all_goals try scalar_tac
  refine ⟨r_post, ?_⟩
  have hw : ∀ x : U32, (UScalar.hcast IScalarTy.I32 x).bv = x.bv := fun x => by simp [UScalar.hcast_bv_eq]
  have h0 := a_post 0 (by decide)
  have h1 := a_post 1 (by decide)
  simp only [i_post, i1_post, i2_post, i3_post, i4_post, i5_post, i6_post, i7_post, i8_post,
    i9_post, i10_post, i11_post, i12_post, i13_post, i14_post, i15_post, i16_post, i17_post,
    i18_post, i19_post, i20_post, i21_post, i22_post, i23_post, i24_post, i25_post, i26_post,
    i27_post, i28_post, i29_post, i30_post, i31_post, i32_post, i33_post, i34_post, i35_post, hw]
    at h0 h1
  simp only [rows, List.flatMap_cons, List.flatMap_nil, show List.range 4 = [0, 1, 2, 3] from rfl,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil] at h0 h1
  simp (disch := omega) only [lane_V, Nat.reduceMul, Nat.reduceAdd, hk, hn, List.getElem_cons_zero,
    List.getElem_cons_succ, List.getElem!_cons_zero, List.getElem!_cons_succ, Nat.sub_zero] at h0 h1
  simp only [show I32.bv 1634760805#i32 = (0x61707865 : BitVec 32) from rfl,
    show I32.bv 857760878#i32 = (0x3320646e : BitVec 32) from rfl,
    show I32.bv 2036477234#i32 = (0x79622d32 : BitVec 32) from rfl,
    show I32.bv 1797285236#i32 = (0x6b206574 : BitVec 32) from rfl,
    core.num.U32.wrapping_add_bv_eq, show (1#u32).bv = (1 : BitVec 32) from rfl] at h0 h1
  have hkw : chacha20.words (wordBytes key.val) = [k0.bv, k1.bv, k2.bv, k3.bv, k4.bv, k5.bv, k6.bv, k7.bv] := by
    rw [wordBytes, vg.words_flatMap, hk]; rfl
  have hnw : chacha20.words (wordBytes (cn.val.drop 1)) = [n1.bv, n2.bv, n3.bv] := by
    rw [wordBytes, vg.words_flatMap, hn]; rfl
  rw [r_post1, encrypt_two _ _ _ _ (by simp [length_wordBytes]) (by simp [length_wordBytes, hn])
    (by simp [bvs]; omega)]
  simp only [chacha20.block, hkw, hnw, List.cons_append, List.nil_append, ← h0, ← h1]
  rw [ks5_post]
  simp only [s9_post2, s6_post2, s3_post2, s_post2, s11_post, s10_post, s8_post, s7_post, s5_post, s4_post,
    s2_post, s1_post, Array.val_to_slice]
  rw [setSlice4 _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  have hsl : bvs (List.slice 0 xs.len.val (a2.val ++ a3.val ++ a4.val ++ a5.val)) =
      (bvs (a2.val ++ a3.val ++ a4.val ++ a5.val)).take (bvs xs.val).length := by
    simp [bvs, List.slice, List.map_take]
  rw [hsl, vg.zipWith_take_length]
  refine congrArg _ ?_
  simp only [bvs, List.map_append, a2_post, a3_post, a4_post, a5_post]
  simp (disch := omega) only [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.map_cons,
    List.map_nil, lane_V]
  simp (disch := omega) only [Nat.reduceLT, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub,
    List.getElem!_cons_zero, List.getElem!_cons_succ, i_post, i1_post, i2_post, i3_post, i4_post,
      i5_post, i6_post, i7_post, i8_post, i9_post, i10_post, i11_post, i12_post, i13_post,
      i14_post, i15_post, i16_post, i17_post, i18_post, i19_post, i20_post, i21_post, i22_post,
      i23_post, i24_post, i25_post, i26_post, i27_post, i28_post, i29_post, i30_post, i31_post,
      i32_post, i33_post, i34_post, i35_post, hw, hk, hn, List.getElem_cons_zero,
    List.getElem_cons_succ, show I32.bv 1634760805#i32 = (0x61707865 : BitVec 32) from rfl,
    show I32.bv 857760878#i32 = (0x3320646e : BitVec 32) from rfl,
    show I32.bv 2036477234#i32 = (0x79622d32 : BitVec 32) from rfl,
    show I32.bv 1797285236#i32 = (0x6b206574 : BitVec 32) from rfl,
    core.num.U32.wrapping_add_bv_eq, show (1#u32).bv = (1 : BitVec 32) from rfl]
  simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.flatMap_cons, List.flatMap_nil,
    List.append_assoc, List.append_nil]

theorem encrypt_nil (key nonce : List (BitVec 8)) (c : BitVec 32) : chacha20.encrypt key c nonce [] = [] := by
  simp [chacha20.encrypt]

/-- One chunk of `cipher_avx2`'s loop: the bytes before `d` are encrypted, the
rest are the message's, and the chunk from `d` to `e` is encrypted from block
`d / 64` on. -/
theorem chunk_step (K N B M S1 : List (BitVec 8)) (c0 : BitVec 32) (d e : Nat)
    (hB : B.length = M.length) (hde : d ≤ e) (he : e ≤ B.length) (hS : S1.length = e - d)
    (hd : d % 64 = 0) (h3 : B.take d = chacha20.encrypt K c0 N (M.take d)) (h4 : B.drop d = M.drop d)
    (hS1 : S1 = chacha20.encrypt K (c0 + BitVec.ofNat 32 (d / 64)) N ((M.drop d).take (e - d))) :
    (B.setSlice! d S1).take e = chacha20.encrypt K c0 N (M.take e) ∧
      (B.setSlice! d S1).drop e = M.drop e := by
  rw [setSlice!_split B S1 d (by omega)]
  have hA : (B.take d ++ S1).length = e := by simp [hS]; omega
  constructor
  · rw [List.take_left' hA, h3, hS1, ← vg.encrypt_append _ _ _ _ _ (d / 64) (by simp; omega),
      ← List.take_add, Nat.add_sub_cancel' hde]
  · rw [List.drop_left' hA, show d + S1.length = e by omega]
    rw [show e = d + (e - d) by omega, ← List.drop_drop, h4, List.drop_drop]

/-- `cipher_avx2`'s loop: if the bytes before `done` are encrypted and the rest
are the message's, the whole buffer ends encrypted. -/
theorem cipher_avx2_loop_spec (key : Std.Array U32 8#usize) (cn : Std.Array U32 4#usize)
    (msg : List (BitVec 8)) (buffer : Slice U8) (counter : U32) (done : Usize)
    (hm : msg.length = buffer.length) (hd : done.val ≤ buffer.length)
    (hc : done.val % 128 = 0 ∧ counter.bv = cn.val[0]!.bv + BitVec.ofNat 32 (done.val / 64) ∨
      done.val = buffer.length)
    (hpre : (bvs buffer.val).take done.val =
      chacha20.encrypt (wordBytes key.val) cn.val[0]!.bv (wordBytes (cn.val.drop 1)) (msg.take done.val))
    (hpost : (bvs buffer.val).drop done.val = msg.drop done.val) :
    low.x86_64.chacha20.cipher_avx2_loop key cn buffer counter done ⦃ r =>
      bvs r.val = chacha20.encrypt (wordBytes key.val) cn.val[0]!.bv (wordBytes (cn.val.drop 1)) msg ⦄ := by
  unfold low.x86_64.chacha20.cipher_avx2_loop
  apply loop.spec_decr_nat (fun x => buffer.length - x.2.2.val)
    (fun x => x.1.length = buffer.length ∧ x.2.2.val ≤ buffer.length ∧
      (x.2.2.val % 128 = 0 ∧ x.2.1.bv = cn.val[0]!.bv + BitVec.ofNat 32 (x.2.2.val / 64) ∨
        x.2.2.val = buffer.length) ∧
      (bvs x.1.val).take x.2.2.val =
        chacha20.encrypt (wordBytes key.val) cn.val[0]!.bv (wordBytes (cn.val.drop 1)) (msg.take x.2.2.val) ∧
      (bvs x.1.val).drop x.2.2.val = msg.drop x.2.2.val)
  · rintro ⟨buf, ctr, dn⟩ ⟨h0, h1, h2, h3, h4⟩
    simp only at h0 h1 h2 h3 h4 ⊢
    have hbl : buf.val.length = buf.length := rfl
    unfold low.x86_64.chacha20.cipher_avx2_loop.body
    by_cases hlt : dn.val < buf.length
    · have h2' : dn.val % 128 = 0 ∧ ctr.bv = cn.val[0]!.bv + BitVec.ofNat 32 (dn.val / 64) := by
        rcases h2 with h2 | h2
        · exact h2
        · omega
      step*
      split <;> step*
      all_goals
        have hi3 : i3.val ≤ buf.length := by scalar_tac
        have hb := chunk_step (wordBytes key.val) (wordBytes (cn.val.drop 1)) (bvs buf.val) msg (bvs s1.val)
          cn.val[0]!.bv dn.val i3.val (by simp [bvs]; omega) (by scalar_tac) (by simp [bvs]; omega)
          (by simp [bvs, s1_post, s_post1]) (by omega) h3 h4 (by
            rw [s1_post1, h2'.2, s_post]
            congr 1
            simp [bvs, List.slice, ← h4, List.map_take, List.map_drop])
        simp only [s_post2, Slice.setSlice!_val, bvs, List.map_setSlice!] at hb ⊢
        have hlen : buf.len.val = buf.length := by simp
        refine ⟨by simp [h0], by omega, ?_, hb.1, hb.2, by omega⟩
        by_cases hfull : i3.val = buffer.length
        · exact Or.inr hfull
        · have h128 : i3.val = dn.val + 128 := by omega
          refine Or.inl ⟨by omega, ?_⟩
          rw [counter1_post, core.num.U32.wrapping_add_bv_eq, h2'.2, h128,
            show (dn.val + 128) / 64 = dn.val / 64 + 2 by omega, BitVec.ofNat_add, BitVec.add_assoc]
          rfl
    · simp only [Slice.len, show ¬ dn < buf.len from by scalar_tac, ite_false, WP.spec_ok]
      have hdn : dn.val = buffer.length := by omega
      have hl : (bvs buf.val).length = dn.val := by simp [bvs]; omega
      have hml : msg.length ≤ dn.val := by omega
      rw [← hl, List.take_length, hl, List.take_of_length_le hml] at h3
      exact h3
  · exact ⟨rfl, hd, hc, hpre, hpost⟩

/-- The kernel meets its contract, which `Rind.X86_64.VgChaCha20` takes as the
hypothesis `Kernel`. -/
theorem kernel : Kernel := by
  intro key cn buffer _
  unfold low.x86_64.chacha20.cipher_avx2
  step as ⟨counter, hc⟩
  apply cipher_avx2_loop_spec key cn (bvs buffer.val) buffer counter 0#usize (by simp [bvs]) (by simp)
    (Or.inl ⟨by simp, by rw [hc, ← getElem!_pos]; simp⟩) (by simp [encrypt_nil]) (by simp)

end rind.x86_64.avx2
