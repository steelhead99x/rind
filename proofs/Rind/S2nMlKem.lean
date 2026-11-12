import Rind.MlKem

/-!
# s2n-bignum's ML-KEM specs

The functions s2n-bignum's ML-KEM postconditions name, from
`common/mlkem_mldsa.ml`, `arm/proofs/mlkem_basemul_k3.ml`,
`x86/proofs/mlkem_mulcache_compute.ml`, and `x86/proofs/mlkem_basemul_k3.ml` at b4f17ee7, which
`thirdparty/s2n-bignum` holds, transliterated: HOL Light's `num->int` is
`ℕ → ℤ`, `isum (0..127)` is `∑ j ∈ range 128`, `&a pow n` is `(a : ℤ) ^ n`, and
`x rem &3329` is `x % 3329`, both the remainder in `[0, 3329)`. `bitreverse7`
reverses the seven bits of `word n : 7 word`, as `BitVec.reverse` does.

Each postcondition holds modulo 3329, so the bridges state each in `Zq`,
against FIPS 203's `NTT`, `NTTInv`, and `MultiplyNTTs`. `poly f` reads
s2n-bignum's coefficient function as a FIPS 203 polynomial. The aarch64
routines keep FIPS 203's coefficient order; the x86_64 AVX2 NTTs keep
coefficient `avx2Layout p` at position `p`, and x86_64's `mlkem_basemul_k3`
reads each 32-coefficient block's pairs' even halves, then their odd halves.
The inverse NTTs and the base multiplications also scale by `2 ^ 16` and
`2 ^ -16`, Montgomery's factor.
-/

open Spec.MLKEM Finset rind.spec.mlkem

namespace rind.spec.s2n

/-! ## Transliteration -/

/-- `bitreverse7`. -/
def bitreverse7 (n : ℕ) : ℕ := (BitVec.ofNat 7 n).reverse.toNat

/-- `bitreverse_pairs`. -/
def bitreversePairs (i : ℕ) : ℕ := 2 * bitreverse7 (i / 2) + i % 2

/-- `avx2_ntt_order`. -/
def avx2NttOrder (i : ℕ) : ℕ := bitreverse7 (64 * (i / 64) + (i % 64) / 16 + 4 * (i % 16))

/-- `avx2_ntt_order'`. -/
def avx2NttOrder' (i : ℕ) : ℕ :=
  let j := bitreverse7 i
  64 * (j / 64) + 16 * (j % 4) + (j % 64) / 4

/-- `avx2_reorder`. -/
def avx2Reorder (i : ℕ) : ℕ :=
  let r := (i / 16) % 2
  let q := 16 * (i / 32) + i % 16
  2 * avx2NttOrder q + r

/-- `tomont_3329`. -/
def tomont3329 (a : ℕ → ℤ) : ℕ → ℤ := fun i => (2 ^ 16 * a i) % 3329

/-- `mulcache`. -/
def mulcache (f : ℕ → ℤ) (k : ℕ) : ℤ := (f (2 * k + 1) * 17 ^ (2 * bitreverse7 k + 1)) % 3329

/-- `inverse_ntt`. -/
def inverseNtt (f : ℕ → ℤ) (k : ℕ) : ℤ :=
  (512 * ∑ j ∈ range 128, f (2 * bitreverse7 j + k % 2) * 1175 ^ ((2 * j + 1) * (k / 2))) % 3329

/-- `forward_ntt`. -/
def forwardNtt (f : ℕ → ℤ) (k : ℕ) : ℤ :=
  (∑ j ∈ range 128, f (2 * j + k % 2) * 17 ^ ((2 * bitreverse7 (k / 2) + 1) * j)) % 3329

/-- `avx2_forward_ntt`. -/
def avx2ForwardNtt (f : ℕ → ℤ) (k : ℕ) : ℤ :=
  let r := (k / 16) % 2
  let q := 16 * (k / 32) + k % 16
  (∑ j ∈ range 128, f (2 * j + r) * 17 ^ ((2 * avx2NttOrder q + 1) * j)) % 3329

/-- `avx2_inverse_ntt`. -/
def avx2InverseNtt (f : ℕ → ℤ) (k : ℕ) : ℤ :=
  (512 * ∑ j ∈ range 128,
      f (avx2NttOrder' j / 16 * 32 + k % 2 * 16 + avx2NttOrder' j % 16) *
        1175 ^ ((2 * j + 1) * (k / 2))) % 3329

/-- `pmull`. -/
def pmull (x0 x1 y0 y1 : ℤ) : ℤ := x1 * y1 + x0 * y0

/-- `pmull_acc3`. -/
def pmullAcc3 (x00 x01 y00 y01 x10 x11 y10 y11 x20 x21 y20 y21 : ℤ) : ℤ :=
  pmull x20 x21 y20 y21 + pmull x10 x11 y10 y11 + pmull x00 x01 y00 y01

/-- `inverse_mod 3329 65536`: the inverse of `2 ^ 16` modulo 3329 in `[0, 3329)`,
which `inverseMod_spec` pins. -/
def inverseMod : ℕ := 169

theorem inverseMod_spec : inverseMod < 3329 ∧ 65536 * inverseMod % 3329 = 1 := by decide

/-- `pmul_acc3`. -/
def pmulAcc3 (x00 x01 y00 y01 x10 x11 y10 y11 x20 x21 y20 y21 : ℤ) : ℤ :=
  ((inverseMod : ℤ) * pmullAcc3 x00 x01 y00 y01 x10 x11 y10 y11 x20 x21 y20 y21) % 3329

/-- `basemul3_even`. -/
def basemul3Even (x0 y0 y0t x1 y1 y1t x2 y2 y2t : ℕ → ℤ) (i : ℕ) : ℤ :=
  pmulAcc3 (x0 (2 * i)) (x0 (2 * i + 1)) (y0 (2 * i)) (y0t i)
    (x1 (2 * i)) (x1 (2 * i + 1)) (y1 (2 * i)) (y1t i)
    (x2 (2 * i)) (x2 (2 * i + 1)) (y2 (2 * i)) (y2t i)

/-- `basemul3_odd`. -/
def basemul3Odd (x0 y0 x1 y1 x2 y2 : ℕ → ℤ) (i : ℕ) : ℤ :=
  pmulAcc3 (x0 (2 * i)) (x0 (2 * i + 1)) (y0 (2 * i + 1)) (y0 (2 * i))
    (x1 (2 * i)) (x1 (2 * i + 1)) (y1 (2 * i + 1)) (y1 (2 * i))
    (x2 (2 * i)) (x2 (2 * i + 1)) (y2 (2 * i + 1)) (y2 (2 * i))

/-- `avx2_mulcache`, from `x86/proofs/mlkem_mulcache_compute.ml`. -/
def avx2Mulcache (f : ℕ → ℤ) (k : ℕ) : ℤ :=
  let r := k / 64
  let q := k % 64
  let s := r * 128 + 32 * (q / 16) + q % 16 + 16
  let t := 64 * r + 2 * (q / 32) + 4 * (q % 16)
  (f s * 17 ^ (2 * bitreverse7 t + 1)) % 3329

/-- `pmul0`, from `x86/proofs/mlkem_basemul_k3.ml`, as are those below. -/
def pmul0 (a b c dz : ℤ) : ℤ := b * dz + a * c

/-- `pmul0_odd`. -/
def pmul0Odd (a b c dz : ℤ) : ℤ := a * c - b * dz

/-- `pmul1`. -/
def pmul1 (a b c d : ℤ) : ℤ := b * c + a * d

/-- `pmulacc0_k3`. -/
def pmulacc0K3 (a0 b0 c0 _d0 dz0 a1 b1 c1 _d1 dz1 a2 b2 c2 _d2 dz2 : ℤ) : ℤ :=
  pmul0 a0 b0 c0 dz0 + pmul0 a1 b1 c1 dz1 + pmul0 a2 b2 c2 dz2

/-- `pmulacc0_odd_k3`. -/
def pmulacc0OddK3 (a0 b0 c0 _d0 dz0 a1 b1 c1 _d1 dz1 a2 b2 c2 _d2 dz2 : ℤ) : ℤ :=
  pmul0Odd a0 b0 c0 dz0 + pmul0Odd a1 b1 c1 dz1 + pmul0Odd a2 b2 c2 dz2

/-- `pmulacc1_k3`. -/
def pmulacc1K3 (a0 b0 c0 d0 _dz0 a1 b1 c1 d1 _dz1 a2 b2 c2 d2 _dz2 : ℤ) : ℤ :=
  pmul1 a0 b0 c0 d0 + pmul1 a1 b1 c1 d1 + pmul1 a2 b2 c2 d2

/-- `pmulaccred0_k3`. -/
def pmulaccred0K3 (a0 b0 c0 d0 dz0 a1 b1 c1 d1 dz1 a2 b2 c2 d2 dz2 : ℤ) : ℤ :=
  ((inverseMod : ℤ) * pmulacc0K3 a0 b0 c0 d0 dz0 a1 b1 c1 d1 dz1 a2 b2 c2 d2 dz2) % 3329

/-- `pmulaccred0_odd_k3`. -/
def pmulaccred0OddK3 (a0 b0 c0 d0 dz0 a1 b1 c1 d1 dz1 a2 b2 c2 d2 dz2 : ℤ) : ℤ :=
  ((inverseMod : ℤ) * pmulacc0OddK3 a0 b0 c0 d0 dz0 a1 b1 c1 d1 dz1 a2 b2 c2 d2 dz2) % 3329

/-- `pmulaccred1_k3`. -/
def pmulaccred1K3 (a0 b0 c0 d0 dz0 a1 b1 c1 d1 dz1 a2 b2 c2 d2 dz2 : ℤ) : ℤ :=
  ((inverseMod : ℤ) * pmulacc1K3 a0 b0 c0 d0 dz0 a1 b1 c1 d1 dz1 a2 b2 c2 d2 dz2) % 3329

/-! ## Bridges -/

/-- s2n-bignum's coefficients `f 0, …, f 255` as a FIPS 203 polynomial. -/
def poly (f : ℕ → ℤ) : Polynomial := Vector.ofFn fun i => (f i.val : Zq)

/-- The FIPS 203 coefficient the AVX2 NTTs keep at position `p`. -/
def avx2Layout (p : ℕ) : ℕ := bitreversePairs (avx2Reorder p)

theorem poly_get (f : ℕ → ℤ) (i : ℕ) (hi : i < 256) : (poly f)[i]! = (f i : Zq) := by
  rw [getElem!_pos (poly f) i hi]
  simp [poly]

theorem cast_rem (x : ℤ) : ((x % 3329 : ℤ) : Zq) = (x : Zq) := ZMod.intCast_mod x 3329

theorem bitreverse7_eq : ∀ n < 128, bitreverse7 n = bitRev 7 n := by decide +kernel

theorem ζ_eq : (17 : Zq) = ζ := rfl

/-- `forward_ntt`, which the aarch64 `mlkem_ntt` computes, is FIPS 203's `NTT`. -/
theorem forwardNtt_eq (f : ℕ → ℤ) (k : ℕ) (hk : k < 256) :
    (forwardNtt f k : Zq) = (NTT (poly f))[k]! := by
  have hi : k / 2 < 128 := by omega
  have hb : k % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [forwardNtt, cast_rem, ← Nat.div_add_mod k 2, NTT_get _ _ _ hi hb,
    bitreverse7_eq _ (by omega)]
  push_cast
  refine sum_congr rfl fun j hj => ?_
  rw [poly_get f _ (by have := mem_range.1 hj; omega), ζ_eq,
    show (2 * (k / 2) + k % 2) / 2 = k / 2 by omega, show (2 * (k / 2) + k % 2) % 2 = k % 2 by omega]

/-- The sum the inverse NTTs scale: FIPS 203's `NTTInv` in Montgomery form, with
its terms in s2n-bignum's order. -/
theorem inverse_sum (g : Polynomial) (k : ℕ) (hk : k < 256) :
    (512 : Zq) * ∑ j ∈ range 128, g[2 * bitRev 7 j + k % 2]! * 1175 ^ ((2 * j + 1) * (k / 2)) =
      2 ^ 16 * (NTTInv g)[k]! := by
  have hj : k / 2 < 128 := by omega
  have hb : k % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [← Nat.div_add_mod k 2, NTTInv_get g _ _ hj hb, ← mul_assoc,
    show (2 : Zq) ^ 16 * 3303 = 512 by decide,
    show (2 * (k / 2) + k % 2) / 2 = k / 2 by omega, show (2 * (k / 2) + k % 2) % 2 = k % 2 by omega]
  refine congrArg (512 * ·) ?_
  refine sum_nbij' (bitRev 7) (bitRev 7) (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
    (fun j hj => ?_) (fun j hj => ?_)
  · exact mem_range.2 (bitRev_lt j (mem_range.1 hj))
  · exact mem_range.2 (bitRev_lt j (mem_range.1 hj))
  · exact bitRev_bitRev j (mem_range.1 hj)
  · exact bitRev_bitRev j (mem_range.1 hj)
  · rw [bitRev_bitRev j (mem_range.1 hj)]

/-- `inverse_ntt`, which the aarch64 `mlkem_intt` computes, is FIPS 203's
`NTTInv` times `2 ^ 16`. -/
theorem inverseNtt_eq (f : ℕ → ℤ) (k : ℕ) (hk : k < 256) :
    (inverseNtt f k : Zq) = 2 ^ 16 * (NTTInv (poly f))[k]! := by
  rw [← inverse_sum _ k hk, inverseNtt, cast_rem]
  push_cast
  refine congrArg (512 * ·) (sum_congr rfl fun j hj => ?_)
  have := bitRev_lt j (mem_range.1 hj)
  have : k % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [bitreverse7_eq j (mem_range.1 hj), poly_get f _ (by omega)]

/-- `mulcache`, which the aarch64 `mlkem_mulcache_compute` computes, is each odd
coefficient times the root `MultiplyNTTs` multiplies it by. -/
theorem mulcache_eq (f : ℕ → ℤ) (k : ℕ) (hk : k < 128) :
    (mulcache f k : Zq) = (poly f)[2 * k + 1]! * ζ ^ (2 * bitRev 7 k + 1) := by
  rw [mulcache, cast_rem, poly_get f _ (by omega), bitreverse7_eq k hk]
  push_cast
  rfl

theorem multiplyNTTs_even (f g : Polynomial) (i : ℕ) (hi : i < 128) :
    (MultiplyNTTs f g)[2 * i]! = f[2 * i]! * g[2 * i]! + f[2 * i + 1]! * g[2 * i + 1]! * ζ ^ (2 * bitRev 7 i + 1) := by
  rw [Symcrust.Properties.MLKEM.Ntt.MultiplyNTTs_eq_ofFn, Vector.getElem!_ofFn _ _ (by omega)]
  simp only [show 2 * i % 2 = 0 by omega, show 2 * i / 2 = i by omega, ite_true]
  rfl

theorem multiplyNTTs_odd (f g : Polynomial) (i : ℕ) (hi : i < 128) :
    (MultiplyNTTs f g)[2 * i + 1]! = f[2 * i]! * g[2 * i + 1]! + f[2 * i + 1]! * g[2 * i]! := by
  rw [Symcrust.Properties.MLKEM.Ntt.MultiplyNTTs_eq_ofFn, Vector.getElem!_ofFn _ _ (by omega)]
  simp only [show (2 * i + 1) % 2 = 1 by omega, show (2 * i + 1) / 2 = i by omega]
  rfl

theorem inverseMod_eq : (2 : Zq) ^ 16 * ((inverseMod : ℤ) : Zq) = 1 := by decide

/-- `basemul3_even`, which the aarch64 `mlkem_basemul_k3` computes, is the sum of
three `MultiplyNTTs` products' even coefficients times `2 ^ -16`, given each
`ymt` is `ym`'s `mulcache`. -/
theorem basemul3Even_eq (x0 y0 y0t x1 y1 y1t x2 y2 y2t : ℕ → ℤ) (i : ℕ) (hi : i < 128)
    (h0 : (y0t i : Zq) = mulcache y0 i) (h1 : (y1t i : Zq) = mulcache y1 i)
    (h2 : (y2t i : Zq) = mulcache y2 i) :
    2 ^ 16 * (basemul3Even x0 y0 y0t x1 y1 y1t x2 y2 y2t i : Zq) =
      (MultiplyNTTs (poly x0) (poly y0))[2 * i]! + (MultiplyNTTs (poly x1) (poly y1))[2 * i]! +
        (MultiplyNTTs (poly x2) (poly y2))[2 * i]! := by
  simp only [multiplyNTTs_even _ _ i hi, poly_get _ _ (by omega : 2 * i < 256),
    poly_get _ _ (by omega : 2 * i + 1 < 256)]
  rw [basemul3Even, pmulAcc3, cast_rem, Int.cast_mul, ← mul_assoc, inverseMod_eq, one_mul]
  simp only [pmullAcc3, pmull]
  push_cast
  rw [h0, h1, h2, mulcache_eq _ _ hi, mulcache_eq _ _ hi, mulcache_eq _ _ hi,
    poly_get _ _ (by omega : 2 * i + 1 < 256), poly_get _ _ (by omega : 2 * i + 1 < 256),
    poly_get _ _ (by omega : 2 * i + 1 < 256)]
  ring

/-- `basemul3_odd`, which the aarch64 `mlkem_basemul_k3` computes, is the sum of
three `MultiplyNTTs` products' odd coefficients times `2 ^ -16`. -/
theorem basemul3Odd_eq (x0 y0 x1 y1 x2 y2 : ℕ → ℤ) (i : ℕ) (hi : i < 128) :
    2 ^ 16 * (basemul3Odd x0 y0 x1 y1 x2 y2 i : Zq) =
      (MultiplyNTTs (poly x0) (poly y0))[2 * i + 1]! +
        (MultiplyNTTs (poly x1) (poly y1))[2 * i + 1]! +
        (MultiplyNTTs (poly x2) (poly y2))[2 * i + 1]! := by
  simp only [multiplyNTTs_odd _ _ i hi, poly_get _ _ (by omega : 2 * i < 256),
    poly_get _ _ (by omega : 2 * i + 1 < 256)]
  rw [basemul3Odd, pmulAcc3, cast_rem, Int.cast_mul, ← mul_assoc, inverseMod_eq, one_mul]
  simp only [pmullAcc3, pmull]
  push_cast
  ring

/-- `tomont_3329`, which `mlkem_tomont` computes on both targets, multiplies by `2 ^ 16`. -/
theorem tomont3329_eq (a : ℕ → ℤ) (i : ℕ) : (tomont3329 a i : Zq) = 2 ^ 16 * (a i : Zq) := by
  rw [tomont3329, cast_rem]
  push_cast
  rfl

theorem avx2_forward_index : ∀ p < 256,
    avx2NttOrder (16 * (p / 32) + p % 16) < 128 ∧
    avx2Layout p = 2 * bitRev 7 (avx2NttOrder (16 * (p / 32) + p % 16)) + (p / 16) % 2 := by
  decide +kernel

/-- `avx2_forward_ntt`, which the x86_64 `mlkem_ntt` computes, is FIPS 203's
`NTT` in the AVX2 layout. -/
theorem avx2ForwardNtt_eq (f : ℕ → ℤ) (p : ℕ) (hp : p < 256) :
    (avx2ForwardNtt f p : Zq) = (NTT (poly f))[avx2Layout p]! := by
  obtain ⟨ho, hl⟩ := avx2_forward_index p hp
  have hb : (p / 16) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [hl, NTT_get _ _ _ (bitRev_lt _ ho) hb, bitRev_bitRev _ ho, avx2ForwardNtt, cast_rem]
  push_cast
  refine sum_congr rfl fun j hj => ?_
  rw [poly_get f _ (by have := mem_range.1 hj; omega), ζ_eq]

theorem avx2_inverse_index : ∀ j < 128, ∀ b < 2,
    avx2NttOrder' j / 16 * 32 + b * 16 + avx2NttOrder' j % 16 < 256 ∧
    avx2Layout (avx2NttOrder' j / 16 * 32 + b * 16 + avx2NttOrder' j % 16) = 2 * bitRev 7 j + b := by
  decide +kernel

/-- `avx2_inverse_ntt`, which the x86_64 `mlkem_intt` computes, is FIPS 203's
`NTTInv` times `2 ^ 16`, given its input `f` holds `g` in the AVX2 layout. -/
theorem avx2InverseNtt_eq (f : ℕ → ℤ) (g : Polynomial)
    (h : ∀ p < 256, (f p : Zq) = g[avx2Layout p]!) (k : ℕ) (hk : k < 256) :
    (avx2InverseNtt f k : Zq) = 2 ^ 16 * (NTTInv g)[k]! := by
  rw [← inverse_sum _ k hk, avx2InverseNtt, cast_rem]
  push_cast
  refine congrArg (512 * ·) (sum_congr rfl fun j hj => ?_)
  obtain ⟨hlt, hl⟩ := avx2_inverse_index j (mem_range.1 hj) (k % 2) (Nat.mod_lt _ (by norm_num))
  rw [h _ hlt, hl]

/-! ### x86_64's base multiplication

x86_64's `mlkem_basemul_k3` postcondition names its inputs by block `j < 8`
and lane `i < 16`: `a i j`, `b i j` are the first factor's coefficients at
positions `32 * j + i` and `32 * j + 16 + i`, `c i j`, `d i j` the second's,
and `dz i j` the second's `avx2Mulcache` at `16 * j + i`. Those positions hold
pair `avx2Layout (32 * j + i) / 2`, whose root `avx2Mulcache` takes negated in
odd blocks, which `pmul0_odd` subtracts back. -/

theorem ζ_pow_congr {m n : ℕ} (h : m % 256 = n % 256) : ζ ^ m = ζ ^ n := by
  rw [← pow_mod_orderOf ζ m, ← pow_mod_orderOf ζ n, orderOf_ζ, h]

theorem avx2_pair_index : ∀ j < 8, ∀ i < 16,
    bitRev 7 (avx2NttOrder (16 * j + i)) < 128 ∧
    avx2Layout (32 * j + i) = 2 * bitRev 7 (avx2NttOrder (16 * j + i)) ∧
    avx2Layout (32 * j + 16 + i) = 2 * bitRev 7 (avx2NttOrder (16 * j + i)) + 1 ∧
    (16 * j + i) / 64 * 128 + 32 * ((16 * j + i) % 64 / 16) + (16 * j + i) % 64 % 16 + 16 =
      32 * j + 16 + i ∧
    (2 * bitreverse7 (64 * ((16 * j + i) / 64) + 2 * ((16 * j + i) % 64 / 32) +
      4 * ((16 * j + i) % 64 % 16)) + 1) % 256 =
      (2 * bitRev 7 (bitRev 7 (avx2NttOrder (16 * j + i))) + 1 + 128 * (j % 2)) % 256 := by
  decide +kernel

/-- `x` holds `X` in the AVX2 layout. -/
def Avx2Holds (x : ℕ → ℤ) (X : Polynomial) : Prop := ∀ p < 256, (x p : Zq) = X[avx2Layout p]!

/-- `avx2_mulcache`, which the x86_64 `mlkem_mulcache_compute` computes, is each
odd coefficient times its pair's root, negated in odd blocks. -/
theorem avx2Mulcache_eq (y : ℕ → ℤ) (Y : Polynomial) (hy : Avx2Holds y Y) (j i : ℕ) (hj : j < 8)
    (hi : i < 16) :
    (avx2Mulcache y (16 * j + i) : Zq) =
      (-1) ^ (j % 2) * (Y[avx2Layout (32 * j + 16 + i)]! *
        ζ ^ (2 * bitRev 7 (avx2Layout (32 * j + i) / 2) + 1)) := by
  obtain ⟨_, h0, _, hs, he⟩ := avx2_pair_index j hj i hi
  simp only [avx2Mulcache]
  rw [cast_rem, hs]
  push_cast
  rw [hy _ (by omega), ζ_eq, ζ_pow_congr he, h0, show ∀ n, 2 * n / 2 = n by omega, pow_add, pow_mul,
    ζ_128]
  ring

theorem pmul0_eq (x y yt : ℕ → ℤ) (X Y : Polynomial) (hx : Avx2Holds x X) (hy : Avx2Holds y Y)
    (j i : ℕ) (hj : j < 8) (hi : i < 16) (hj2 : j % 2 = 0)
    (hyt : (yt (16 * j + i) : Zq) = avx2Mulcache y (16 * j + i)) :
    (pmul0 (x (32 * j + i)) (x (32 * j + 16 + i)) (y (32 * j + i)) (yt (16 * j + i)) : Zq) =
      (MultiplyNTTs X Y)[avx2Layout (32 * j + i)]! := by
  obtain ⟨hu, h0, h1, _, _⟩ := avx2_pair_index j hj i hi
  rw [pmul0]
  push_cast
  rw [hyt, avx2Mulcache_eq y Y hy j i hj hi, hx _ (by omega), hx _ (by omega), hy _ (by omega), h0,
    h1, multiplyNTTs_even _ _ _ hu, hj2, show ∀ n, 2 * n / 2 = n by omega]
  ring

theorem pmul0Odd_eq (x y yt : ℕ → ℤ) (X Y : Polynomial) (hx : Avx2Holds x X) (hy : Avx2Holds y Y)
    (j i : ℕ) (hj : j < 8) (hi : i < 16) (hj2 : j % 2 = 1)
    (hyt : (yt (16 * j + i) : Zq) = avx2Mulcache y (16 * j + i)) :
    (pmul0Odd (x (32 * j + i)) (x (32 * j + 16 + i)) (y (32 * j + i)) (yt (16 * j + i)) : Zq) =
      (MultiplyNTTs X Y)[avx2Layout (32 * j + i)]! := by
  obtain ⟨hu, h0, h1, _, _⟩ := avx2_pair_index j hj i hi
  rw [pmul0Odd]
  push_cast
  rw [hyt, avx2Mulcache_eq y Y hy j i hj hi, hx _ (by omega), hx _ (by omega), hy _ (by omega), h0,
    h1, multiplyNTTs_even _ _ _ hu, hj2, show ∀ n, 2 * n / 2 = n by omega]
  ring

theorem pmul1_eq (x y : ℕ → ℤ) (X Y : Polynomial) (hx : Avx2Holds x X) (hy : Avx2Holds y Y)
    (j i : ℕ) (hj : j < 8) (hi : i < 16) :
    (pmul1 (x (32 * j + i)) (x (32 * j + 16 + i)) (y (32 * j + i)) (y (32 * j + 16 + i)) : Zq) =
      (MultiplyNTTs X Y)[avx2Layout (32 * j + 16 + i)]! := by
  obtain ⟨hu, h0, h1, _, _⟩ := avx2_pair_index j hj i hi
  rw [pmul1]
  push_cast
  rw [hx _ (by omega), hx _ (by omega), hy _ (by omega), hy _ (by omega), h0, h1,
    multiplyNTTs_odd _ _ _ hu]
  ring

/-- `pmulaccred0_k3`, which the x86_64 `mlkem_basemul_k3` computes at position
`32 * j + i` of each even block, is the sum of three `MultiplyNTTs` products'
coefficients there times `2 ^ -16`. -/
theorem pmulaccred0K3_eq (x0 y0 y0t x1 y1 y1t x2 y2 y2t : ℕ → ℤ) (X0 Y0 X1 Y1 X2 Y2 : Polynomial)
    (hx0 : Avx2Holds x0 X0) (hy0 : Avx2Holds y0 Y0) (hx1 : Avx2Holds x1 X1)
    (hy1 : Avx2Holds y1 Y1) (hx2 : Avx2Holds x2 X2) (hy2 : Avx2Holds y2 Y2)
    (j i : ℕ) (hj : j < 8) (hi : i < 16) (hj2 : j % 2 = 0)
    (h0 : (y0t (16 * j + i) : Zq) = avx2Mulcache y0 (16 * j + i))
    (h1 : (y1t (16 * j + i) : Zq) = avx2Mulcache y1 (16 * j + i))
    (h2 : (y2t (16 * j + i) : Zq) = avx2Mulcache y2 (16 * j + i)) :
    2 ^ 16 * (pmulaccred0K3
      (x0 (32 * j + i)) (x0 (32 * j + 16 + i)) (y0 (32 * j + i)) (y0 (32 * j + 16 + i)) (y0t (16 * j + i))
      (x1 (32 * j + i)) (x1 (32 * j + 16 + i)) (y1 (32 * j + i)) (y1 (32 * j + 16 + i)) (y1t (16 * j + i))
      (x2 (32 * j + i)) (x2 (32 * j + 16 + i)) (y2 (32 * j + i)) (y2 (32 * j + 16 + i)) (y2t (16 * j + i))
      : Zq) =
      (MultiplyNTTs X0 Y0)[avx2Layout (32 * j + i)]! + (MultiplyNTTs X1 Y1)[avx2Layout (32 * j + i)]! +
        (MultiplyNTTs X2 Y2)[avx2Layout (32 * j + i)]! := by
  rw [pmulaccred0K3, cast_rem, Int.cast_mul, ← mul_assoc, inverseMod_eq, one_mul, pmulacc0K3,
    Int.cast_add, Int.cast_add, pmul0_eq x0 y0 y0t X0 Y0 hx0 hy0 j i hj hi hj2 h0,
    pmul0_eq x1 y1 y1t X1 Y1 hx1 hy1 j i hj hi hj2 h1, pmul0_eq x2 y2 y2t X2 Y2 hx2 hy2 j i hj hi hj2 h2]

/-- `pmulaccred0_odd_k3`, which the x86_64 `mlkem_basemul_k3` computes at
position `32 * j + i` of each odd block, is the sum of three `MultiplyNTTs`
products' coefficients there times `2 ^ -16`. -/
theorem pmulaccred0OddK3_eq (x0 y0 y0t x1 y1 y1t x2 y2 y2t : ℕ → ℤ) (X0 Y0 X1 Y1 X2 Y2 : Polynomial)
    (hx0 : Avx2Holds x0 X0) (hy0 : Avx2Holds y0 Y0) (hx1 : Avx2Holds x1 X1)
    (hy1 : Avx2Holds y1 Y1) (hx2 : Avx2Holds x2 X2) (hy2 : Avx2Holds y2 Y2)
    (j i : ℕ) (hj : j < 8) (hi : i < 16) (hj2 : j % 2 = 1)
    (h0 : (y0t (16 * j + i) : Zq) = avx2Mulcache y0 (16 * j + i))
    (h1 : (y1t (16 * j + i) : Zq) = avx2Mulcache y1 (16 * j + i))
    (h2 : (y2t (16 * j + i) : Zq) = avx2Mulcache y2 (16 * j + i)) :
    2 ^ 16 * (pmulaccred0OddK3
      (x0 (32 * j + i)) (x0 (32 * j + 16 + i)) (y0 (32 * j + i)) (y0 (32 * j + 16 + i)) (y0t (16 * j + i))
      (x1 (32 * j + i)) (x1 (32 * j + 16 + i)) (y1 (32 * j + i)) (y1 (32 * j + 16 + i)) (y1t (16 * j + i))
      (x2 (32 * j + i)) (x2 (32 * j + 16 + i)) (y2 (32 * j + i)) (y2 (32 * j + 16 + i)) (y2t (16 * j + i))
      : Zq) =
      (MultiplyNTTs X0 Y0)[avx2Layout (32 * j + i)]! + (MultiplyNTTs X1 Y1)[avx2Layout (32 * j + i)]! +
        (MultiplyNTTs X2 Y2)[avx2Layout (32 * j + i)]! := by
  rw [pmulaccred0OddK3, cast_rem, Int.cast_mul, ← mul_assoc, inverseMod_eq, one_mul, pmulacc0OddK3,
    Int.cast_add, Int.cast_add, pmul0Odd_eq x0 y0 y0t X0 Y0 hx0 hy0 j i hj hi hj2 h0,
    pmul0Odd_eq x1 y1 y1t X1 Y1 hx1 hy1 j i hj hi hj2 h1,
    pmul0Odd_eq x2 y2 y2t X2 Y2 hx2 hy2 j i hj hi hj2 h2]

/-- `pmulaccred1_k3`, which the x86_64 `mlkem_basemul_k3` computes at position
`32 * j + 16 + i`, is the sum of three `MultiplyNTTs` products' coefficients
there times `2 ^ -16`. -/
theorem pmulaccred1K3_eq (x0 y0 dz0 x1 y1 dz1 x2 y2 dz2 : ℕ → ℤ) (X0 Y0 X1 Y1 X2 Y2 : Polynomial)
    (hx0 : Avx2Holds x0 X0) (hy0 : Avx2Holds y0 Y0) (hx1 : Avx2Holds x1 X1)
    (hy1 : Avx2Holds y1 Y1) (hx2 : Avx2Holds x2 X2) (hy2 : Avx2Holds y2 Y2)
    (j i : ℕ) (hj : j < 8) (hi : i < 16) :
    2 ^ 16 * (pmulaccred1K3
      (x0 (32 * j + i)) (x0 (32 * j + 16 + i)) (y0 (32 * j + i)) (y0 (32 * j + 16 + i)) (dz0 (16 * j + i))
      (x1 (32 * j + i)) (x1 (32 * j + 16 + i)) (y1 (32 * j + i)) (y1 (32 * j + 16 + i)) (dz1 (16 * j + i))
      (x2 (32 * j + i)) (x2 (32 * j + 16 + i)) (y2 (32 * j + i)) (y2 (32 * j + 16 + i)) (dz2 (16 * j + i))
      : Zq) =
      (MultiplyNTTs X0 Y0)[avx2Layout (32 * j + 16 + i)]! +
        (MultiplyNTTs X1 Y1)[avx2Layout (32 * j + 16 + i)]! +
        (MultiplyNTTs X2 Y2)[avx2Layout (32 * j + 16 + i)]! := by
  rw [pmulaccred1K3, cast_rem, Int.cast_mul, ← mul_assoc, inverseMod_eq, one_mul, pmulacc1K3,
    Int.cast_add, Int.cast_add, pmul1_eq x0 y0 X0 Y0 hx0 hy0 j i hj hi,
    pmul1_eq x1 y1 X1 Y1 hx1 hy1 j i hj hi, pmul1_eq x2 y2 X2 Y2 hx2 hy2 j i hj hi]

end rind.spec.s2n
