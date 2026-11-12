-- Vendored from SymCrypt (https://github.com/microsoft/SymCrypt), `SymCRust/lean/Spec/Round.lean` at
-- c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be.
-- Copyright (c) Microsoft Corporation. MIT License:
-- https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/LICENSE.txt
-- Changed: nothing.
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Rat.Floor

/-!
# Rounding to nearest integer

`⌈ x ⌋` denotes `⌊x + 1/2⌋` (rounding to nearest integer, ties go up).
Used by ML-KEM (Compress/Decompress, FIPS 203 Eq. 4.7–4.8) and FrodoKEM.
-/

namespace Aeneas

def rat_round (x : ℚ) : Int := ⌊x + 1/2⌋
notation:max "⌈ " x " ⌋" => rat_round x

private theorem Nat.rat_round_div (x y : ℕ) (hy : y ≠ 0) :
    ⌈ (x : ℚ) / (y : ℚ) ⌋ = (2 * x + y) / (2 * y) := by
  simp only [rat_round]
  have : (x : ℚ) / y + 1 / 2 = ((2 * x + y : ℕ) : ℚ) / ((2 * y : ℕ) : ℚ) := by
    simp; ring_nf; simp [*]; ring_nf
  rw [this]
  rw [Rat.floor_natCast_div_natCast]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

end Aeneas
