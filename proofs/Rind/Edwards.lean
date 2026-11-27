/-
SPDX-License-Identifier: MIT

MIT License

Copyright (c) 2026 The Beneficial AI Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The group law of the twisted Edwards curve `-x² + y² = 1 + d x² y²`

From the Beneficial AI Foundation's `DalekSim/Edwards.lean`, MIT licensed, at
https://github.com/Beneficial-AI-Foundation/ref-impl-simulation/blob/b02b07f8e613b129a9da18962d6a9c57252a1f09/shared/dalek/lean/DalekSim/Edwards.lean,
without its edwards25519 section, which `Rind.Ed25519Group` replaces.

Affine points `(x, y)` on the curve with `a = -1`, and the unified addition
`(x₁, y₁) + (x₂, y₂) = ((x₁ y₂ + y₁ x₂) / (1 + t), (y₁ y₂ + x₁ x₂) / (1 - t))`
with `t = d x₁ x₂ y₁ y₂`. Over a field with `2 ≠ 0`, `-1` a square and `d` not
a square, the denominators `1 ± t` are not 0 for two points on the curve
(`one_add_ne_zero`, `one_sub_ne_zero`): Bernstein and Lange's completeness
theorem, which Bernstein, Birkner, Joye, Lange, and Peters extend to a square
`a`. So the sum of two points on the curve is on the curve, and the points
form a commutative group (`Point`).

Associativity is direct: substitute the inner sums, multiply out the
denominators, and write the result as a combination of the three curve
equations, whose cofactors Singular found and `linear_combination` checks.
-/

namespace rind.edwards
/-! ## Polynomial identities

These hold in every commutative ring. `hᵢ` is the curve equation of the point `(xᵢ, yᵢ)`. -/

section Core

variable {R : Type*} [CommRing R]

/-- Closure, with the denominators multiplied out: `(x₁ y₂ + y₁ x₂) / (1 + t)` and
`(y₁ y₂ + x₁ x₂) / (1 - t)` satisfy the curve equation. -/
theorem closure_core (d x1 y1 x2 y2 : R)
    (h1 : -x1 ^ 2 + y1 ^ 2 = 1 + d * x1 ^ 2 * y1 ^ 2)
    (h2 : -x2 ^ 2 + y2 ^ 2 = 1 + d * x2 ^ 2 * y2 ^ 2) :
    -(x1 * y2 + y1 * x2) ^ 2 * (1 - d * x1 * x2 * y1 * y2) ^ 2 +
      (y1 * y2 + x1 * x2) ^ 2 * (1 + d * x1 * x2 * y1 * y2) ^ 2 =
    (1 + d * x1 * x2 * y1 * y2) ^ 2 * (1 - d * x1 * x2 * y1 * y2) ^ 2 +
      d * (x1 * y2 + y1 * x2) ^ 2 * (y1 * y2 + x1 * x2) ^ 2 := by
  linear_combination (x1^2*x2^4*y1^2*d+x1^2*y1^2*y2^4*d+2*x1^2*x2^2*y1^2*d-2*x1^2*y1^2*y2^2*d
    +2*x1^2*x2^2*y1^2-2*x1^2*y1^2*y2^2+x1^2*y1^2*d-x1^2*x2^2+2*x1^2*y1^2+x2^2*y1^2+x1^2*y2^2
    -y1^2*y2^2-x1^2+y1^2+1) * h1 + (x1^4*x2^2*y1^4*y2^2*d^3-x1^4*x2^2*y1^4*d^2+x1^4*y1^4*y2^2*d^2
    -x1^4*y1^4*d^2-x1^4*x2^2*y1^2*d-2*x1^4*y1^4*d+x1^2*x2^2*y1^4*d+x1^4*y1^2*y2^2*d
    -x1^2*y1^4*y2^2*d-2*x1^4*y1^2+2*x1^2*y1^4-2*x1^2*y1^2*d+x1^4-4*x1^2*y1^2+y1^4) * h2

/-- Associativity of the x-coordinate, with the denominators multiplied out. The left side is
`A B`, the right side is `C E`, where `(P + Q) + R` has the x-coordinate `A / E` and
`P + (Q + R)` has the x-coordinate `C / B`. -/
theorem assoc_x_core (d x1 y1 x2 y2 x3 y3 : R)
    (h1 : -x1 ^ 2 + y1 ^ 2 = 1 + d * x1 ^ 2 * y1 ^ 2)
    (h2 : -x2 ^ 2 + y2 ^ 2 = 1 + d * x2 ^ 2 * y2 ^ 2)
    (h3 : -x3 ^ 2 + y3 ^ 2 = 1 + d * x3 ^ 2 * y3 ^ 2) :
    ((x1 * y2 + y1 * x2) * y3 * (1 - d * x1 * x2 * y1 * y2) +
        (y1 * y2 + x1 * x2) * x3 * (1 + d * x1 * x2 * y1 * y2)) *
      ((1 + d * x2 * x3 * y2 * y3) * (1 - d * x2 * x3 * y2 * y3) +
        d * x1 * y1 * (x2 * y3 + y2 * x3) * (y2 * y3 + x2 * x3)) =
    (x1 * (y2 * y3 + x2 * x3) * (1 + d * x2 * x3 * y2 * y3) +
        y1 * (x2 * y3 + y2 * x3) * (1 - d * x2 * x3 * y2 * y3)) *
      ((1 + d * x1 * x2 * y1 * y2) * (1 - d * x1 * x2 * y1 * y2) +
        d * x3 * y3 * (x1 * y2 + y1 * x2) * (y1 * y2 + x1 * x2)) := by
  linear_combination (x1*x2^2*x3^2*y2*y3*d-x2*x3^2*y1*y2^2*y3*d-x2^2*x3*y1*y2*y3^2*d
    +x1*x2*x3*y2^2*y3^2*d+x1*x2^3*x3^3+x2^2*x3^3*y1*y2-x1*x2*x3^3*y2^2-x3^3*y1*y2^3+x2^3*x3^2*y1*y3
    +x1*x2^2*x3^2*y2*y3-x2*x3^2*y1*y2^2*y3-x1*x3^2*y2^3*y3-x1*x2^3*x3*y3^2-x2^2*x3*y1*y2*y3^2
    +x1*x2*x3*y2^2*y3^2+x3*y1*y2^3*y3^2-x2^3*y1*y3^3-x1*x2^2*y2*y3^3+x2*y1*y2^2*y3^3+x1*y2^3*y3^3
    +x1*x2^3*x3+x1*x2*x3^3+x2^2*x3*y1*y2+x3^3*y1*y2-x1*x2*x3*y2^2-x3*y1*y2^3+x2^3*y1*y3
    +x2*x3^2*y1*y3+x1*x2^2*y2*y3+x1*x3^2*y2*y3-x2*y1*y2^2*y3-x1*y2^3*y3-x1*x2*x3*y3^2-x3*y1*y2*y3^2
    -x2*y1*y3^3-x1*y2*y3^3+x1*x2*x3+x3*y1*y2+x2*y1*y3+x1*y2*y3) * h1 + (
    -x1^3*x2^2*x3^2*y1^2*y2*y3*d^2+x1^2*x2*x3^2*y1^3*y2^2*y3*d^2+x1^2*x2^2*x3*y1^3*y2*y3^2*d^2
    -x1^3*x2*x3*y1^2*y2^2*y3^2*d^2-x1^3*x2*x3^3*y1^2*d-x1^2*x2^2*x3^3*y1*y2*d-x1^2*x3^3*y1^3*y2*d
    -x1*x2*x3^3*y1^2*y2^2*d-x1^2*x2*x3^2*y1^3*y3*d-x1^3*x3^2*y1^2*y2*y3*d+x1*x2^2*x3^2*y1^2*y2*y3*d
    +x1^2*x2*x3^2*y1*y2^2*y3*d+x1^3*x2*x3*y1^2*y3^2*d+x1^2*x2^2*x3*y1*y2*y3^2*d
    +x1^2*x3*y1^3*y2*y3^2*d+x1*x2*x3*y1^2*y2^2*y3^2*d+x1^2*x2*y1^3*y3^3*d+x1^3*y1^2*y2*y3^3*d
    -x1*x2^2*y1^2*y2*y3^3*d-x1^2*x2*y1*y2^2*y3^3*d-x1^3*x2*x3*y1^2*d-x1^2*x2^2*x3*y1*y2*d
    -x1^2*x3*y1^3*y2*d-x1*x2*x3*y1^2*y2^2*d-x1^2*x2*y1^3*y3*d-x1^3*y1^2*y2*y3*d
    +x1*x2^2*y1^2*y2*y3*d+x1^2*x2*y1*y2^2*y3*d-x1^3*x2*x3^3+x1*x2*x3^3*y1^2-x1^2*x3^3*y1*y2
    +x3^3*y1^3*y2-x1^2*x2*x3^2*y1*y3+x2*x3^2*y1^3*y3-x1^3*x3^2*y2*y3+x1*x3^2*y1^2*y2*y3
    +x1^3*x2*x3*y3^2-x1*x2*x3*y1^2*y3^2+x1^2*x3*y1*y2*y3^2-x3*y1^3*y2*y3^2+x1^2*x2*y1*y3^3
    -x2*y1^3*y3^3+x1^3*y2*y3^3-x1*y1^2*y2*y3^3-x1^3*x2*x3-x1*x2*x3^3+x1*x2*x3*y1^2-x1^2*x3*y1*y2
    -x3^3*y1*y2+x3*y1^3*y2-x1^2*x2*y1*y3-x2*x3^2*y1*y3+x2*y1^3*y3-x1^3*y2*y3-x1*x3^2*y2*y3
    +x1*y1^2*y2*y3+x1*x2*x3*y3^2+x3*y1*y2*y3^2+x2*y1*y3^3+x1*y2*y3^3-x1*x2*x3-x3*y1*y2-x2*y1*y3
    -x1*y2*y3) * h2 + (x1^2*x2^4*x3*y1*y2^3*d^2+x1*x2^3*x3*y1^2*y2^4*d^2-x1*x2^4*y1^2*y2^3*y3*d^2
    -x1^2*x2^3*y1*y2^4*y3*d^2+x1^2*x2^4*x3*y1*y2*d+x1^3*x2^3*x3*y2^2*d-x2^2*x3*y1^3*y2^3*d
    -x1*x2*x3*y1^2*y2^4*d-x1*x2^4*y1^2*y2*y3*d-x2^3*y1^3*y2^2*y3*d+x1^3*x2^2*y2^3*y3*d
    +x1^2*x2*y1*y2^4*y3*d+x1*x2^3*x3*y2^2*d+x2^2*x3*y1*y2^3*d+x2^3*y1*y2^2*y3*d
    +x1*x2^2*y2^3*y3*d) * h3

/-- Associativity of the y-coordinate, with the denominators multiplied out. The left side is
`A' B'`, the right side is `C' E'`, where `(P + Q) + R` has the y-coordinate `A' / E'` and
`P + (Q + R)` has the y-coordinate `C' / B'`. -/
theorem assoc_y_core (d x1 y1 x2 y2 x3 y3 : R)
    (h1 : -x1 ^ 2 + y1 ^ 2 = 1 + d * x1 ^ 2 * y1 ^ 2)
    (h2 : -x2 ^ 2 + y2 ^ 2 = 1 + d * x2 ^ 2 * y2 ^ 2)
    (h3 : -x3 ^ 2 + y3 ^ 2 = 1 + d * x3 ^ 2 * y3 ^ 2) :
    ((y1 * y2 + x1 * x2) * y3 * (1 + d * x1 * x2 * y1 * y2) +
        (x1 * y2 + y1 * x2) * x3 * (1 - d * x1 * x2 * y1 * y2)) *
      ((1 + d * x2 * x3 * y2 * y3) * (1 - d * x2 * x3 * y2 * y3) -
        d * x1 * y1 * (x2 * y3 + y2 * x3) * (y2 * y3 + x2 * x3)) =
    (y1 * (y2 * y3 + x2 * x3) * (1 + d * x2 * x3 * y2 * y3) +
        x1 * (x2 * y3 + y2 * x3) * (1 - d * x2 * x3 * y2 * y3)) *
      ((1 + d * x1 * x2 * y1 * y2) * (1 - d * x1 * x2 * y1 * y2) -
        d * x3 * y3 * (x1 * y2 + y1 * x2) * (y1 * y2 + x1 * x2)) := by
  linear_combination (x2^2*x3^2*y1*y2*y3*d-x1*x2*x3^2*y2^2*y3*d-x1*x2^2*x3*y2*y3^2*d
    +x2*x3*y1*y2^2*y3^2*d+x2^3*x3^3*y1+x1*x2^2*x3^3*y2-x2*x3^3*y1*y2^2-x1*x3^3*y2^3+x1*x2^3*x3^2*y3
    +x2^2*x3^2*y1*y2*y3-x1*x2*x3^2*y2^2*y3-x3^2*y1*y2^3*y3-x2^3*x3*y1*y3^2-x1*x2^2*x3*y2*y3^2
    +x2*x3*y1*y2^2*y3^2+x1*x3*y2^3*y3^2-x1*x2^3*y3^3-x2^2*y1*y2*y3^3+x1*x2*y2^2*y3^3+y1*y2^3*y3^3
    +x2^3*x3*y1+x2*x3^3*y1+x1*x2^2*x3*y2+x1*x3^3*y2-x2*x3*y1*y2^2-x1*x3*y2^3+x1*x2^3*y3
    +x1*x2*x3^2*y3+x2^2*y1*y2*y3+x3^2*y1*y2*y3-x1*x2*y2^2*y3-y1*y2^3*y3-x2*x3*y1*y3^2-x1*x3*y2*y3^2
    -x1*x2*y3^3-y1*y2*y3^3+x2*x3*y1+x1*x3*y2+x1*x2*y3+y1*y2*y3) * h1 + (
    -x1^2*x2^2*x3^2*y1^3*y2*y3*d^2+x1^3*x2*x3^2*y1^2*y2^2*y3*d^2+x1^3*x2^2*x3*y1^2*y2*y3^2*d^2
    -x1^2*x2*x3*y1^3*y2^2*y3^2*d^2-x1^2*x2*x3^3*y1^3*d-x1^3*x3^3*y1^2*y2*d+x1*x2^2*x3^3*y1^2*y2*d
    +x1^2*x2*x3^3*y1*y2^2*d-x1^3*x2*x3^2*y1^2*y3*d-x1^2*x2^2*x3^2*y1*y2*y3*d-x1^2*x3^2*y1^3*y2*y3*d
    -x1*x2*x3^2*y1^2*y2^2*y3*d+x1^2*x2*x3*y1^3*y3^2*d+x1^3*x3*y1^2*y2*y3^2*d
    -x1*x2^2*x3*y1^2*y2*y3^2*d-x1^2*x2*x3*y1*y2^2*y3^2*d+x1^3*x2*y1^2*y3^3*d+x1^2*x2^2*y1*y2*y3^3*d
    +x1^2*y1^3*y2*y3^3*d+x1*x2*y1^2*y2^2*y3^3*d-x1^2*x2*x3*y1^3*d-x1^3*x3*y1^2*y2*d
    +x1*x2^2*x3*y1^2*y2*d+x1^2*x2*x3*y1*y2^2*d-x1^3*x2*y1^2*y3*d-x1^2*x2^2*y1*y2*y3*d
    -x1^2*y1^3*y2*y3*d-x1*x2*y1^2*y2^2*y3*d-x1^2*x2*x3^3*y1+x2*x3^3*y1^3-x1^3*x3^3*y2
    +x1*x3^3*y1^2*y2-x1^3*x2*x3^2*y3+x1*x2*x3^2*y1^2*y3-x1^2*x3^2*y1*y2*y3+x3^2*y1^3*y2*y3
    +x1^2*x2*x3*y1*y3^2-x2*x3*y1^3*y3^2+x1^3*x3*y2*y3^2-x1*x3*y1^2*y2*y3^2+x1^3*x2*y3^3
    -x1*x2*y1^2*y3^3+x1^2*y1*y2*y3^3-y1^3*y2*y3^3-x1^2*x2*x3*y1-x2*x3^3*y1+x2*x3*y1^3-x1^3*x3*y2
    -x1*x3^3*y2+x1*x3*y1^2*y2-x1^3*x2*y3-x1*x2*x3^2*y3+x1*x2*y1^2*y3-x1^2*y1*y2*y3-x3^2*y1*y2*y3
    +y1^3*y2*y3+x2*x3*y1*y3^2+x1*x3*y2*y3^2+x1*x2*y3^3+y1*y2*y3^3-x2*x3*y1-x1*x3*y2-x1*x2*y3
    -y1*y2*y3) * h2 + (-x1*x2^4*x3*y1^2*y2^3*d^2-x1^2*x2^3*x3*y1*y2^4*d^2+x1^2*x2^4*y1*y2^3*y3*d^2
    +x1*x2^3*y1^2*y2^4*y3*d^2-x1*x2^4*x3*y1^2*y2*d-x2^3*x3*y1^3*y2^2*d+x1^3*x2^2*x3*y2^3*d
    +x1^2*x2*x3*y1*y2^4*d+x1^2*x2^4*y1*y2*y3*d+x1^3*x2^3*y2^2*y3*d-x2^2*y1^3*y2^3*y3*d
    -x1*x2*y1^2*y2^4*y3*d+x2^3*x3*y1*y2^2*d+x1*x2^2*x3*y2^3*d+x1*x2^3*y2^2*y3*d
    +x2^2*y1*y2^3*y3*d) * h3

end Core

/-! ## Affine points and addition -/

variable {F : Type*} [Field F]

/-- `P` is on the curve `-x² + y² = 1 + d x² y²`. -/
def OnCurve (d : F) (P : F × F) : Prop := -P.1 ^ 2 + P.2 ^ 2 = 1 + d * P.1 ^ 2 * P.2 ^ 2

/-- The unified addition formula with `a = -1`. -/
def add (d : F) (P Q : F × F) : F × F :=
  ((P.1 * Q.2 + P.2 * Q.1) / (1 + d * P.1 * Q.1 * P.2 * Q.2),
   (P.2 * Q.2 + P.1 * Q.1) / (1 - d * P.1 * Q.1 * P.2 * Q.2))

/-- Sufficient conditions for the unified addition with `a = -1` to be complete: `2 ≠ 0`, `-1`
is a square and `d` is not a square. -/
class Complete (d : F) : Prop where
  two_ne_zero : (2 : F) ≠ 0
  neg_one_square : IsSquare (-1 : F)
  not_square : ¬IsSquare d

/-! ## Completeness -/

section Completeness

variable {d : F}

/-- Completeness: `(d x₁ x₂ y₁ y₂)² ≠ 1` for two points on the curve. -/
theorem sq_ne_one [hc : Complete d] {x1 y1 x2 y2 : F} (h1 : OnCurve d (x1, y1))
    (h2 : OnCurve d (x2, y2)) :
    (d * x1 * x2 * y1 * y2) ^ 2 ≠ 1 := by
  intro ht
  simp only [OnCurve] at h1 h2
  obtain ⟨i, hi⟩ := hc.neg_one_square
  have hne : d * x1 * x2 * y1 * y2 ≠ 0 := by
    intro h0; rw [h0] at ht; simp at ht
  have hx1 : x1 ≠ 0 := by rintro rfl; simp at hne
  have hy1 : y1 ≠ 0 := by rintro rfl; simp at hne
  have hx2 : x2 ≠ 0 := by rintro rfl; simp at hne
  -- With `t = d x₁ x₂ y₁ y₂`: `(i x₁ ± t y₁)² = d (x₁ y₁)² (i x₂ ± y₂)²`.
  have eP : (i * x1 + d * x1 * x2 * y1 * y2 * y1) ^ 2 =
      d * (x1 * y1) ^ 2 * (i * x2 + y2) ^ 2 := by
    linear_combination h1 - d * x1 ^ 2 * y1 ^ 2 * h2 -
      (x1 ^ 2 - d * x1 ^ 2 * y1 ^ 2 * x2 ^ 2) * hi + (y1 ^ 2 - 1) * ht
  have eM : (i * x1 - d * x1 * x2 * y1 * y2 * y1) ^ 2 =
      d * (x1 * y1) ^ 2 * (i * x2 - y2) ^ 2 := by
    linear_combination h1 - d * x1 ^ 2 * y1 ^ 2 * h2 -
      (x1 ^ 2 - d * x1 ^ 2 * y1 ^ 2 * x2 ^ 2) * hi + (y1 ^ 2 - 1) * ht
  -- If `i x₂ ± y₂ ≠ 0`, then `d` is a square.
  have sq : ∀ u v : F, v ≠ 0 → u ^ 2 = d * (x1 * y1) ^ 2 * v ^ 2 → False := by
    intro u v hv huv
    refine hc.not_square ⟨u / (x1 * y1 * v), ?_⟩
    field_simp
    linear_combination -huv
  by_cases hp : i * x2 + y2 = 0
  · by_cases hm : i * x2 - y2 = 0
    · have hi0 : i ≠ 0 := by
        rintro rfl; simp at hi
      have : 2 * i * x2 = 0 := by linear_combination hp + hm
      simp [hc.two_ne_zero, hi0, hx2] at this
    · exact sq _ _ hm eM
  · exact sq _ _ hp eP

/-- `1 + d x₁ x₂ y₁ y₂ ≠ 0` for two points on the curve. -/
theorem one_add_ne_zero [Complete d] {x1 y1 x2 y2 : F} (h1 : OnCurve d (x1, y1))
    (h2 : OnCurve d (x2, y2)) : 1 + d * x1 * x2 * y1 * y2 ≠ 0 := by
  intro h
  exact sq_ne_one h1 h2 (by linear_combination (d * x1 * x2 * y1 * y2 - 1) * h)

/-- `1 - d x₁ x₂ y₁ y₂ ≠ 0` for two points on the curve. -/
theorem one_sub_ne_zero [Complete d] {x1 y1 x2 y2 : F} (h1 : OnCurve d (x1, y1))
    (h2 : OnCurve d (x2, y2)) : 1 - d * x1 * x2 * y1 * y2 ≠ 0 := by
  intro h
  exact sq_ne_one h1 h2 (by linear_combination (-1 - d * x1 * x2 * y1 * y2) * h)

end Completeness

/-! ## The group law -/

section GroupLaw

variable {d : F}

/-- If `b ≠ 0`, `e ≠ 0` and the curve equation holds for `(a / b, c / e)` with the denominators
multiplied out, then `(a / b, c / e)` is on the curve. -/
theorem onCurve_div {a b c e : F} (hb : b ≠ 0) (he : e ≠ 0)
    (h : -a ^ 2 * e ^ 2 + c ^ 2 * b ^ 2 = b ^ 2 * e ^ 2 + d * a ^ 2 * c ^ 2) :
    OnCurve d (a / b, c / e) := by
  simp only [OnCurve]
  field_simp
  linear_combination h

/-- Closure: the sum of two points on the curve is on the curve. -/
theorem add_onCurve [Complete d] {P Q : F × F} (hP : OnCurve d P) (hQ : OnCurve d Q) :
    OnCurve d (add d P Q) := by
  obtain ⟨x1, y1⟩ := P
  obtain ⟨x2, y2⟩ := Q
  refine onCurve_div (one_add_ne_zero hP hQ) (one_sub_ne_zero hP hQ) ?_
  simp only [OnCurve] at hP hQ
  linear_combination closure_core d x1 y1 x2 y2 hP hQ

/-- The addition is commutative, for all `P` and `Q`, with no curve hypothesis. -/
theorem add_comm' (P Q : F × F) : add d P Q = add d Q P := by
  simp only [add]; ring_nf

/-- `(0, 1)` is a right identity, for all `P`, with no curve hypothesis. -/
theorem add_zero' (P : F × F) : add d P (0, 1) = P := by
  simp [add]

/-- `(-x, y)` is the inverse of a point `(x, y)` on the curve. -/
theorem add_neg' [Complete d] {P : F × F} (hP : OnCurve d P) :
    add d P (-P.1, P.2) = (0, 1) := by
  obtain ⟨x, y⟩ := P
  have hm := one_sub_ne_zero hP (show OnCurve d (-x, y) by simpa [OnCurve] using hP)
  simp only [OnCurve] at hP
  simp only [add, Prod.mk.injEq]
  refine ⟨by ring, ?_⟩
  rw [div_eq_one_iff_eq hm]
  linear_combination hP

/-- `n / (b e) / (m / (b e)) = n / m`, the step that removes the inner denominators. -/
private theorem div_div_cancel {b e n m : F} (hb : b ≠ 0) (he : e ≠ 0) :
    n / (b * e) / (m / (b * e)) = n / m :=
  div_div_div_cancel_right₀ (mul_ne_zero hb he) n m

/-- Associativity of the unified addition on the curve. -/
theorem add_assoc' [Complete d] {P Q R : F × F} (hP : OnCurve d P) (hQ : OnCurve d Q)
    (hR : OnCurve d R) : add d (add d P Q) R = add d P (add d Q R) := by
  have hPQ := add_onCurve hP hQ
  have hQR := add_onCurve hQ hR
  have a1 := one_add_ne_zero hPQ hR
  have a2 := one_sub_ne_zero hPQ hR
  have b1 := one_add_ne_zero hP hQR
  have b2 := one_sub_ne_zero hP hQR
  obtain ⟨x1, y1⟩ := P
  obtain ⟨x2, y2⟩ := Q
  obtain ⟨x3, y3⟩ := R
  have p1 := one_add_ne_zero hP hQ
  have p2 := one_sub_ne_zero hP hQ
  have q1 := one_add_ne_zero hQ hR
  have q2 := one_sub_ne_zero hQ hR
  simp only [OnCurve] at hP hQ hR
  have cx := assoc_x_core d x1 y1 x2 y2 x3 y3 hP hQ hR
  have cy := assoc_y_core d x1 y1 x2 y2 x3 y3 hP hQ hR
  simp only [add] at a1 a2 b1 b2 ⊢
  -- Names for the inner sums `P + Q = (a / b, c / e)` and `Q + R = (f / g, k / l)`.
  generalize ha : x1 * y2 + y1 * x2 = a at *
  generalize hb : 1 + d * x1 * x2 * y1 * y2 = b at *
  generalize hc : y1 * y2 + x1 * x2 = c at *
  generalize he : 1 - d * x1 * x2 * y1 * y2 = e at *
  generalize hf : x2 * y3 + y2 * x3 = f at *
  generalize hg : 1 + d * x2 * x3 * y2 * y3 = g at *
  generalize hk : y2 * y3 + x2 * x3 = k at *
  generalize hl : 1 - d * x2 * x3 * y2 * y3 = l at *
  -- Each coordinate is a quotient of two polynomials.
  have ex1 : a / b * y3 + c / e * x3 = (a * y3 * e + c * x3 * b) / (b * e) := by
    field_simp
  have dx1 : 1 + d * (a / b) * x3 * (c / e) * y3 = (b * e + d * x3 * y3 * a * c) / (b * e) := by
    field_simp
  have ex2 : x1 * (k / l) + y1 * (f / g) = (x1 * k * g + y1 * f * l) / (g * l) := by
    field_simp
  have dx2 : 1 + d * x1 * (f / g) * y1 * (k / l) = (g * l + d * x1 * y1 * f * k) / (g * l) := by
    field_simp
  have ey1 : c / e * y3 + a / b * x3 = (c * y3 * b + a * x3 * e) / (b * e) := by
    field_simp
  have dy1 : 1 - d * (a / b) * x3 * (c / e) * y3 = (b * e - d * x3 * y3 * a * c) / (b * e) := by
    field_simp
  have ey2 : y1 * (k / l) + x1 * (f / g) = (y1 * k * g + x1 * f * l) / (g * l) := by
    field_simp
  have dy2 : 1 - d * x1 * (f / g) * y1 * (k / l) = (g * l - d * x1 * y1 * f * k) / (g * l) := by
    field_simp
  rw [dx1] at a1
  rw [dy1] at a2
  rw [dx2] at b1
  rw [dy2] at b2
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [ex1, dx1, ex2, dx2, div_div_cancel p1 p2, div_div_cancel q1 q2,
      div_eq_div_iff (div_ne_zero_iff.mp a1).1 (div_ne_zero_iff.mp b1).1]
    exact cx
  · dsimp only
    rw [ey1, dy1, ey2, dy2, div_div_cancel p1 p2, div_div_cancel q1 q2,
      div_eq_div_iff (div_ne_zero_iff.mp a2).1 (div_ne_zero_iff.mp b2).1]
    exact cy

end GroupLaw

/-! ## The group of points -/

section Point

variable (d : F)

/-- The points of the curve. -/
def Point : Type _ := {P : F × F // OnCurve d P}

variable {d}

namespace Point

@[ext] theorem ext {P Q : Point d} (h : P.1 = Q.1) : P = Q := Subtype.ext h

instance : Zero (Point d) := ⟨⟨(0, 1), by simp [OnCurve]⟩⟩
instance : Neg (Point d) := ⟨fun P => ⟨(-P.1.1, P.1.2), by simpa [OnCurve] using P.2⟩⟩

@[simp] theorem val_zero : (0 : Point d).1 = (0, 1) := rfl
@[simp] theorem val_neg (P : Point d) : (-P).1 = (-P.1.1, P.1.2) := rfl

variable [Complete d]

instance : Add (Point d) := ⟨fun P Q => ⟨add d P.1 Q.1, add_onCurve P.2 Q.2⟩⟩

@[simp] theorem val_add (P Q : Point d) : (P + Q).1 = add d P.1 Q.1 := rfl

/-- The points form a commutative group, with the identity `(0, 1)` and the negation
`(x, y) ↦ (-x, y)`. -/
instance : AddCommGroup (Point d) where
  add_assoc P Q R := Point.ext (add_assoc' P.2 Q.2 R.2)
  zero_add P := Point.ext (by simp only [val_add, val_zero]; rw [add_comm', add_zero'])
  add_zero P := Point.ext (add_zero' P.1)
  add_comm P Q := Point.ext (add_comm' P.1 Q.1)
  neg_add_cancel P := Point.ext (by
    simp only [val_add, val_neg, val_zero]; rw [add_comm']; exact add_neg' P.2)
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The step of a ladder: `(n + 1) • P` is `n • P` plus `P` by the addition formula. -/
theorem val_succ_nsmul (n : ℕ) (P : Point d) : ((n + 1) • P).1 = add d (n • P).1 P.1 := by
  rw [succ_nsmul]; rfl

/-- `(2 n) • P` is the double of `n • P`. -/
theorem val_two_mul_nsmul (n : ℕ) (P : Point d) :
    ((2 * n) • P).1 = add d (n • P).1 (n • P).1 := by
  rw [two_mul, add_nsmul]; rfl

/-- `(2 n + 1) • P = (n + 1) • P + n • P`, by the addition formula. A ladder proof uses this
with the invariant that its two registers differ by `P`. -/
theorem val_two_mul_add_one_nsmul (n : ℕ) (P : Point d) :
    ((2 * n + 1) • P).1 = add d ((n + 1) • P).1 (n • P).1 := by
  rw [show 2 * n + 1 = (n + 1) + n by ring, add_nsmul]; rfl

end Point

end Point

end rind.edwards
