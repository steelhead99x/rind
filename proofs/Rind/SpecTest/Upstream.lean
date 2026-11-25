import Rind.Ed25519
import Rind.Pratt
import Rind.SpecTest.Nist

/-!
# Stand-ins for the opaque constants

`rfcx25519`, `edPow`, and `edMul` are opaque: under the composition rule
each stands for HOL Light's definition, and nothing is assumed of it, so no
executable twin can be proven equal to one. The spec tests run the specs
around them with these transliterations of the upstream definitions in their
place, which checks those specs, such as Ed25519's hashing and encodings, and
not the constants: HOL Light's `rfcx25519` as RFC 7748 section 5 computes it,
and `edwards25519_group`'s `group_mul` as `edwards_add`, with `group_pow` by
doubling and adding.
-/

namespace rind.spec.upstream

/-- RFC 7748 section 5's X25519, as numbers: the scalar clamped, the
u-coordinate's top bit masked, the Montgomery ladder, and the result's
affine u-coordinate below p. -/
def x25519 (k u : Nat) : Nat :=
  let p := p25519
  let k := k % 2 ^ 255 / 8 * 8 ||| 2 ^ 254
  let x1 := u % 2 ^ 255 % p
  let rec ladder : Nat → Nat × Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat × Nat
    | 0, s => s
    | t + 1, (x2, z2, x3, z3, swap) =>
      let kt := k / 2 ^ t % 2
      let sw := swap ^^^ kt
      let (x2, x3) := if sw = 1 then (x3, x2) else (x2, x3)
      let (z2, z3) := if sw = 1 then (z3, z2) else (z2, z3)
      let A := (x2 + z2) % p
      let AA := A * A % p
      let B := (x2 + p - z2) % p
      let BB := B * B % p
      let E := (AA + p - BB) % p
      let C := (x3 + z3) % p
      let D := (x3 + p - z3) % p
      let DA := D * A % p
      let CB := C * B % p
      let x3 := (DA + CB) % p * ((DA + CB) % p) % p
      let z3 := x1 * ((DA + p - CB) % p * ((DA + p - CB) % p) % p) % p
      let x2 := AA * BB % p
      let z2 := E * ((AA + 121665 * E) % p) % p
      ladder t (x2, z2, x3, z3, kt)
  let (x2, z2, x3, z3, swap) := ladder 255 (1, 0, x1, 1, 0)
  let (x2, _) := if swap = 1 then (x3, x2) else (x2, x3)
  let (z2, _) := if swap = 1 then (z3, z2) else (z2, z3)
  x2 * powMod p 256 z2 (p - 2) % p

/-- `edwards_add` on `edwards25519_group`: `group_mul`. -/
def edMul (P Q : EdPoint) : EdPoint :=
  let p := p25519
  let x1 := P.1.toNat % p; let y1 := P.2.toNat % p
  let x2 := Q.1.toNat % p; let y2 := Q.2.toNat % p
  let t := d25519 * x1 % p * x2 % p * y1 % p * y2 % p
  let x3 := (x1 * y2 + y1 * x2) % p * nist.invC p ((1 + t) % p) % p
  let y3 := (y1 * y2 + x1 * x2) % p * nist.invC p ((1 + p - t) % p) % p
  ((x3 : Int), (y3 : Int))

/-- `group_pow` on `edwards25519_group`, by doubling and adding. -/
def edPow (P : EdPoint) (n : Nat) : EdPoint :=
  if n = 0 then (0, 1)
  else
    let h := edPow P (n / 2)
    let d := edMul h h
    if n % 2 = 0 then d else edMul P d
termination_by n
decreasing_by omega

end rind.spec.upstream
