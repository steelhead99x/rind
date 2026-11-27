module

public import VerifiedGarbage.TCB.Mem

/-!
# X25519 (RFC 7748)

**Trusted** (as every file in `Spec/`). The Diffie-Hellman function X25519,
transcribed from RFC 7748, *Elliptic Curves for Security* (January 2016);
section numbers below refer to it, and the function names in backquotes to
the Python code of §5. Byte strings are little-endian.

The field `GF(p)` for `p = 2²⁵⁵ - 19` is `Fin p`, whose `+`, `-` and `*`
are modulo `p` (§5: "All calculations are performed in GF(p), i.e., they are
performed modulo p"). An element is the integer in `{0, …, p - 1}` that
represents it (`.val`).

This file is independent of any architecture; the contract of the function
implemented in assembly is in `Spec/X25519/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.X25519

/-- The prime `p = 2²⁵⁵ - 19` (§4.1). -/
def P : Nat := 2 ^ 255 - 19

instance : NeZero P := ⟨by decide⟩

/-- An element of `GF(p)`. -/
abbrev Fe := Fin P

/-- `a24 = (486662 - 2) / 4 = 121665` for curve25519 (§5). -/
def a24 : Fe := 121665

/-- `a ^ e` in `GF(p)`: `e` factors of `a` (`1` if `e = 0`), computed by
square-and-multiply from `a ^ e = (a · a) ^ ⌊e / 2⌋ · a ^ (e mod 2)`. -/
def pow (a : Fe) (e : Nat) : Fe :=
  if e = 0 then 1 else
  let r := pow (a * a) (e / 2)
  if e % 2 = 0 then r else a * r
termination_by e
decreasing_by omega

/-- `decodeLittleEndian(b, 255)`: `Σ b[i] << 8*i` for `i` in
`range((255+7)/8)`, i.e. the first 32 bytes of `b` read as a little-endian
number. -/
def decodeLittleEndian (b : List Byte) : Nat :=
  ((List.range 32).map fun i => (b.getD i 0).toNat <<< (8 * i)).sum

/-- `decodeUCoordinate(u, 255)`: the most significant bit of the last (32nd)
byte masked (`u_list[-1] &= (1<<(255%8))-1`, that is `&= 127`), then read as a
little-endian number. The result is less than `2²⁵⁵`, but not necessarily
less than `p` (§5: "Implementations MUST accept non-canonical values and
process them as if they had been reduced modulo the field prime"). -/
def decodeUCoordinate (u : List Byte) : Nat :=
  decodeLittleEndian (u.set 31 (u.getD 31 0 &&& 127))

/-- `encodeUCoordinate(u, 255)`: `u mod p` as 32 bytes, byte `i` being
`(u >> 8*i) & 0xff`. -/
def encodeUCoordinate (u : Fe) : List Byte :=
  (List.range 32).map fun i => BitVec.ofNat 8 (u.val >>> (8 * i))

/-- `decodeScalar25519(k)`: `k_list[0] &= 248`, `k_list[31] &= 127`,
`k_list[31] |= 64`, then read as a little-endian number. -/
def decodeScalar25519 (k : List Byte) : Nat :=
  let k := k.set 0 (k.getD 0 0 &&& 248)
  let k := k.set 31 ((k.getD 31 0 &&& 127) ||| 64)
  decodeLittleEndian k

/-- `cswap(swap, a, b)`: `(b, a)` if `swap = 1`, else `(a, b)` (§5, which
also describes how to compute it in constant time). -/
def cswap (swap : Nat) (a b : Fe) : Fe × Fe := if swap = 1 then (b, a) else (a, b)

/-- The variables of the Montgomery ladder of §5 between iterations. -/
structure Ladder where
  x2 : Fe
  z2 : Fe
  x3 : Fe
  z3 : Fe
  swap : Nat

/-- One iteration of the loop of §5, for the bit `t` of the scalar `k` and
`x_1 = x1`:
```
k_t = (k >> t) & 1
swap ^= k_t
(x_2, x_3) = cswap(swap, x_2, x_3)
(z_2, z_3) = cswap(swap, z_2, z_3)
swap = k_t
A = x_2 + z_2
AA = A^2
B = x_2 - z_2
BB = B^2
E = AA - BB
C = x_3 + z_3
D = x_3 - z_3
DA = D * A
CB = C * B
x_3 = (DA + CB)^2
z_3 = x_1 * (DA - CB)^2
x_2 = AA * BB
z_2 = E * (AA + a24 * E)
```
-/
def ladderStep (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat) : Ladder :=
  let kt := (k >>> t) &&& 1
  let swap := st.swap ^^^ kt
  let (x2, x3) := cswap swap st.x2 st.x3
  let (z2, z3) := cswap swap st.z2 st.z3
  let swap := kt
  let A := x2 + z2
  let AA := A * A
  let B := x2 - z2
  let BB := B * B
  let E := AA - BB
  let C := x3 + z3
  let D := x3 - z3
  let DA := D * A
  let CB := C * B
  let x3 := (DA + CB) * (DA + CB)
  let z3 := x1 * ((DA - CB) * (DA - CB))
  let x2 := AA * BB
  let z2 := E * (AA + a24 * E)
  { x2, z2, x3, z3, swap }

/-- `X25519(k, u)` (§5), for a 32-byte scalar `k` and u-coordinate `u`:
decode both, then
```
x_1 = u
x_2 = 1
z_2 = 0
x_3 = u
z_3 = 1
swap = 0
For t = bits-1 down to 0:
    … (see `ladderStep`)
(x_2, x_3) = cswap(swap, x_2, x_3)
(z_2, z_3) = cswap(swap, z_2, z_3)
Return x_2 * (z_2^(p - 2))
```
with `bits = 255`, and encode the result as 32 bytes. -/
def x25519 (k u : List Byte) : List Byte :=
  let k := decodeScalar25519 k
  let u : Fe := Fin.ofNat P (decodeUCoordinate u)
  let x1 := u
  let st := (List.range 255).reverse.foldl (ladderStep k x1)
    { x2 := 1, z2 := 0, x3 := u, z3 := 1, swap := 0 }
  let (x2, _) := cswap st.swap st.x2 st.x3
  let (z2, _) := cswap st.swap st.z2 st.z3
  encodeUCoordinate (x2 * pow z2 (P - 2))

/-- The u-coordinate of the base point, 9 (§4.1), encoded as the byte 9
followed by 31 zero bytes (§6.1). -/
def basePoint : List Byte := 9 :: List.replicate 31 0

end VG.Spec.X25519
