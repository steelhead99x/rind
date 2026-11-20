module

public import VerifiedGarbage.TCB.Mem

/-!
# SHA-1 (FIPS 180-4)

**Trusted** (as every file in `Spec/`). The hash function SHA-1, transcribed
from FIPS 180-4, *Secure Hash Standard* (August 2015); section numbers below
refer to it. Messages are sequences of bytes (the standard allows any number
of bits); every multi-byte quantity is big-endian (§3.1).

SHA-1 is broken as a collision-resistant hash function; it is here because
existing protocols and file formats still use it.

The primitives implemented in assembly are the compression function over a
run of whole blocks (`compressBlocks`), and the streaming (incremental)
interface: initialize, absorb message bytes, pad and output the digest, on a
streaming state that `Repr` relates to the message absorbed so far. Their
contracts are in `Spec/Sha1/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.Sha1

/-- A 32-bit word (§2.1). -/
abbrev Word := BitVec 32

/-- The five 32-bit words `H₀ … H₄` of a hash value (§2.2.1), or equally the
working variables `a … e` (§6.1.2). -/
abbrev HashValue := Vector Word 5

/-- A 512-bit message block, as sixteen 32-bit words `M₀ … M₁₅` (§5.2.1). -/
abbrev Block := Fin 16 → Word

/-! ## Functions (§4.1.1) -/

/-- `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)`, for `0 ≤ t ≤ 19` -/
def ch (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)

/-- `Parity(x, y, z) = x ⊕ y ⊕ z`, for `20 ≤ t ≤ 39` and `60 ≤ t ≤ 79` -/
def parity (x y z : Word) : Word := x ^^^ y ^^^ z

/-- `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`, for `40 ≤ t ≤ 59` -/
def maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `fₜ(x, y, z)` -/
def f (t : Nat) (x y z : Word) : Word :=
  if t < 20 then ch x y z
  else if t < 40 then parity x y z
  else if t < 60 then maj x y z
  else parity x y z

/-! ## Constants (§4.2.1) and the initial hash value (§5.3.1) -/

/-- `Kₜ` -/
def K (t : Nat) : Word :=
  if t < 20 then 0x5a827999
  else if t < 40 then 0x6ed9eba1
  else if t < 60 then 0x8f1bbcdc
  else 0xca62c1d6

/-- `H⁽⁰⁾` -/
def H0 : HashValue := #v[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]

/-! ## Preprocessing (§5.1.1, §5.2.1) -/

/-- The big-endian bytes of a word. -/
def wordBytes (x : Word) : List Byte :=
  [x.extractLsb' 24 8, x.extractLsb' 16 8, x.extractLsb' 8 8, x.extractLsb' 0 8]

/-- §5.1.1: append the bit `1`, then the least number of `0` bits that makes
the length `≡ 448 (mod 512)`, then the message length `ℓ` in bits as a 64-bit
big-endian integer. For a message of bytes, the `1` bit and the first seven
`0` bits are the byte `0x80`. (SHA-1 is only defined for `ℓ < 2⁶⁴`.) -/
def pad (m : List Byte) : List Byte :=
  let ℓ : BitVec 64 := BitVec.ofNat 64 (8 * m.length)
  m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++
    ((List.range 8).reverse.map fun i => ℓ.extractLsb' (8 * i) 8)

/-- §5.2.1: the block whose `j`-th word is made of bytes `4j … 4j+3` of
`byte` (big-endian). -/
def parseBlock (byte : Nat → Byte) : Block := fun j =>
  (byte (4 * j) ++ byte (4 * j + 1) ++ byte (4 * j + 2) ++ byte (4 * j + 3) : Word)

/-! ## Hash computation (§6.1.2) -/

/-- Step 1, the message schedule: `Wₜ = Mₜ` for `0 ≤ t ≤ 15`, and
`Wₜ = ROTL¹(Wₜ₋₃ ⊕ Wₜ₋₈ ⊕ Wₜ₋₁₄ ⊕ Wₜ₋₁₆)` for `16 ≤ t ≤ 79`.

`schedule M t` is the list `[Wₜ₋₁, Wₜ₋₂, …, W₀]` (most recent first, so
`Wₜ₋ᵢ` is at index `i - 1`); building it one word at a time keeps evaluation
linear rather than exponential. -/
def schedule (M : Block) : Nat → List Word
  | 0 => []
  | t + 1 =>
    let w := schedule M t
    (if h : t < 16 then M ⟨t, h⟩ else (w[2]! ^^^ w[7]! ^^^ w[13]! ^^^ w[15]!).rotateLeft 1) :: w

/-- `Wₜ` -/
def W (M : Block) (t : Nat) : Word := (schedule M (t + 1)).headD 0

/-- Step 3, one round `t` of the working variables `v = (a, b, c, d, e)`:
`T = ROTL⁵(a) + fₜ(b, c, d) + e + Kₜ + Wₜ`, `e = d`, `d = c`,
`c = ROTL³⁰(b)`, `b = a`, `a = T`. -/
def round (M : Block) (v : HashValue) (t : Nat) : HashValue :=
  let a := v[0]; let b := v[1]; let c := v[2]; let d := v[3]; let e := v[4]
  let T := a.rotateLeft 5 + f t b c d + e + K t + W M t
  #v[T, a, b.rotateLeft 30, c, d]

/-- The working variables after rounds `0 … n-1`, starting from `H` (step 2). -/
def rounds (H : HashValue) (M : Block) (n : Nat) : HashValue :=
  (List.range n).foldl (round M) H

/-- Steps 2–4: the hash value `H⁽ⁱ⁾` computed from `H⁽ⁱ⁻¹⁾` and the block `M⁽ⁱ⁾`. -/
def compress (H : HashValue) (M : Block) : HashValue :=
  Vector.zipWith (· + ·) (rounds H M 80) H

/-- `H` updated with the first `n` 64-byte blocks `M⁽¹⁾ … M⁽ⁿ⁾` of the bytes `p`. -/
def compressList (H : HashValue) (p : List Byte) (n : Nat) : HashValue :=
  (List.range n).foldl (fun H i => compress H (parseBlock fun k => p.getD (64 * i + k) 0)) H

/-- The SHA-1 digest of a message: `H⁽ᴺ⁾` as 20 big-endian bytes. -/
def hash (m : List Byte) : List Byte :=
  let p := pad m
  (compressList H0 p (p.length / 64)).toList.flatMap wordBytes

/-! ## The compression function on memory

These read the arguments of the assembly primitive from memory: a hash value
is stored as five native (little-endian) `u32`s, and message blocks are
consecutive runs of 64 bytes. -/

/-- The hash value stored as `[u32; 5]` at `p`. -/
def stateAt (m : Mem) (p : Addr) : HashValue :=
  Vector.ofFn fun j => m.readW (p + BitVec.ofNat 64 (4 * j)) 32

/-- The 64-byte block at `p`. -/
def blockAt (m : Mem) (p : Addr) : Block := parseBlock fun k => m (p + BitVec.ofNat 64 k)

/-- `H` updated with the `n` consecutive blocks at `p`. -/
def compressBlocks (H : HashValue) (m : Mem) (p : Addr) (n : Nat) : HashValue :=
  (List.range n).foldl (fun H i => compress H (blockAt m (p + BitVec.ofNat 64 (64 * i)))) H

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-! ## Streaming

The streaming primitives hash a message given in pieces. Their state is 84
bytes: the hash value after the message's whole blocks (stored as by
`stateAt`), followed by a 64-byte buffer holding the bytes of the message
after its last whole block. The length of the message is not part of the
state: the caller keeps it (in bytes, modulo 2⁶⁴) and passes it to every
call. (Lengths are public, so it may live anywhere; and `pad` only uses the
length modulo 2⁶⁴ bits, so this suffices even beyond SHA-1's limit of
`ℓ < 2⁶⁴` bits.) -/

/-- The streaming state at `p` (84 bytes) represents the message `m`: its hash
value is `H⁽⁰⁾` updated with the `⌊|m| / 64⌋` whole blocks of `m`, and its
buffer starts with the remaining `|m| mod 64` bytes of `m`. The rest of the
buffer is unspecified. -/
def Repr (mem : Mem) (p : Addr) (m : List Byte) : Prop :=
  stateAt mem p = compressList H0 m (m.length / 64) ∧
  bytesAt mem (p + 20) (m.length % 64) = m.drop (64 * (m.length / 64))

end VG.Spec.Sha1
