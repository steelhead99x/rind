module

public import VerifiedGarbage.TCB.Mem

/-!
# SHA-224 and SHA-256 (FIPS 180-4)

**Trusted** (as every file in `Spec/`). The hash functions SHA-224 and
SHA-256, transcribed from FIPS 180-4, *Secure Hash Standard* (August 2015);
section numbers below refer to it. Messages are sequences of bytes (the
standard allows any number of bits); every multi-byte quantity is big-endian
(§3.1).

Both functions share the SHA-256 compression function and differ only in the
initial hash value and in how much of the final hash value is output (§6.2,
§6.3). The primitives implemented in assembly are the compression function
over a run of whole blocks (`compressBlocks`), and the streaming
(incremental) interface: initialize with either initial hash value, absorb
message bytes, and pad and output the final hash value, on a streaming state
that `ReprFrom` relates to the message absorbed so far. Their contracts,
which say how the code's arguments and memory relate to these definitions,
are in `Spec/Sha256/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.Sha256

/-- A 32-bit word (§2.1). -/
abbrev Word := BitVec 32

/-- The eight 32-bit words `H₀ … H₇` of a hash value (§2.2.1), or equally the
working variables `a … h` (§6.2.2). -/
abbrev HashValue := Vector Word 8

/-- A 512-bit message block, as sixteen 32-bit words `M₀ … M₁₅` (§5.2.1). -/
abbrev Block := Fin 16 → Word

/-! ## Functions (§4.1.2) -/

/-- `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)` -/
def ch (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)

/-- `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)` -/
def maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ₀(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)` -/
def bsig0 (x : Word) : Word := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- `Σ₁(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)` -/
def bsig1 (x : Word) : Word := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- `σ₀(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)` -/
def ssig0 (x : Word) : Word := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> 3

/-- `σ₁(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)` -/
def ssig1 (x : Word) : Word := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> 10

/-! ## Constants (§4.2.2) and initial hash values (§5.3.2, §5.3.3) -/

/-- The sixty-four constants `K₀ … K₆₃`. -/
def Ks : List Word := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- `Kₜ` -/
def K (t : Nat) : Word := Ks.getD t 0

/-- `H⁽⁰⁾` for SHA-256 (§5.3.3). -/
def H0 : HashValue :=
  #v[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- `H⁽⁰⁾` for SHA-224 (§5.3.2). -/
def H0_224 : HashValue :=
  #v[0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939, 0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4]

/-! ## Preprocessing (§5.1.1, §5.2.1) -/

/-- The big-endian bytes of a word. -/
def wordBytes (x : Word) : List Byte :=
  [x.extractLsb' 24 8, x.extractLsb' 16 8, x.extractLsb' 8 8, x.extractLsb' 0 8]

/-- §5.1.1: append the bit `1`, then the least number of `0` bits that makes
the length `≡ 448 (mod 512)`, then the message length `ℓ` in bits as a 64-bit
big-endian integer. For a message of bytes, the `1` bit and the first seven
`0` bits are the byte `0x80`. (SHA-224 and SHA-256 are only defined for
`ℓ < 2⁶⁴`.) -/
def pad (m : List Byte) : List Byte :=
  let ℓ : BitVec 64 := BitVec.ofNat 64 (8 * m.length)
  m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++
    ((List.range 8).reverse.map fun i => ℓ.extractLsb' (8 * i) 8)

/-- §5.2.1: the block whose `j`-th word is made of bytes `4j … 4j+3` of
`byte` (big-endian). -/
def parseBlock (byte : Nat → Byte) : Block := fun j =>
  (byte (4 * j) ++ byte (4 * j + 1) ++ byte (4 * j + 2) ++ byte (4 * j + 3) : Word)

/-! ## Hash computation (§6.2.2) -/

/-- Step 1, the message schedule: `Wₜ = Mₜ` for `0 ≤ t ≤ 15`, and
`Wₜ = σ₁(Wₜ₋₂) + Wₜ₋₇ + σ₀(Wₜ₋₁₅) + Wₜ₋₁₆` for `16 ≤ t ≤ 63`
(`+` is addition modulo 2³²).

`schedule M t` is the list `[Wₜ₋₁, Wₜ₋₂, …, W₀]` (most recent first, so
`Wₜ₋ᵢ` is at index `i - 1`); building it one word at a time keeps evaluation
linear rather than exponential. -/
def schedule (M : Block) : Nat → List Word
  | 0 => []
  | t + 1 =>
    let w := schedule M t
    (if h : t < 16 then M ⟨t, h⟩ else ssig1 w[1]! + w[6]! + ssig0 w[14]! + w[15]!) :: w

/-- `Wₜ` -/
def W (M : Block) (t : Nat) : Word := (schedule M (t + 1)).headD 0

/-- Step 3, one round `t` of the working variables `v = (a, b, c, d, e, f, g, h)`. -/
def round (M : Block) (v : HashValue) (t : Nat) : HashValue :=
  let a := v[0]; let b := v[1]; let c := v[2]; let d := v[3]
  let e := v[4]; let f := v[5]; let g := v[6]; let h := v[7]
  let T₁ := h + bsig1 e + ch e f g + K t + W M t
  let T₂ := bsig0 a + maj a b c
  #v[T₁ + T₂, a, b, c, d + T₁, e, f, g]

/-- The working variables after rounds `0 … n-1`, starting from `H` (step 2). -/
def rounds (H : HashValue) (M : Block) (n : Nat) : HashValue :=
  (List.range n).foldl (round M) H

/-- Steps 2–4: the hash value `H⁽ⁱ⁾` computed from `H⁽ⁱ⁻¹⁾` and the block `M⁽ⁱ⁾`. -/
def compress (H : HashValue) (M : Block) : HashValue :=
  Vector.zipWith (· + ·) (rounds H M 64) H

/-- `H` updated with the first `n` 64-byte blocks `M⁽¹⁾ … M⁽ⁿ⁾` of the bytes `p`. -/
def compressList (H : HashValue) (p : List Byte) (n : Nat) : HashValue :=
  (List.range n).foldl (fun H i => compress H (parseBlock fun k => p.getD (64 * i + k) 0)) H

/-- §6.2: the final hash value `H⁽ᴺ⁾` of a message, starting from `iv`, as
32 big-endian bytes. -/
def finalHash (iv : HashValue) (m : List Byte) : List Byte :=
  let p := pad m
  (compressList iv p (p.length / 64)).toList.flatMap wordBytes

/-- The SHA-256 digest (§6.2): all of `H⁽ᴺ⁾`, 32 bytes. -/
def hash (m : List Byte) : List Byte := finalHash H0 m

/-- The SHA-224 digest (§6.3): the left-most 224 bits of `H⁽ᴺ⁾`, 28 bytes. -/
def sha224 (m : List Byte) : List Byte := (finalHash H0_224 m).take 28

/-! ## The compression function on memory

These read the arguments of the assembly primitive from memory: a hash value
is stored as eight native (little-endian) `u32`s, and message blocks are
consecutive runs of 64 bytes. -/

/-- The hash value stored as `[u32; 8]` at `p`. -/
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

The streaming primitives hash a message given in pieces. Their state is 96
bytes: the hash value after the message's whole blocks (stored as by
`stateAt`), followed by a 64-byte buffer holding the bytes of the message
after its last whole block. SHA-224 and SHA-256 share the state and differ
only in the initial hash value it starts from, and in how much of the final
hash value is output.

The length of the message is not part of the state: the caller keeps it (in
bytes, modulo 2⁶⁴) and passes it to every call. (Lengths are public, so it
may live anywhere; and `pad` only uses the length modulo 2⁶⁴ bits, so this
suffices even beyond the limit of `ℓ < 2⁶⁴` bits.) -/

/-- The streaming state at `p` (96 bytes) represents the message `m`, hashed
from the initial hash value `iv`: its hash value is `iv` updated with the
`⌊|m| / 64⌋` whole blocks of `m`, and its buffer starts with the remaining
`|m| mod 64` bytes of `m`. The rest of the buffer is unspecified. -/
def ReprFrom (iv : HashValue) (mem : Mem) (p : Addr) (m : List Byte) : Prop :=
  stateAt mem p = compressList iv m (m.length / 64) ∧
  bytesAt mem (p + 32) (m.length % 64) = m.drop (64 * (m.length / 64))

/-- The streaming state at `p` represents the message `m`, hashed by SHA-256
(from `H0`). -/
def Repr (mem : Mem) (p : Addr) (m : List Byte) : Prop := ReprFrom H0 mem p m

end VG.Spec.Sha256
