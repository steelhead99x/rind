module

public import VerifiedGarbage.TCB.Mem

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4)

**Trusted** (as every file in `Spec/`). The SHA-512 family of hash functions,
transcribed from FIPS 180-4, *Secure Hash Standard* (August 2015); section
numbers below refer to it. Messages are sequences of bytes (the standard allows
any number of bits); every multi-byte quantity is big-endian (§3.1).

All four functions share the SHA-512 compression function and differ only in
the initial hash value and in how much of the final hash value is output
(§6.4–§6.7). The primitives implemented in assembly are the compression
function over a run of whole blocks (`compressBlocks`), and the streaming
(incremental) interface: initialize with one of the four initial hash values,
absorb message bytes, and pad and output the final hash value, on a streaming
state that `Repr` relates to the message absorbed so far. Nothing here depends
on the target: the contracts of the implementations, on every target, are in
`Spec/Sha512/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.Sha512

/-- A 64-bit word (§2.1). -/
abbrev Word := BitVec 64

/-- The eight 64-bit words `H₀ … H₇` of a hash value (§2.2.1), or equally the
working variables `a … h` (§6.4.2). -/
abbrev HashValue := Vector Word 8

/-- A 1024-bit message block, as sixteen 64-bit words `M₀ … M₁₅` (§5.2.2). -/
abbrev Block := Fin 16 → Word

/-! ## Functions (§4.1.3) -/

/-- `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)` -/
def ch (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)

/-- `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)` -/
def maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ₀(x) = ROTR²⁸(x) ⊕ ROTR³⁴(x) ⊕ ROTR³⁹(x)` -/
def bsig0 (x : Word) : Word := x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39

/-- `Σ₁(x) = ROTR¹⁴(x) ⊕ ROTR¹⁸(x) ⊕ ROTR⁴¹(x)` -/
def bsig1 (x : Word) : Word := x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41

/-- `σ₀(x) = ROTR¹(x) ⊕ ROTR⁸(x) ⊕ SHR⁷(x)` -/
def ssig0 (x : Word) : Word := x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ x >>> 7

/-- `σ₁(x) = ROTR¹⁹(x) ⊕ ROTR⁶¹(x) ⊕ SHR⁶(x)` -/
def ssig1 (x : Word) : Word := x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ x >>> 6

/-! ## Constants (§4.2.3) and initial hash values (§5.3.4–§5.3.6) -/

/-- The eighty constants `K₀ … K₇₉`. -/
def Ks : List Word := [
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

/-- `Kₜ` -/
def K (t : Nat) : Word := Ks.getD t 0

/-- `H⁽⁰⁾` for SHA-384 (§5.3.4). -/
def H0_384 : HashValue :=
  #v[0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
    0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4]

/-- `H⁽⁰⁾` for SHA-512 (§5.3.5). -/
def H0_512 : HashValue :=
  #v[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- `H⁽⁰⁾` for SHA-512/224 (§5.3.6.1). -/
def H0_512_224 : HashValue :=
  #v[0x8c3d37c819544da2, 0x73e1996689dcd4d6, 0x1dfab7ae32ff9c82, 0x679dd514582f9fcf,
    0x0f6d2b697bd44da8, 0x77e36f7304c48942, 0x3f9d85a86a1d36c8, 0x1112e6ad91d692a1]

/-- `H⁽⁰⁾` for SHA-512/256 (§5.3.6.2). -/
def H0_512_256 : HashValue :=
  #v[0x22312194fc2bf72c, 0x9f555fa3c84c64c2, 0x2393b86b6f53b151, 0x963877195940eabd,
    0x96283ee2a88effe3, 0xbe5e1e2553863992, 0x2b0199fc2c85b8aa, 0x0eb72ddc81c52ca2]

/-! ## Preprocessing (§5.1.2, §5.2.2) -/

/-- The big-endian bytes of a word. -/
def wordBytes (x : Word) : List Byte :=
  (List.range 8).reverse.map fun i => x.extractLsb' (8 * i) 8

/-- §5.1.2: append the bit `1`, then the least number of `0` bits that makes
the length `≡ 896 (mod 1024)`, then the message length `ℓ` in bits as a 128-bit
big-endian integer. For a message of bytes, the `1` bit and the first seven
`0` bits are the byte `0x80`. (These functions are only defined for
`ℓ < 2¹²⁸`.) -/
def pad (m : List Byte) : List Byte :=
  let ℓ : BitVec 128 := BitVec.ofNat 128 (8 * m.length)
  m ++ [0x80] ++ List.replicate ((239 - m.length % 128) % 128) 0 ++
    ((List.range 16).reverse.map fun i => ℓ.extractLsb' (8 * i) 8)

/-- §5.2.2: the block whose `j`-th word is made of bytes `8j … 8j+7` of
`byte` (big-endian). -/
def parseBlock (byte : Nat → Byte) : Block := fun j =>
  (byte (8 * j) ++ byte (8 * j + 1) ++ byte (8 * j + 2) ++ byte (8 * j + 3) ++
    byte (8 * j + 4) ++ byte (8 * j + 5) ++ byte (8 * j + 6) ++ byte (8 * j + 7) : Word)

/-! ## Hash computation (§6.4.2) -/

/-- Step 1, the message schedule: `Wₜ = Mₜ` for `0 ≤ t ≤ 15`, and
`Wₜ = σ₁(Wₜ₋₂) + Wₜ₋₇ + σ₀(Wₜ₋₁₅) + Wₜ₋₁₆` for `16 ≤ t ≤ 79`
(`+` is addition modulo 2⁶⁴).

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
  Vector.zipWith (· + ·) (rounds H M 80) H

/-- `H` updated with the first `n` 128-byte blocks `M⁽¹⁾ … M⁽ⁿ⁾` of the bytes `p`. -/
def compressList (H : HashValue) (p : List Byte) (n : Nat) : HashValue :=
  (List.range n).foldl (fun H i => compress H (parseBlock fun k => p.getD (128 * i + k) 0)) H

/-- §6.4: the final hash value `H⁽ᴺ⁾` of a message, starting from `H0`, as
64 big-endian bytes. -/
def finalHash (H0 : HashValue) (m : List Byte) : List Byte :=
  let p := pad m
  (compressList H0 p (p.length / 128)).toList.flatMap wordBytes

/-- The SHA-512 digest (§6.4): all of `H⁽ᴺ⁾`, 64 bytes. -/
def sha512 (m : List Byte) : List Byte := finalHash H0_512 m

/-- The SHA-384 digest (§6.5): the left-most 384 bits of `H⁽ᴺ⁾`, 48 bytes. -/
def sha384 (m : List Byte) : List Byte := (finalHash H0_384 m).take 48

/-- The SHA-512/224 digest (§6.6): the left-most 224 bits of `H⁽ᴺ⁾`, 28 bytes. -/
def sha512_224 (m : List Byte) : List Byte := (finalHash H0_512_224 m).take 28

/-- The SHA-512/256 digest (§6.7): the left-most 256 bits of `H⁽ᴺ⁾`, 32 bytes. -/
def sha512_256 (m : List Byte) : List Byte := (finalHash H0_512_256 m).take 32

/-! ## The compression function on memory

These read the arguments of the assembly primitive from memory: a hash value
is stored as eight little-endian `u64`s, and message blocks are
consecutive runs of 128 bytes. -/

/-- The hash value stored as `[u64; 8]` at `p`. -/
def stateAt (m : Mem) (p : Addr) : HashValue :=
  Vector.ofFn fun j => m.readW (p + BitVec.ofNat 64 (8 * j)) 64

/-- The 128-byte block at `p`. -/
def blockAt (m : Mem) (p : Addr) : Block := parseBlock fun k => m (p + BitVec.ofNat 64 k)

/-- `H` updated with the `n` consecutive blocks at `p`. -/
def compressBlocks (H : HashValue) (m : Mem) (p : Addr) (n : Nat) : HashValue :=
  (List.range n).foldl (fun H i => compress H (blockAt m (p + BitVec.ofNat 64 (128 * i)))) H

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-! ## Streaming

The streaming primitives hash a message given in pieces. Their state is 192
bytes: the hash value after the message's whole blocks (stored as by
`stateAt`), followed by a 128-byte buffer holding the bytes of the message
after its last whole block. The four functions share the state and differ
only in the initial hash value it starts from, and in how much of the final
hash value is output.

The length of the message is not part of the state: the caller keeps it (in
bytes, modulo 2⁶⁴) and passes it to every call. (Lengths are public, so it may
live anywhere.) `pad` needs the length in bits as a 128-bit integer, which
that count determines only for messages of fewer than 2⁶⁴ bytes, so the
contracts are stated for those; FIPS 180-4 allows up to 2¹²⁵ − 1 bytes. -/

/-- The streaming state at `p` (192 bytes) represents the message `m`, hashed
from the initial hash value `iv`: its hash value is `iv` updated with the
`⌊|m| / 128⌋` whole blocks of `m`, and its buffer starts with the remaining
`|m| mod 128` bytes of `m`. The rest of the buffer is unspecified. -/
def Repr (iv : HashValue) (mem : Mem) (p : Addr) (m : List Byte) : Prop :=
  stateAt mem p = compressList iv m (m.length / 128) ∧
  bytesAt mem (p + 64) (m.length % 128) = m.drop (128 * (m.length / 128))

end VG.Spec.Sha512
