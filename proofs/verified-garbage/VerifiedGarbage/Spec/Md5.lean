module

public import VerifiedGarbage.TCB.Mem

/-!
# MD5 (RFC 1321)

**Trusted** (as every file in `Spec/`). The MD5 message-digest algorithm,
transcribed from RFC 1321, *The MD5 Message-Digest Algorithm* (April 1992);
section numbers below refer to it. Messages are sequences of bytes (the RFC
allows any number of bits). Unlike SHA-1 and SHA-2, every multi-byte
quantity is little-endian: "a sequence of bytes can be interpreted as a
sequence of 32-bit words, where each consecutive group of four bytes is
interpreted as a word with the low-order (least significant) byte given
first" (§2).

MD5 is broken as a collision-resistant hash function; it is here because
existing protocols and file formats still use it.

The primitives implemented in assembly are the compression function over a
run of whole blocks (`compressBlocks`), and the streaming (incremental)
interface: initialize, absorb message bytes, pad and output the digest, on a
streaming state that `Repr` relates to the message absorbed so far. Their
contracts are in `Spec/Md5/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.Md5

/-- A 32-bit word (§2). -/
abbrev Word := BitVec 32

/-- The four words `A, B, C, D` of the MD buffer (§3.3). -/
abbrev HashValue := Vector Word 4

/-- A 512-bit block of the message, as sixteen 32-bit words `X[0] … X[15]`
(§3.4). -/
abbrev Block := Fin 16 → Word

/-! ## Auxiliary functions (§3.4) -/

/-- `F(X,Y,Z) = XY v not(X) Z` -/
def F (x y z : Word) : Word := (x &&& y) ||| (~~~x &&& z)

/-- `G(X,Y,Z) = XZ v Y not(Z)` -/
def G (x y z : Word) : Word := (x &&& z) ||| (y &&& ~~~z)

/-- `H(X,Y,Z) = X xor Y xor Z` -/
def H (x y z : Word) : Word := x ^^^ y ^^^ z

/-- `I(X,Y,Z) = Y xor (X v not(Z))` -/
def I (x y z : Word) : Word := y ^^^ (x ||| ~~~z)

/-! ## Constants (§3.3, §3.4) -/

/-- The table `T[1 … 64]`: `T[i]` is the integer part of `4294967296 *
abs(sin(i))`, `i` in radians. The values are those of the reference
implementation in Appendix A.3 of the RFC. -/
def Ts : List Word := [
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

/-- For each of the 64 operations `[abcd k s i]` of §3.4, in order, the index
`k` of the word `X[k]` it adds. -/
def ks : List Nat := [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  1, 6, 11, 0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12,
  5, 8, 11, 14, 1, 4, 7, 10, 13, 0, 3, 6, 9, 12, 15, 2,
  0, 7, 14, 5, 12, 3, 10, 1, 8, 15, 6, 13, 4, 11, 2, 9]

/-- For each of the four rounds of §3.4, the rotation amounts `s` of its
operations, which repeat every four operations. -/
def ss : List (List Nat) := [[7, 12, 17, 22], [5, 9, 14, 20], [4, 11, 16, 23], [6, 10, 15, 21]]

/-- The MD buffer's initial value (§3.3): word A is `01 23 45 67` in
little-endian byte order, and so on. -/
def H0 : HashValue := #v[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476]

/-! ## Preprocessing (§3.1, §3.2) -/

/-- The little-endian bytes of a word (§3.5). -/
def wordBytes (x : Word) : List Byte :=
  [x.extractLsb' 0 8, x.extractLsb' 8 8, x.extractLsb' 16 8, x.extractLsb' 24 8]

/-- §3.1–§3.2: append the bit `1`, then the least number of `0` bits that
makes the length `≡ 448 (mod 512)`, then the low-order 64 bits of the
message length `b` in bits, as a little-endian 64-bit integer. For a message
of bytes, the `1` bit and the first seven `0` bits are the byte `0x80`. (MD5
is defined for any length: only `b mod 2⁶⁴` is used.) -/
def pad (m : List Byte) : List Byte :=
  let b : BitVec 64 := BitVec.ofNat 64 (8 * m.length)
  m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++
    ((List.range 8).map fun i => b.extractLsb' (8 * i) 8)

/-- §2: the block whose `j`-th word is made of bytes `4j … 4j+3` of `byte`,
low-order byte first. -/
def parseBlock (byte : Nat → Byte) : Block := fun j =>
  (byte (4 * j + 3) ++ byte (4 * j + 2) ++ byte (4 * j + 1) ++ byte (4 * j) : Word)

/-! ## Processing a block (§3.4) -/

/-- The auxiliary function of round `r` (0-based). -/
def roundFn (r : Nat) : Word → Word → Word → Word :=
  match r with
  | 0 => F
  | 1 => G
  | 2 => H
  | _ => I

/-- Operation `t` (0-based, so the RFC's `i` is `t + 1`) of §3.4,
`a = b + ((a + fn(b,c,d) + X[k] + T[i]) <<< s)`, on `v = (a, b, c, d)`.

The RFC names the operands of successive operations `[ABCD …]`, `[DABC …]`,
`[CDAB …]`, `[BCDA …]`: the word just computed becomes the `b` of the next
operation, and the old `d, b, c` its `a, c, d`. So the result here is
`(d, a', b, c)`, and after a multiple of four operations the words are back
in the order `A, B, C, D`. -/
def step (X : Block) (v : HashValue) (t : Nat) : HashValue :=
  let a := v[0]; let b := v[1]; let c := v[2]; let d := v[3]
  let r := t / 16
  let k := ks.getD t 0
  let s := (ss.getD r []).getD (t % 4) 0
  let a' := b + (a + roundFn r b c d + (if h : k < 16 then X ⟨k, h⟩ else 0) +
    Ts.getD t 0).rotateLeft s
  #v[d, a', b, c]

/-- The MD buffer after operations `0 … n-1`, starting from `v`. -/
def steps (v : HashValue) (X : Block) (n : Nat) : HashValue :=
  (List.range n).foldl (step X) v

/-- §3.4: the four rounds of one block, then `A = A + AA` and so on. -/
def compress (v : HashValue) (X : Block) : HashValue :=
  Vector.zipWith (· + ·) (steps v X 64) v

/-- `v` updated with the first `n` 64-byte blocks of the bytes `p`. -/
def compressList (v : HashValue) (p : List Byte) (n : Nat) : HashValue :=
  (List.range n).foldl (fun v i => compress v (parseBlock fun k => p.getD (64 * i + k) 0)) v

/-- The MD5 digest of a message (§3.5): `A, B, C, D`, each low-order byte
first, 16 bytes. -/
def hash (m : List Byte) : List Byte :=
  let p := pad m
  (compressList H0 p (p.length / 64)).toList.flatMap wordBytes

/-! ## The compression function on memory

These read the arguments of the assembly primitive from memory: the MD
buffer is stored as four native (little-endian) `u32`s, and message blocks
are consecutive runs of 64 bytes. -/

/-- The MD buffer stored as `[u32; 4]` at `p`. -/
def stateAt (m : Mem) (p : Addr) : HashValue :=
  Vector.ofFn fun j => m.readW (p + BitVec.ofNat 64 (4 * j)) 32

/-- The 64-byte block at `p`. -/
def blockAt (m : Mem) (p : Addr) : Block := parseBlock fun k => m (p + BitVec.ofNat 64 k)

/-- `v` updated with the `n` consecutive blocks at `p`. -/
def compressBlocks (v : HashValue) (m : Mem) (p : Addr) (n : Nat) : HashValue :=
  (List.range n).foldl (fun v i => compress v (blockAt m (p + BitVec.ofNat 64 (64 * i)))) v

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-! ## Streaming

The streaming primitives hash a message given in pieces. Their state is 80
bytes: the MD buffer after the message's whole blocks (stored as by
`stateAt`), followed by a 64-byte buffer holding the bytes of the message
after its last whole block. The length of the message is not part of the
state: the caller keeps it (in bytes, modulo 2⁶⁴) and passes it to every
call. (Lengths are public, so it may live anywhere; and `pad` only uses the
length modulo 2⁶⁴ bits, which that count determines.) -/

/-- The streaming state at `p` (80 bytes) represents the message `m`: its MD
buffer is `H0` updated with the `⌊|m| / 64⌋` whole blocks of `m`, and its
buffer starts with the remaining `|m| mod 64` bytes of `m`. The rest of the
buffer is unspecified. -/
def Repr (mem : Mem) (p : Addr) (m : List Byte) : Prop :=
  stateAt mem p = compressList H0 m (m.length / 64) ∧
  bytesAt mem (p + 16) (m.length % 64) = m.drop (64 * (m.length / 64))

end VG.Spec.Md5
