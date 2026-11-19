module

public import VerifiedGarbage.TCB.Mem

/-!
# ChaCha20 (RFC 8439)

**Trusted** (as every file in `Spec/`). The stream cipher ChaCha20,
transcribed from RFC 8439, *ChaCha20 and Poly1305 for IETF Protocols* (June
2018); section numbers below refer to it. Every multi-byte quantity is
little-endian (§2.3).

The primitives implemented in assembly are the block function (`block`) on a
state in memory, the XOR of the keystream of such a state into data
(`keystream`), and a streaming cipher (`keystreamOf`, applied in pieces to a
state in memory that represents what is left of it: `keyAt`, `restAt`). This
file is independent of any architecture; the contracts of the primitives on
every target are in `Spec/ChaCha20/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.ChaCha20

/-- A 32-bit word. -/
abbrev Word := BitVec 32

/-- The sixteen 32-bit words of a ChaCha state (§2.2), in the order of the
RFC's 4×4 matrix (row by row). -/
abbrev State := Vector Word 16

/-! ## The quarter round (§2.1, §2.2) -/

/-- §2.1:
```
a += b; d ^= a; d <<<= 16;
c += d; b ^= c; b <<<= 12;
a += b; d ^= a; d <<<= 8;
c += d; b ^= c; b <<<= 7;
```
(`+` is addition modulo 2³², `<<<` rotation towards the high bits.) -/
def quarterRound (a b c d : Word) : Word × Word × Word × Word :=
  let a := a + b; let d := (d ^^^ a).rotateLeft 16
  let c := c + d; let b := (b ^^^ c).rotateLeft 12
  let a := a + b; let d := (d ^^^ a).rotateLeft 8
  let c := c + d; let b := (b ^^^ c).rotateLeft 7
  (a, b, c, d)

/-- §2.2, `QUARTERROUND(x, y, z, w)`: the quarter round on the words of the
state at indices `x, y, z, w`, leaving the others alone. -/
def qround (s : State) (x y z w : Fin 16) : State :=
  let (a, b, c, d) := quarterRound s[x] s[y] s[z] s[w]
  ((((s.set x a).set y b).set z c).set w d)

/-! ## The block function (§2.3) -/

/-- The four constant words `0x61707865, 0x3320646e, 0x79622d32, 0x6b206574`. -/
def constants : Vector Word 4 := #v[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

/-- §2.3.1, `inner_block`: a column round followed by a diagonal round. -/
def innerBlock (s : State) : State :=
  let s := qround s 0 4 8 12
  let s := qround s 1 5 9 13
  let s := qround s 2 6 10 14
  let s := qround s 3 7 11 15
  let s := qround s 0 5 10 15
  let s := qround s 1 6 11 12
  let s := qround s 2 7 8 13
  qround s 3 4 9 14

/-- §2.3: the ChaCha20 block function on a state — 20 rounds (10 iterations
of `innerBlock`), then the original state added word by word (modulo 2³²). -/
def block (s : State) : State :=
  Vector.zipWith (· + ·) (Nat.repeat innerBlock 10 s) s

/-- §2.3: serialize a state by sequencing its words in little-endian order. -/
def serialize (s : State) : List Byte :=
  s.toList.flatMap fun x => [x.extractLsb' 0 8, x.extractLsb' 8 8, x.extractLsb' 16 8, x.extractLsb' 24 8]

/-- Word `j` of a byte string read as little-endian 32-bit integers. -/
def wordLE (bs : List Byte) (j : Nat) : Word :=
  (bs.getD (4 * j + 3) 0 ++ bs.getD (4 * j + 2) 0 ++ bs.getD (4 * j + 1) 0 ++ bs.getD (4 * j) 0 : Word)

/-- §2.3: the initial state from a 256-bit key (32 bytes), a 32-bit block
counter and a 96-bit nonce (12 bytes): the constants (words 0–3), the key
(words 4–11), the counter (word 12) and the nonce (words 13–15). -/
def initState (key : List Byte) (counter : Word) (nonce : List Byte) : State :=
  Vector.ofFn fun i =>
    if i.1 < 4 then constants.getD i.1 0
    else if i.1 < 12 then wordLE key (i.1 - 4)
    else if i.1 = 12 then counter
    else wordLE nonce (i.1 - 13)

/-- §2.3.1, `chacha20_block(key, counter, nonce)`: 64 bytes of keystream. -/
def chacha20Block (key : List Byte) (counter : Word) (nonce : List Byte) : List Byte :=
  serialize (block (initState key counter nonce))

/-! ## Encryption (§2.4) -/

/-- §2.4.1, `chacha20_encrypt(key, counter, nonce, plaintext)`: the plaintext
XORed with the concatenation of the keystream blocks for the counters
`counter, counter + 1, …` (as many as the plaintext needs; the extra
keystream of the last block is discarded). Decryption is the same function. -/
def encrypt (key : List Byte) (counter : Word) (nonce : List Byte) (m : List Byte) : List Byte :=
  let ks := (List.range ((m.length + 63) / 64)).flatMap fun j =>
    chacha20Block key (counter + BitVec.ofNat 32 j) nonce
  List.zipWith (· ^^^ ·) m ks

/-- The whole keystream for the 256-bit key `key` (32 bytes) and the 16-byte
`nonce`: state words 12–15 (§2.3), i.e. the initial 32-bit block counter `c`
(bytes 0–3, little-endian) followed by the 96-bit nonce (bytes 4–15): the
concatenation of `chacha20_block(key, c + j, nonce)` for `j = 0, 1, …`, up to
the last 32-bit block counter, 2³² − 1, since the 32-bit block counter of §2.3
does not go further (the `P_MAX` of §2.8, 2³⁸ − 64 bytes, is this length for
`c = 1`). In terms of §2.4.1's `encrypt`, it is the encryption of the
64 × (2³² − c) zero bytes, and `encrypt` XORs any message that is not longer
with its first bytes. -/
def keystreamOf (key nonce : List Byte) : List Byte :=
  let c := wordLE nonce 0
  (List.range (2 ^ 32 - c.toNat)).flatMap fun j =>
    chacha20Block key (c + BitVec.ofNat 32 j) (nonce.drop 4)

/-! ## The block function on memory

The assembly primitive is the block function on a whole 16-word state
(constants included) read from memory. Building the state from the key,
counter and nonce, XORing the keystream into the data and advancing the
counter are the caller's (Rust's) job. -/

/-- The state stored as `[u32; 16]` at `p`. -/
def stateAt (m : Mem) (p : Addr) : State :=
  Vector.ofFn fun j => m.readW (p + BitVec.ofNat 64 (4 * j)) 32

/-! ## The keystream on memory

A second primitive XORs the keystream of a state in memory into data: the
blocks for the states with word 12, the block counter, advanced by `0, 1, …`
(modulo 2³², as in `encrypt`). -/

/-- The first `n` bytes of the keystream from the state `s`: the serialized
blocks of `s` with the counter (word 12) advanced by `j = 0, 1, …`. -/
def keystream (s : State) (n : Nat) : List Byte :=
  ((List.range ((n + 63) / 64)).flatMap fun j =>
    serialize (block (s.set 12 (s[12] + BitVec.ofNat 32 j)))).take n

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-! ## The streaming state on memory

The streaming functions apply `keystreamOf key nonce` in pieces, keeping
what is left of it in a state in memory (`[u64; 96]`, opaque to the caller):

* bytes 0–63: a 16-word state (`stateAt`): the constants, the key (bytes
  16–47), and the block counter (word 12) and nonce of the next block;
* bytes 64–127: the current block of keystream, whose last bytes are still
  to be used;
* bytes 128–135: the number of bytes of keystream left (`leftAt`), a
  little-endian 64-bit integer;
* bytes 136–767: working space.

The state represents the key `keyAt` and the keystream bytes left `restAt`.
Every state represents some key and keystream: the contracts hold whatever
the state holds, and those of the functions that set it up (`init`,
`set_nonce`) say that it then represents `keystreamOf`. -/

/-- The key of the streaming state at `p`: words 4–11 of its 16-word state,
as bytes (§2.3 reads the key as little-endian words, as memory is). -/
def keyAt (m : Mem) (p : Addr) : List Byte := bytesAt m (p + 16) 32

/-- The number of bytes of keystream left in the streaming state at `p`. -/
def leftAt (m : Mem) (p : Addr) : Nat := (m.readW (p + 128) 64).toNat

/-- The keystream left in the streaming state at `p`, `leftAt m p = n` bytes
long: the last `n % 64` bytes of the block at bytes 64–127, then the first
`64 * (n / 64)` bytes of the keystream of the 16-word state at bytes 0–63
(`keystream`: its blocks for the block counters word 12, word 12 + 1, …). -/
def restAt (m : Mem) (p : Addr) : List Byte :=
  let n := leftAt m p
  bytesAt m (p + BitVec.ofNat 64 (128 - n % 64)) (n % 64) ++ keystream (stateAt m p) (64 * (n / 64))

end VG.Spec.ChaCha20
