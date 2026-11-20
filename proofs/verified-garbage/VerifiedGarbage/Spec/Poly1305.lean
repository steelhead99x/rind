module

public import VerifiedGarbage.TCB.Mem

/-!
# Poly1305 (RFC 8439)

**Trusted** (as every file in `Spec/`). The one-time authenticator Poly1305,
transcribed from RFC 8439, *ChaCha20 and Poly1305 for IETF Protocols* (June
2018); section numbers below refer to it, and the function names in
backquotes to the pseudocode of §2.5.1. Every multi-byte quantity is
little-endian.

This file is independent of any architecture; the contracts of the
primitives on every target are in `Spec/Poly1305/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.Poly1305

/-- `le_bytes_to_num`: a byte string read as a little-endian number. -/
def leNum : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNum bs

/-- `num_to_16_le_bytes` (for `n = 16`): the `n` least significant bytes of
`x`, in little-endian order. -/
def leBytes (n x : Nat) : List Byte :=
  (List.range n).map fun i => BitVec.ofNat 8 (x / 256 ^ i)

/-- `clamp(r)`: `r &= 0x0ffffffc0ffffffc0ffffffc0fffffff` (§2.5, §2.5.1). -/
def clamp (r : Nat) : Nat := r &&& 0x0ffffffc0ffffffc0ffffffc0fffffff

/-- The prime `p = 2¹³⁰ - 5`. -/
def P : Nat := 2 ^ 130 - 5

/-- Block `i` of a message: `msg[(i*16)..(i*16+15)]`, 16 bytes, except that
the last block may be shorter. -/
def block (msg : List Byte) (i : Nat) : List Byte := (msg.drop (16 * i)).take 16

/-- The number of blocks of a message: `ceil(msg length in bytes / 16)`. -/
def numBlocks (msg : List Byte) : Nat := (msg.length + 15) / 16

/-- The accumulator `a` of `poly1305_mac` after the loop over the blocks of
`msg`, with the clamped `r`:
```
a = 0
for i=1 upto ceil(msg length in bytes / 16)
   n = le_bytes_to_num(msg[((i-1)*16)..(i*16)] | [0x01])
   a += n
   a = (r * a) % p
```
(`|` is concatenation: the byte `0x01` is appended to each block.) -/
def accumulate (r : Nat) (msg : List Byte) : Nat :=
  (List.range (numBlocks msg)).foldl (fun a i => (r * (a + leNum (block msg i ++ [0x01]))) % P) 0

/-- §2.5.1, `poly1305_mac(msg, key)`, for a 32-byte one-time key:
```
r = le_bytes_to_num(key[0..15])
clamp(r)
s = le_bytes_to_num(key[16..31])
a = … (see `accumulate`)
a += s
return num_to_16_le_bytes(a)
```
-/
def mac (key msg : List Byte) : List Byte :=
  let r := clamp (leNum (key.take 16))
  let s := leNum ((key.drop 16).take 16)
  leBytes 16 (accumulate r msg + s)

/-! ## Streaming

The primitives on memory MAC a message given in pieces. Their state is 128
bytes (`[u64; 16]`): the accumulator after the message's whole 16-byte blocks
so far (bytes 0–23, a little-endian number), the one-time key (bytes 24–55),
the message's last bytes that do not fill a block (bytes 56–71, `Buffered`),
and working space (the rest). `Repr` is the special case of a message of
whole blocks, whose buffer is empty. -/

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- The state at `p` represents the message `msg` under the one-time key
`key`: `msg` is a whole number of blocks, the key is stored at bytes 24–55,
and the accumulator at bytes 0–23 is `accumulate` of `msg` with the clamped
`r` of the key. The rest of the state is unspecified. -/
def Repr (mem : Mem) (p : Addr) (key msg : List Byte) : Prop :=
  msg.length % 16 = 0 ∧ bytesAt mem (p + 24) 32 = key ∧
    leNum (bytesAt mem p 24) = accumulate (clamp (leNum (key.take 16))) msg

/-- The state at `p` represents the message `msg`, of any length, under the
one-time key `key`: its whole blocks as in `Repr`, and its remaining
`msg.length % 16` bytes stored at bytes 56–71. For a message of whole blocks
this is `Repr` (the buffer is empty). -/
def Buffered (mem : Mem) (p : Addr) (key msg : List Byte) : Prop :=
  Repr mem p key (msg.take (16 * (msg.length / 16))) ∧
    bytesAt mem (p + 56) (msg.length % 16) = msg.drop (16 * (msg.length / 16))

end VG.Spec.Poly1305
