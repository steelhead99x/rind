module

public import VerifiedGarbage.TCB.X86_64.State

/-!
# x86-64 SSE instructions

**Trusted.** The legacy SSE instructions of the x86-64 model in
`TCB/X86_64/Isa.lean` that write only an SSE register (SSE2, SSSE3, SHA,
AES-NI and PCLMULQDQ), with the SHA-1, SHA-256 and AES functions their SDM
pseudocode uses.
-/

@[expose] public section

namespace VG.X86_64

/-- Two-operand SSE instructions `op xmm1, xmm2` (register forms only). -/
inductive XBinOp
  | movdqa | paddd | pxor | por | punpckldq | punpckhdq | punpcklqdq | punpckhqdq
  | pshufb | sha256msg1 | sha256msg2 | sha1msg1 | sha1msg2 | sha1nexte
  | pand | pandn | paddq | psubq | pmuludq
  | paddw | psubw | psubd | pmullw | pmulhw | packssdw | punpcklwd | punpckhwd
  | pmaddwd | pmulhrsw | pcmpgtw | packsswb
  | aesenc | aesenclast | aesdec | aesdeclast | aesimc
  | pcmpeqd
  deriving DecidableEq, Repr

/-- SSE2 shifts by an immediate count: of each word (`psllw`, `psrlw`,
`psraw`), of each doubleword (`pslld`, `psrld`, `psrad`), of each quadword
(`psllq`, `psrlq`), or of the whole register by bytes (`pslldq`,
`psrldq`). -/
inductive XShiftOp | pslld | psrld | psllq | psrlq | pslldq | psrldq | psllw | psrlw | psraw | psrad
  deriving DecidableEq, Repr

/-- SSE instructions that write only an SSE register. -/
inductive XOp
  /-- `op xmm1, xmm2` -/
  | bin (op : XBinOp) (dst src : XReg)
  /-- `op xmm1, imm8` -/
  | shift (op : XShiftOp) (dst : XReg) (count : BitVec 8)
  /-- `pshufd xmm1, xmm2, imm8` -/
  | pshufd (dst src : XReg) (order : BitVec 8)
  /-- `palignr xmm1, xmm2, imm8` -/
  | palignr (dst src : XReg) (shift : BitVec 8)
  /-- `pblendw xmm1, xmm2, imm8` (`66 0F 3A 0E /r ib`, SSE4_1) -/
  | pblendw (dst src : XReg) (sel : BitVec 8)
  /-- `sha256rnds2 xmm1, xmm2, xmm0` (`xmm0` is implicit in the encoding) -/
  | sha256rnds2 (dst src : XReg)
  /-- `sha1rnds4 xmm1, xmm2, imm8` -/
  | sha1rnds4 (dst src : XReg) (func : BitVec 8)
  /-- `movq xmm, r64` (`66 REX.W 0F 6E /r`) -/
  | movq (dst : XReg) (src : Reg)
  /-- `aeskeygenassist xmm1, xmm2, imm8` -/
  | aeskeygenassist (dst src : XReg) (rcon : BitVec 8)
  /-- `pclmulqdq xmm1, xmm2, imm8` -/
  | pclmulqdq (dst src : XReg) (sel : BitVec 8)
  deriving DecidableEq, Repr

/-! ### SSE

The SDM's pseudocode numbers bits from the least significant: doubleword `i`
of a 128-bit operand is bits `32i+31:32i`, quadword `i` bits `64i+63:64i`. -/

/-- Doubleword `i` of `x`: bits `32i+31:32i`. -/
def dword (x : BitVec 128) (i : Nat) : BitVec 32 := x.extractLsb' (32 * i) 32

/-- Quadword `i` of `x`: bits `64i+63:64i`. -/
def qword (x : BitVec 128) (i : Nat) : BitVec 64 := x.extractLsb' (64 * i) 64

/-- The 128-bit value with doublewords `d0` (bits 31:0), `d1`, `d2`, `d3` (bits 127:96). -/
def ofDwords (d0 d1 d2 d3 : BitVec 32) : BitVec 128 := d3 ++ d2 ++ d1 ++ d0

/-- Word `i` of `x`: bits `16i+15:16i`. -/
def word (x : BitVec 128) (i : Nat) : BitVec 16 := x.extractLsb' (16 * i) 16

/-- The 128-bit value whose word `i` (bits `16i+15:16i`) is `f i`. -/
def ofWords (f : Nat → BitVec 16) : BitVec 128 :=
  f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0

/-- The signed product of two words (SDM Vol. 2, "PMULLW" and "PMULHW":
`TEMP0[31:0] := DEST[15:0] * SRC[15:0]`, "signed multiply"). -/
def mulWordsSigned (a b : BitVec 16) : BitVec 32 := a.signExtend 32 * b.signExtend 32

/-- SDM Vol. 2, "PACKSSDW", `SaturateSignedDwordToSignedWord`: the
doubleword as a signed word, `7FFFH` if it is greater than 32767 and `8000H`
if it is less than -32768. -/
def satSignedWord (x : BitVec 32) : BitVec 16 :=
  if 32767 < x.toInt then 0x7fff else if x.toInt < -32768 then 0x8000 else x.setWidth 16

/-- SDM Vol. 2, "PACKSSWB", `SaturateSignedWordToSignedByte`: the word as a
signed byte, `7FH` if it is greater than 127 and `80H` if it is less than
-128. -/
def satSignedByte (x : BitVec 16) : BitVec 8 :=
  if 127 < x.toInt then 0x7f else if x.toInt < -128 then 0x80 else x.setWidth 8

/-- Byte `i` of `x`: bits `8i+7:8i`. -/
def byte (x : BitVec 128) (i : Nat) : BitVec 8 := x.extractLsb' (8 * i) 8

/-- The 128-bit value whose byte `i` (bits `8i+7:8i`) is `f i`. -/
def ofBytes (f : Nat → BitVec 8) : BitVec 128 :=
  f 15 ++ f 14 ++ f 13 ++ f 12 ++ f 11 ++ f 10 ++ f 9 ++ f 8 ++
    f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0

/-! The SHA-256 functions used, but not defined, by the SDM's pseudocode for
the SHA extensions: those of the SHA-256 standard, FIPS 180-4 §4.1.2, where
`ROTRⁿ` is a 32-bit rotate right and `SHRⁿ` a logical shift right. -/

/-- `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)` -/
def sha256Ch (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (~~~x &&& z)

/-- `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)` -/
def sha256Maj (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ0(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)` -/
def sha256BigSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- `Σ1(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)` -/
def sha256BigSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- `σ0(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)` -/
def sha256Sigma0 (x : BitVec 32) : BitVec 32 := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> 3

/-- `σ1(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)` -/
def sha256Sigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> 10

/-- SDM Vol. 2, "SHA256MSG2": `W14 := SRC2[95:64]; W15 := SRC2[127:96];
W16 := SRC1[31:0] + σ1(W14); W17 := SRC1[63:32] + σ1(W15); W18 :=
SRC1[95:64] + σ1(W16); W19 := SRC1[127:96] + σ1(W17); DEST[127:96] := W19;
DEST[95:64] := W18; DEST[63:32] := W17; DEST[31:0] := W16`. -/
def sha256Msg2 (src1 src2 : BitVec 128) : BitVec 128 :=
  let w14 := dword src2 2
  let w15 := dword src2 3
  let w16 := dword src1 0 + sha256Sigma1 w14
  let w17 := dword src1 1 + sha256Sigma1 w15
  let w18 := dword src1 2 + sha256Sigma1 w16
  let w19 := dword src1 3 + sha256Sigma1 w17
  ofDwords w16 w17 w18 w19

/-! The SHA-1 functions and constants used, but not defined, by the SDM's
pseudocode for SHA1RNDS4, which selects the function `f()` and constant `K`
of one of the four groups of 20 rounds by `imm8[1:0]` (`f0()` and `K0` for
rounds 0–19, …, `f3()` and `K3` for rounds 60–79): those of the SHA-1
standard, FIPS 180-4 §4.1.1 and §4.2.1. -/

/-- `fᵢ(x, y, z)` for group `i < 4` of 20 rounds, FIPS 180-4 §4.1.1:
`Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)` for group 0, `Parity(x, y, z) = x ⊕ y ⊕ z`
for groups 1 and 3, and `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)` for
group 2. -/
def sha1F (i : Nat) (x y z : BitVec 32) : BitVec 32 :=
  match i with
  | 0 => (x &&& y) ^^^ (~~~x &&& z)
  | 1 => x ^^^ y ^^^ z
  | 2 => (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
  | _ => x ^^^ y ^^^ z

/-- `Kᵢ` for group `i < 4` of 20 rounds, FIPS 180-4 §4.2.1: `5a827999`,
`6ed9eba1`, `8f1bbcdc`, `ca62c1d6`. -/
def sha1K (i : Nat) : BitVec 32 :=
  match i with
  | 0 => 0x5a827999
  | 1 => 0x6ed9eba1
  | 2 => 0x8f1bbcdc
  | _ => 0xca62c1d6

/-- SDM Vol. 2, "SHA1MSG2": `W13 := SRC2[95:64]; W14 := SRC2[63:32]; W15 :=
SRC2[31:0]; W16 := (SRC1[127:96] XOR W13) ROL 1; W17 := (SRC1[95:64] XOR
W14) ROL 1; W18 := (SRC1[63:32] XOR W15) ROL 1; W19 := (SRC1[31:0] XOR W16)
ROL 1; DEST[127:96] := W16; DEST[95:64] := W17; DEST[63:32] := W18;
DEST[31:0] := W19`. -/
def sha1Msg2 (src1 src2 : BitVec 128) : BitVec 128 :=
  let w13 := dword src2 2
  let w14 := dword src2 1
  let w15 := dword src2 0
  let w16 := (dword src1 3 ^^^ w13).rotateLeft 1
  let w17 := (dword src1 2 ^^^ w14).rotateLeft 1
  let w18 := (dword src1 1 ^^^ w15).rotateLeft 1
  let w19 := (dword src1 0 ^^^ w16).rotateLeft 1
  ofDwords w19 w18 w17 w16

/-! The AES transformations used, but not defined, by the SDM's pseudocode
for the AES instructions: those of the AES standard, FIPS 197 (§4 and §5).
The state `s[r, c]` (FIPS 197 §3.4) is byte `r + 4c` of the 128-bit operand,
so the operand is the state's 16 bytes in memory order. -/

/-- FIPS 197 §4.2, `XTIMES(b)`: `b` shifted left by one bit, XOR `{1b}` if the
bit shifted out was 1. -/
def aesXtimes (b : BitVec 8) : BitVec 8 := (b <<< 1) ^^^ (if b.msb then 0x1b else 0)

/-- FIPS 197 §4.2, the product `b • c` in GF(2⁸): the XOR of `XTIMES` applied
`i` times to `c`, for each bit `i` of `b` that is 1. -/
def aesMul (b c : BitVec 8) : BitVec 8 :=
  (List.range 8).foldl (fun acc i => if b.getLsbD i then acc ^^^ Nat.repeat aesXtimes i c else acc) 0

/-- FIPS 197 §4.4, the inverse `b⁻¹ = b²⁵⁴` in GF(2⁸), with `{00} ↦ {00}`:
`b^254 = b^2 • b^4 • … • b^128`, by repeated squaring. -/
def aesInv (b : BitVec 8) : BitVec 8 :=
  ((List.range 7).foldl (fun (acc, sq) _ => let sq := aesMul sq sq; (aesMul acc sq, sq))
    ((1 : BitVec 8), b)).1

/-- The byte whose bit `i` is `f i`. -/
def ofBits8 (f : Nat → Bool) : BitVec 8 :=
  BitVec.ofNat 8 ((List.range 8).foldl (fun acc i => acc + if f i then 2 ^ i else 0) 0)

/-- FIPS 197 §5.1.1, the S-box: `b ↦ b⁻¹`, then `b'ᵢ = bᵢ ⊕ b₍ᵢ₊₄₎ mod 8 ⊕
b₍ᵢ₊₅₎ mod 8 ⊕ b₍ᵢ₊₆₎ mod 8 ⊕ b₍ᵢ₊₇₎ mod 8 ⊕ cᵢ` with `c = {63}`. -/
def aesSbox (b : BitVec 8) : BitVec 8 :=
  let b := aesInv b
  let c : BitVec 8 := 0x63
  ofBits8 fun i => b.getLsbD i ^^ b.getLsbD ((i + 4) % 8) ^^ b.getLsbD ((i + 5) % 8) ^^
    b.getLsbD ((i + 6) % 8) ^^ b.getLsbD ((i + 7) % 8) ^^ c.getLsbD i

/-- FIPS 197 §5.3.2, the inverse S-box: the inverse of the affine
transformation, `b'ᵢ = b₍ᵢ₊₂₎ mod 8 ⊕ b₍ᵢ₊₅₎ mod 8 ⊕ b₍ᵢ₊₇₎ mod 8 ⊕ dᵢ` with
`d = {05}`, then `b ↦ b⁻¹`. -/
def aesInvSbox (b : BitVec 8) : BitVec 8 :=
  let d : BitVec 8 := 0x05
  aesInv (ofBits8 fun i =>
    b.getLsbD ((i + 2) % 8) ^^ b.getLsbD ((i + 5) % 8) ^^ b.getLsbD ((i + 7) % 8) ^^ d.getLsbD i)

/-- FIPS 197 §5.1.1 `SUBBYTES` and §5.3.2 `INVSUBBYTES`: `f` applied to every byte. -/
def aesMapBytes (f : BitVec 8 → BitVec 8) (x : BitVec 128) : BitVec 128 :=
  ofBytes fun i => f (byte x i)

/-- FIPS 197 §5.1.2 `SHIFTROWS`: `s'[r, c] = s[r, (c + r) mod 4]`. -/
def aesShiftRows (x : BitVec 128) : BitVec 128 :=
  ofBytes fun i => byte x (i % 4 + 4 * ((i / 4 + i % 4) % 4))

/-- FIPS 197 §5.3.1 `INVSHIFTROWS`: `s'[r, c] = s[r, (c − r) mod 4]`. -/
def aesInvShiftRows (x : BitVec 128) : BitVec 128 :=
  ofBytes fun i => byte x (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4))

/-- FIPS 197 §5.1.3 `MIXCOLUMNS` (with `m = [{02}, {03}, {01}, {01}]`) and
§5.3.3 `INVMIXCOLUMNS` (with `m = [{0e}, {0b}, {0d}, {09}]`):
`s'[r, c] = m₀ • s[r, c] ⊕ m₁ • s[r + 1, c] ⊕ m₂ • s[r + 2, c] ⊕ m₃ • s[r + 3, c]`,
rows modulo 4. -/
def aesMixWith (m₀ m₁ m₂ m₃ : BitVec 8) (x : BitVec 128) : BitVec 128 :=
  ofBytes fun i =>
    let a (k : Nat) : BitVec 8 := byte x ((i % 4 + k) % 4 + 4 * (i / 4))
    aesMul m₀ (a 0) ^^^ aesMul m₁ (a 1) ^^^ aesMul m₂ (a 2) ^^^ aesMul m₃ (a 3)

def aesMixColumns : BitVec 128 → BitVec 128 := aesMixWith 0x02 0x03 0x01 0x01

def aesInvMixColumns : BitVec 128 → BitVec 128 := aesMixWith 0x0e 0x0b 0x0d 0x09

/-- The carry-less product of two quadwords. SDM Vol. 2, "PCLMULQDQ", defines
bit `i` of the product as `TEMP1[0] AND TEMP2[i]` XOR … XOR `TEMP1[j] AND
TEMP2[i−j]` over all `j` with `0 ≤ i − j ≤ 63`, and bit 127 as 0; that is
the XOR, over the bits `j` of `a` that are 1, of `b` shifted left by `j`. -/
def clmul (a b : BitVec 64) : BitVec 128 :=
  (List.range 64).foldl (fun acc j => if a.getLsbD j then acc ^^^ (b.setWidth 128 <<< j) else acc) 0

/-- SDM Vol. 2, "PMULHRSW", for one word: `temp[31:0] := INT32 ((a * b) >> 14) + 1;
result := temp[16:1]`, with the signed 32-bit product (`mulWordsSigned`, which no
pair of words overflows) shifted arithmetically. -/
def mulhrs (a b : BitVec 16) : BitVec 16 :=
  ((mulWordsSigned a b).sshiftRight 14 + 1).extractLsb' 1 16

/-- SDM Vol. 2, "PBLENDW" (128-bit legacy SSE version): `IF (imm8[i] = 1) THEN
DEST[16i+15:16i] := SRC[16i+15:16i] ELSE DEST[16i+15:16i] := DEST[16i+15:16i]` for
each word `i`; VPBLENDW applies it to each lane with the same `imm8` (`SRC1` in place
of the destination). -/
def blendWords (a b : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  ofWords fun i => if imm.getLsbD i then word b i else word a i

/-- The result of `op dst, src`, given the old values `a` of `dst` and `b` of
`src`. SDM Vol. 2 (128-bit legacy SSE forms, which leave the destination's
bits above 127 unmodified; no flags are affected):

* MOVDQA: `DEST[127:0] := SRC[127:0]`.
* PADDD: `DEST[31:0] := DEST[31:0] + SRC[31:0]`, and likewise for doublewords
  1–3 (wrapping; no carry between doublewords).
* PXOR: `DEST := DEST XOR SRC`. POR: `DEST := DEST OR SRC`.
* PUNPCKLDQ (`INTERLEAVE_DWORDS`): `DEST[31:0] := SRC1[31:0]; DEST[63:32] :=
  SRC2[31:0]; DEST[95:64] := SRC1[63:32]; DEST[127:96] := SRC2[63:32]`.
* PUNPCKHDQ (`INTERLEAVE_HIGH_DWORDS`): `DEST[31:0] := SRC1[95:64];
  DEST[63:32] := SRC2[95:64]; DEST[95:64] := SRC1[127:96]; DEST[127:96] :=
  SRC2[127:96]`.
* PUNPCKLQDQ (`INTERLEAVE_QWORDS`): `DEST[63:0] := SRC1[63:0];
  DEST[127:64] := SRC2[63:0]`.
* PUNPCKHQDQ (`INTERLEAVE_HIGH_QWORDS`): `DEST[63:0] := SRC1[127:64];
  DEST[127:64] := SRC2[127:64]`.

* PSHUFB (with 128 bit operands): `TEMP := DEST; for i = 0 to 15 { if
  (SRC[(i * 8)+7] = 1) then DEST[(i*8)+7..(i*8)+0] := 0; else index[3..0] :=
  SRC[(i*8)+3 .. (i*8)+0]; DEST[(i*8)+7..(i*8)+0] :=
  TEMP[(index*8+7)..(index*8+0)]; endif }`.
* SHA256MSG1: `W4 := SRC2[31:0]; W3 := SRC1[127:96]; W2 := SRC1[95:64];
  W1 := SRC1[63:32]; W0 := SRC1[31:0]; DEST[127:96] := W3 + σ0(W4);
  DEST[95:64] := W2 + σ0(W3); DEST[63:32] := W1 + σ0(W2); DEST[31:0] :=
  W0 + σ0(W1)`.
* SHA256MSG2: see `sha256Msg2`.
* SHA1MSG1: `W0 := SRC1[127:96]; W1 := SRC1[95:64]; W2 := SRC1[63:32];
  W3 := SRC1[31:0]; W4 := SRC2[127:96]; W5 := SRC2[95:64]; DEST[127:96] :=
  W2 XOR W0; DEST[95:64] := W3 XOR W1; DEST[63:32] := W4 XOR W2;
  DEST[31:0] := W5 XOR W3`.
* SHA1MSG2: see `sha1Msg2`.
* SHA1NEXTE: `TMP := (SRC1[127:96] ROL 30); DEST[127:96] := SRC2[127:96] +
  TMP; DEST[95:64] := SRC2[95:64]; DEST[63:32] := SRC2[63:32]; DEST[31:0] :=
  SRC2[31:0]`.
* PAND: `DEST := DEST AND SRC`. PANDN: `DEST := NOT(DEST) AND SRC`.
* PADDQ: `DEST[63:0] := DEST[63:0] + SRC[63:0]; DEST[127:64] :=
  DEST[127:64] + SRC[127:64]` (wrapping). PSUBQ: `DEST[63:0] := DEST[63:0]
  − SRC[63:0]; DEST[127:64] := DEST[127:64] − SRC[127:64]` (wrapping).
* PMULUDQ: `DEST[63:0] := DEST[31:0] * SRC[31:0]; DEST[127:64] :=
  DEST[95:64] * SRC[95:64]` (unsigned, full 64-bit products).
* PADDW: `DEST[15:0] := DEST[15:0] + SRC[15:0]`, and likewise for words
  1–7. PSUBW: `DEST[15:0] := DEST[15:0] − SRC[15:0]`, and likewise for
  words 1–7. PSUBD: `DEST[31:0] := DEST[31:0] − SRC[31:0]`, and likewise
  for doublewords 1–3 (all wrapping; no carry or borrow between elements).
* PMULLW: `TEMP0[31:0] := DEST[15:0] * SRC[15:0]` (signed multiply; see
  `mulWordsSigned`), … `TEMP7[31:0] := DEST[127:112] * SRC[127:112]`;
  `DEST[15:0] := TEMP0[15:0]`, … `DEST[127:112] := TEMP7[15:0]`.
* PMULHW: the same products; `DEST[15:0] := TEMP0[31:16]`, …
  `DEST[127:112] := TEMP7[31:16]`.
* PMADDWD: `DEST[31:0] := (DEST[15:0] * SRC[15:0]) + (DEST[31:16] *
  SRC[31:16])`, … `DEST[127:96] := (DEST[111:96] * SRC[111:96]) +
  (DEST[127:112] * SRC[127:112])` (signed products, see `mulWordsSigned`;
  the sum wraps: the one sum that overflows, of four `8000H` words, is
  `80000000H`).
* PMULHRSW (SSSE3): `temp0[31:0] := INT32 ((DEST[15:0] * SRC[15:0]) >> 14) + 1`,
  … `temp7[31:0] := INT32 ((DEST[127:112] * SRC[127:112]) >> 14) + 1`;
  `DEST[15:0] := temp0[16:1]`, … `DEST[127:112] := temp7[16:1]` (signed
  products, see `mulWordsSigned`; `>>` an arithmetic shift of the 32-bit
  product: see `mulhrs`).
* PCMPGTW (`COMPARE_WORDS_GREATER`): `IF DEST[15:0] > SRC[15:0] THEN
  DEST[15:0] := FFFFH ELSE DEST[15:0] := 0`, and likewise for words 1–7
  (a signed comparison).
* PACKSSDW: `DEST[15:0] := SaturateSignedDwordToSignedWord (DEST[31:0])`,
  … `DEST[63:48] := SaturateSignedDwordToSignedWord (DEST[127:96])`;
  `DEST[79:64] := SaturateSignedDwordToSignedWord (SRC[31:0])`, …
  `DEST[127:112] := SaturateSignedDwordToSignedWord (SRC[127:96])` (see
  `satSignedWord`).
* PACKSSWB: `DEST[7:0] := SaturateSignedWordToSignedByte (DEST[15:0])`, …
  `DEST[63:56] := SaturateSignedWordToSignedByte (DEST[127:112])`;
  `DEST[71:64] := SaturateSignedWordToSignedByte (SRC[15:0])`, …
  `DEST[127:120] := SaturateSignedWordToSignedByte (SRC[127:112])` (see
  `satSignedByte`).
* PUNPCKLWD (`INTERLEAVE_WORDS`): `DEST[15:0] := SRC1[15:0]; DEST[31:16] :=
  SRC2[15:0]; DEST[47:32] := SRC1[31:16]; DEST[63:48] := SRC2[31:16];
  DEST[79:64] := SRC1[47:32]; DEST[95:80] := SRC2[47:32]; DEST[111:96] :=
  SRC1[63:48]; DEST[127:112] := SRC2[63:48]`.
* PUNPCKHWD (`INTERLEAVE_HIGH_WORDS`): the same, from `SRC1[127:64]` and
  `SRC2[127:64]`: `DEST[15:0] := SRC1[79:64]; DEST[31:16] := SRC2[79:64];
  …; DEST[127:112] := SRC2[127:112]`.
* AESENC: `STATE := SRC1; RoundKey := SRC2; STATE := ShiftRows(STATE);
  STATE := SubBytes(STATE); STATE := MixColumns(STATE); DEST[127:0] :=
  STATE XOR RoundKey`.
* AESENCLAST: as AESENC, without `MixColumns`.
* AESDEC: `STATE := SRC1; RoundKey := SRC2; STATE := InvShiftRows(STATE);
  STATE := InvSubBytes(STATE); STATE := InvMixColumns(STATE); DEST[127:0] :=
  STATE XOR RoundKey`.
* AESDECLAST: as AESDEC, without `InvMixColumns`.
* AESIMC: `DEST[127:0] := InvMixColumns(SRC)`.
* PCMPEQD: `IF DEST[31:0] = SRC[31:0] THEN DEST[31:0] := FFFFFFFFH; ELSE
  DEST[31:0] := 0; FI;`, and likewise for doublewords 1–3.

(`SRC1` is the destination, `SRC2` the source.) -/
def XBinOp.eval : XBinOp → BitVec 128 → BitVec 128 → BitVec 128
  | .movdqa, _, b => b
  | .paddd, a, b =>
    ofDwords (dword a 0 + dword b 0) (dword a 1 + dword b 1) (dword a 2 + dword b 2)
      (dword a 3 + dword b 3)
  | .pxor, a, b => a ^^^ b
  | .por, a, b => a ||| b
  | .punpckldq, a, b => ofDwords (dword a 0) (dword b 0) (dword a 1) (dword b 1)
  | .punpckhdq, a, b => ofDwords (dword a 2) (dword b 2) (dword a 3) (dword b 3)
  | .punpcklqdq, a, b => qword b 0 ++ qword a 0
  | .punpckhqdq, a, b => qword b 1 ++ qword a 1
  | .pshufb, a, b => ofBytes fun i =>
    let c := byte b i
    if c.msb then 0 else byte a (c.extractLsb' 0 4).toNat
  | .sha256msg1, a, b =>
    ofDwords (dword a 0 + sha256Sigma0 (dword a 1)) (dword a 1 + sha256Sigma0 (dword a 2))
      (dword a 2 + sha256Sigma0 (dword a 3)) (dword a 3 + sha256Sigma0 (dword b 0))
  | .sha256msg2, a, b => sha256Msg2 a b
  | .sha1msg1, a, b =>
    ofDwords (dword b 2 ^^^ dword a 0) (dword b 3 ^^^ dword a 1) (dword a 0 ^^^ dword a 2)
      (dword a 1 ^^^ dword a 3)
  | .sha1msg2, a, b => sha1Msg2 a b
  | .sha1nexte, a, b =>
    ofDwords (dword b 0) (dword b 1) (dword b 2) (dword b 3 + (dword a 3).rotateLeft 30)
  | .pand, a, b => a &&& b
  | .pandn, a, b => ~~~a &&& b
  | .paddq, a, b => (qword a 1 + qword b 1) ++ (qword a 0 + qword b 0)
  | .psubq, a, b => (qword a 1 - qword b 1) ++ (qword a 0 - qword b 0)
  | .pmuludq, a, b =>
    ((dword a 2).setWidth 64 * (dword b 2).setWidth 64) ++
      ((dword a 0).setWidth 64 * (dword b 0).setWidth 64)
  | .paddw, a, b => ofWords fun i => word a i + word b i
  | .psubw, a, b => ofWords fun i => word a i - word b i
  | .psubd, a, b =>
    ofDwords (dword a 0 - dword b 0) (dword a 1 - dword b 1) (dword a 2 - dword b 2)
      (dword a 3 - dword b 3)
  | .pmullw, a, b => ofWords fun i => (mulWordsSigned (word a i) (word b i)).extractLsb' 0 16
  | .pmulhw, a, b => ofWords fun i => (mulWordsSigned (word a i) (word b i)).extractLsb' 16 16
  | .pmaddwd, a, b =>
    let m (i : Nat) : BitVec 32 :=
      mulWordsSigned (word a (2 * i)) (word b (2 * i)) +
        mulWordsSigned (word a (2 * i + 1)) (word b (2 * i + 1))
    ofDwords (m 0) (m 1) (m 2) (m 3)
  | .pmulhrsw, a, b => ofWords fun i => mulhrs (word a i) (word b i)
  | .pcmpgtw, a, b => ofWords fun i => if (word b i).slt (word a i) then 0xFFFF else 0
  | .packssdw, a, b =>
    ofWords fun i => if i < 4 then satSignedWord (dword a i) else satSignedWord (dword b (i - 4))
  | .packsswb, a, b =>
    ofBytes fun i => if i < 8 then satSignedByte (word a i) else satSignedByte (word b (i - 8))
  | .punpcklwd, a, b => ofWords fun i => if i % 2 = 0 then word a (i / 2) else word b (i / 2)
  | .punpckhwd, a, b =>
    ofWords fun i => if i % 2 = 0 then word a (4 + i / 2) else word b (4 + i / 2)
  | .aesenc, a, b => aesMixColumns (aesMapBytes aesSbox (aesShiftRows a)) ^^^ b
  | .aesenclast, a, b => aesMapBytes aesSbox (aesShiftRows a) ^^^ b
  | .aesdec, a, b => aesInvMixColumns (aesMapBytes aesInvSbox (aesInvShiftRows a)) ^^^ b
  | .aesdeclast, a, b => aesMapBytes aesInvSbox (aesInvShiftRows a) ^^^ b
  | .aesimc, _, b => aesInvMixColumns b
  | .pcmpeqd, a, b =>
    let eq (i : Nat) : BitVec 32 := if dword a i = dword b i then 0xFFFFFFFF else 0
    ofDwords (eq 0) (eq 1) (eq 2) (eq 3)

/-- SDM Vol. 2, the forms with an immediate count (no flags are affected):

* "PSLLW/PSLLD/PSLLQ" and "PSRLW/PSRLD/PSRLQ", words: `IF (COUNT > 15) THEN
  DEST[127:0] := 0 ELSE DEST[15:0] := ZeroExtend(DEST[15:0] << COUNT)`
  (respectively `>>`, a logical shift), and likewise for words 1–7.
* "PSRAW/PSRAD": `IF (COUNT > 15) THEN COUNT := 16; DEST[15:0] :=
  SignExtend(DEST[15:0] >> COUNT)` (an arithmetic shift), and likewise for
  words 1–7; doublewords: `IF (COUNT > 31) THEN COUNT := 32; DEST[31:0] :=
  SignExtend(DEST[31:0] >> COUNT)`, and likewise for doublewords 1–3.
* "PSLLW/PSLLD/PSLLQ" and "PSRLW/PSRLD/PSRLQ", doublewords: `IF (COUNT > 31)
  THEN DEST[127:0] := 0 ELSE DEST[31:0] := ZeroExtend(DEST[31:0] << COUNT)`
  (respectively `>>`, a logical shift), and likewise for doublewords 1–3.
* The same, quadwords: `IF (COUNT > 63) THEN DEST[127:0] := 0 ELSE
  DEST[63:0] := ZeroExtend(DEST[63:0] << COUNT)` (respectively `>>`), and
  likewise for quadword 1.
* "PSLLDQ" and "PSRLDQ": `TEMP := COUNT; IF (TEMP > 15) THEN TEMP := 16;
  DEST := DEST << (TEMP * 8)` (respectively `>>`, a logical shift). -/
def XShiftOp.eval (op : XShiftOp) (a : BitVec 128) (count : BitVec 8) : BitVec 128 :=
  let n := count.toNat
  let dwords (f : BitVec 32 → BitVec 32) : BitVec 128 :=
    if 31 < n then 0 else ofDwords (f (dword a 0)) (f (dword a 1)) (f (dword a 2)) (f (dword a 3))
  let qwords (f : BitVec 64 → BitVec 64) : BitVec 128 :=
    if 63 < n then 0 else f (qword a 1) ++ f (qword a 0)
  let words (f : BitVec 16 → BitVec 16) : BitVec 128 :=
    if 15 < n then 0 else ofWords fun i => f (word a i)
  match op with
  | .pslld => dwords (· <<< n)
  | .psrld => dwords (· >>> n)
  | .psllq => qwords (· <<< n)
  | .psrlq => qwords (· >>> n)
  | .pslldq => a <<< (min n 16 * 8)
  | .psrldq => a >>> (min n 16 * 8)
  | .psllw => words (· <<< n)
  | .psrlw => words (· >>> n)
  | .psraw => ofWords fun i => (word a i).sshiftRight (min n 16)
  | .psrad =>
    let f (x : BitVec 32) := x.sshiftRight (min n 32)
    ofDwords (f (dword a 0)) (f (dword a 1)) (f (dword a 2)) (f (dword a 3))

/-- SDM Vol. 2, "PSHUFD": `DEST[31:0] := (SRC >> (ORDER[1:0] * 32))[31:0];
DEST[63:32] := (SRC >> (ORDER[3:2] * 32))[31:0]; DEST[95:64] := (SRC >>
(ORDER[5:4] * 32))[31:0]; DEST[127:96] := (SRC >> (ORDER[7:6] * 32))[31:0]`.
No flags are affected. -/
def shufDwords (a : BitVec 128) (order : BitVec 8) : BitVec 128 :=
  ofDwords (dword a (order.extractLsb' 0 2).toNat) (dword a (order.extractLsb' 2 2).toNat)
    (dword a (order.extractLsb' 4 2).toNat) (dword a (order.extractLsb' 6 2).toNat)

/-- SDM Vol. 2, "PALIGNR", 128-bit legacy SSE version: `temp1[255:0] :=
((DEST[127:0] << 128) OR SRC[127:0])>>(imm8*8); DEST[127:0] :=
temp1[127:0]`. No flags are affected. -/
def alignRight (dst src : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  ((dst ++ src) >>> (imm.toNat * 8)).extractLsb' 0 128

/-- SDM Vol. 2, "SHA256RNDS2", where `SRC1` is the destination, `SRC2` the
source and `wk` the implicit operand `XMM0`: `A_0 := SRC2[127:96]; B_0 :=
SRC2[95:64]; C_0 := SRC1[127:96]; D_0 := SRC1[95:64]; E_0 := SRC2[63:32];
F_0 := SRC2[31:0]; G_0 := SRC1[63:32]; H_0 := SRC1[31:0]; WK0 :=
XMM0[31:0]; WK1 := XMM0[63:32]; FOR i = 0 to 1 A_(i+1) := Ch(E_i, F_i,
G_i) + Σ1(E_i) + WKi + H_i + Maj(A_i, B_i, C_i) + Σ0(A_i); B_(i+1) := A_i;
C_(i+1) := B_i; D_(i+1) := C_i; E_(i+1) := Ch(E_i, F_i, G_i) + Σ1(E_i) +
WKi + H_i + D_i; F_(i+1) := E_i; G_(i+1) := F_i; H_(i+1) := G_i; ENDFOR
DEST[127:96] := A_2; DEST[95:64] := B_2; DEST[63:32] := E_2; DEST[31:0] :=
F_2`. No flags are affected. -/
def sha256Rnds2 (src1 src2 wk : BitVec 128) : BitVec 128 :=
  let a0 := dword src2 3
  let b0 := dword src2 2
  let c0 := dword src1 3
  let d0 := dword src1 2
  let e0 := dword src2 1
  let f0 := dword src2 0
  let g0 := dword src1 1
  let h0 := dword src1 0
  let wk0 := dword wk 0
  let wk1 := dword wk 1
  let a1 := sha256Ch e0 f0 g0 + sha256BigSigma1 e0 + wk0 + h0 + sha256Maj a0 b0 c0 +
    sha256BigSigma0 a0
  let b1 := a0
  let c1 := b0
  let d1 := c0
  let e1 := sha256Ch e0 f0 g0 + sha256BigSigma1 e0 + wk0 + h0 + d0
  let f1 := e0
  let g1 := f0
  let h1 := g0
  let a2 := sha256Ch e1 f1 g1 + sha256BigSigma1 e1 + wk1 + h1 + sha256Maj a1 b1 c1 +
    sha256BigSigma0 a1
  let b2 := a1
  let e2 := sha256Ch e1 f1 g1 + sha256BigSigma1 e1 + wk1 + h1 + d1
  let f2 := e1
  ofDwords f2 e2 b2 a2

/-- SDM Vol. 2, "SHA1RNDS4", where `SRC1` is the destination and `SRC2` the
source: `f()` and `K` are `fᵢ()` and `Kᵢ` for `i = imm8[1:0]` (`sha1F`,
`sha1K`); `A := SRC1[127:96]; B := SRC1[95:64]; C := SRC1[63:32]; D :=
SRC1[31:0]; W0E := SRC2[127:96]; W1 := SRC2[95:64]; W2 := SRC2[63:32]; W3
:= SRC2[31:0]; A_1 := f(B, C, D) + (A ROL 5) + W0E + K; B_1 := A; C_1 := B
ROL 30; D_1 := C; E_1 := D; FOR i := 1 to 3 A_(i+1) := f(B_i, C_i, D_i) +
(A_i ROL 5) + W_i + E_i + K; B_(i+1) := A_i; C_(i+1) := B_i ROL 30;
D_(i+1) := C_i; E_(i+1) := D_i; ENDFOR DEST[127:96] := A_4; DEST[95:64] :=
B_4; DEST[63:32] := C_4; DEST[31:0] := D_4`. No flags are affected. -/
def sha1Rnds4 (src1 src2 : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  let i := (imm.extractLsb' 0 2).toNat
  let a0 := dword src1 3
  let b0 := dword src1 2
  let c0 := dword src1 1
  let d0 := dword src1 0
  let w0e := dword src2 3
  let w1 := dword src2 2
  let w2 := dword src2 1
  let w3 := dword src2 0
  let a1 := sha1F i b0 c0 d0 + a0.rotateLeft 5 + w0e + sha1K i
  let b1 := a0
  let c1 := b0.rotateLeft 30
  let d1 := c0
  let e1 := d0
  let a2 := sha1F i b1 c1 d1 + a1.rotateLeft 5 + w1 + e1 + sha1K i
  let b2 := a1
  let c2 := b1.rotateLeft 30
  let d2 := c1
  let e2 := d1
  let a3 := sha1F i b2 c2 d2 + a2.rotateLeft 5 + w2 + e2 + sha1K i
  let b3 := a2
  let c3 := b2.rotateLeft 30
  let d3 := c2
  let e3 := d2
  let a4 := sha1F i b3 c3 d3 + a3.rotateLeft 5 + w3 + e3 + sha1K i
  let b4 := a3
  let c4 := b3.rotateLeft 30
  let d4 := c3
  ofDwords d4 c4 b4 a4

/-- SDM Vol. 2, "AESKEYGENASSIST": `X3[31:0] := SRC[127:96]; X2[31:0] :=
SRC[95:64]; X1[31:0] := SRC[63:32]; X0[31:0] := SRC[31:0]; RCON[31:0] :=
ZeroExtend(imm8[7:0]); DEST[31:0] := SubWord(X1); DEST[63:32] :=
RotWord(SubWord(X1)) XOR RCON; DEST[95:64] := SubWord(X3); DEST[127:96] :=
RotWord(SubWord(X3)) XOR RCON`, where `SubWord` applies the S-box to each
byte and `RotWord(x) = (x >> 8) OR (x << 24)` (a 32-bit rotate right by 8).
No flags are affected. -/
def aesKeygenAssist (src : BitVec 128) (rcon : BitVec 8) : BitVec 128 :=
  let subWord (x : BitVec 32) : BitVec 32 :=
    aesSbox (x.extractLsb' 24 8) ++ aesSbox (x.extractLsb' 16 8) ++
      aesSbox (x.extractLsb' 8 8) ++ aesSbox (x.extractLsb' 0 8)
  let rc : BitVec 32 := rcon.setWidth 32
  let x1 := subWord (dword src 1)
  let x3 := subWord (dword src 3)
  ofDwords x1 (x1.rotateRight 8 ^^^ rc) x3 (x3.rotateRight 8 ^^^ rc)

/-- SDM Vol. 2, "PCLMULQDQ", 128-bit legacy SSE version: `IF (imm8[0] = 0)
THEN TEMP1 := SRC1[63:0] ELSE TEMP1 := SRC1[127:64]; IF (imm8[4] = 0) THEN
TEMP2 := SRC2[63:0] ELSE TEMP2 := SRC2[127:64]`, and `DEST[127:0]` the
carry-less product of `TEMP1` and `TEMP2` (`clmul`). No flags are affected. -/
def pclmul (src1 src2 : BitVec 128) (sel : BitVec 8) : BitVec 128 :=
  clmul (qword src1 (if sel.getLsbD 0 then 1 else 0)) (qword src2 (if sel.getLsbD 4 then 1 else 0))

/-- Semantics of an SSE instruction that writes only an SSE register. MOVQ
with an XMM destination: SDM Vol. 2, "MOVD/MOVQ", 128-bit legacy SSE
version: `DEST[63:0] := SRC[63:0]; DEST[127:64] := 0000000000000000H`. No
flags are affected. -/
def XOp.exec : XOp → State → State
  | .bin op d r, s => s.setXmm d (op.eval (s.xmm d) (s.xmm r))
  | .shift op d n, s => s.setXmm d (op.eval (s.xmm d) n)
  | .pshufd d r o, s => s.setXmm d (shufDwords (s.xmm r) o)
  | .palignr d r n, s => s.setXmm d (alignRight (s.xmm d) (s.xmm r) n)
  | .pblendw d r n, s => s.setXmm d (blendWords (s.xmm d) (s.xmm r) n)
  | .sha256rnds2 d r, s => s.setXmm d (sha256Rnds2 (s.xmm d) (s.xmm r) (s.xmm .xmm0))
  | .sha1rnds4 d r n, s => s.setXmm d (sha1Rnds4 (s.xmm d) (s.xmm r) n)
  | .movq d r, s => s.setXmm d ((0 : BitVec 64) ++ s.gpr r)
  | .aeskeygenassist d r n, s => s.setXmm d (aesKeygenAssist (s.xmm r) n)
  | .pclmulqdq d r n, s => s.setXmm d (pclmul (s.xmm d) (s.xmm r) n)

end VG.X86_64
