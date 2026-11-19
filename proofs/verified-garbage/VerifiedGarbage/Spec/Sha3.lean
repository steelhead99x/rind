module

public import VerifiedGarbage.TCB.Mem

/-!
# SHA-3 and SHAKE (FIPS 202)

**Trusted** (as every file in `Spec/`). The permutation Keccak-f[1600], the
sponge construction, and the hash functions SHA3-224, SHA3-256, SHA3-384 and
SHA3-512 and extendable-output functions SHAKE128 and SHAKE256, transcribed
from FIPS 202, *SHA-3 Standard: Permutation-Based Hash and
Extendable-Output Functions* (August 2015); section, algorithm and appendix
numbers below refer to it.

Messages and outputs are sequences of bytes (the standard allows any number
of bits). The standard orders the bits of a byte least significant first
(Appendix B.1), so a string of bytes is the string of bits whose bit `8i + k`
is bit `k` of byte `i`, and each 64-bit lane of the state is the
little-endian integer of 8 consecutive bytes. The rate is in bytes.

The primitives implemented in assembly are the sponge taken apart for
streaming: absorbing message bytes into a state that `Repr` relates to the
message absorbed so far, padding and absorbing the last block, and squeezing
output. Their contracts are in `Spec/Sha3/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.Sha3

/-- A lane: the 64 bits `A[x, y, 0] … A[x, y, 63]` of a state with the same
`x` and `y`, bit `z` of the lane being `A[x, y, z]` (§3.1.1, `w = 64`). -/
abbrev Lane := BitVec 64

/-- A state of Keccak-p[1600] as its 25 lanes, lane `(x, y)` at index
`x + 5y`, so that bit `z` of lane `x + 5y` is `A[x, y, z] = S[64(5y + x) + z]`
(§3.1.2). -/
abbrev State := Vector Lane 25

/-- The all-zero state `0ᵇ`. -/
def zero : State := Vector.replicate 25 0

/-- Lane `(x mod 5, y mod 5)` of `A`. -/
def lane (A : State) (x y : Nat) : Lane := A[x % 5 + 5 * (y % 5)]!

/-! ## Step mappings (§3.2) -/

/-- Algorithm 1, θ: `C[x] = A[x, 0] ⊕ … ⊕ A[x, 4]`,
`D[x, z] = C[(x - 1) mod 5, z] ⊕ C[(x + 1) mod 5, (z - 1) mod 64]`, and
`A′[x, y, z] = A[x, y, z] ⊕ D[x, z]`. (Taking bit `(z - 1) mod 64` of a lane
for bit `z` is rotating the lane left by one.) -/
def theta (A : State) : State :=
  let C (x : Nat) : Lane := lane A x 0 ^^^ lane A x 1 ^^^ lane A x 2 ^^^ lane A x 3 ^^^ lane A x 4
  let D (x : Nat) : Lane := C ((x + 4) % 5) ^^^ (C ((x + 1) % 5)).rotateLeft 1
  Vector.ofFn fun i => A[i] ^^^ D (i % 5)

/-- The positions `(x, y)` visited by Algorithm 2: `(1, 0)` at `t = 0`, and
`(y, (2x + 3y) mod 5)` after `(x, y)`. -/
def rhoPos : Nat → Nat × Nat
  | 0 => (1, 0)
  | t + 1 => let (x, y) := rhoPos t; (y, (2 * x + 3 * y) % 5)

/-- Algorithm 2, ρ: `A′[0, 0] = A[0, 0]`, and for `t = 0 … 23`,
`A′[x, y, z] = A[x, y, (z - (t + 1)(t + 2)/2) mod 64]` at the `t`-th position
`(x, y)`: lane `(x, y)` rotated left by `(t + 1)(t + 2)/2 mod 64`. -/
def rho (A : State) : State :=
  Vector.ofFn fun i =>
    match (List.range 24).find? (fun t => rhoPos t == (i.val % 5, i.val / 5)) with
    | some t => A[i].rotateLeft ((t + 1) * (t + 2) / 2 % 64)
    | none => A[i]

/-- Algorithm 3, π: `A′[x, y, z] = A[(x + 3y) mod 5, x, z]`. -/
def pi (A : State) : State :=
  Vector.ofFn fun i => lane A (i.val % 5 + 3 * (i.val / 5)) (i.val % 5)

/-- Algorithm 4, χ:
`A′[x, y, z] = A[x, y, z] ⊕ ((A[(x + 1) mod 5, y, z] ⊕ 1) ⋅ A[(x + 2) mod 5, y, z])`. -/
def chi (A : State) : State :=
  Vector.ofFn fun i =>
    let x := i.val % 5; let y := i.val / 5
    lane A x y ^^^ (~~~(lane A (x + 1) y) &&& lane A (x + 2) y)

/-- One step of the linear feedback shift register of Algorithm 5, on
`R = R[0] … R[7]` as the number with bit `i` equal to `R[i]`:
`R = 0 ‖ R`; `R[0] = R[0] ⊕ R[8]`; `R[4] = R[4] ⊕ R[8]`; `R[5] = R[5] ⊕ R[8]`;
`R[6] = R[6] ⊕ R[8]`; `R = Trunc₈(R)`. -/
def rcStep (R : Nat) : Nat :=
  let R := 2 * R
  let r8 := R / 256 % 2
  (R ^^^ (r8 * 0b1110001)) % 256

/-- Algorithm 5, `rc(t)`: 1 if `t mod 255 = 0`, and otherwise `R[0]` after
`t mod 255` steps from `R = 10000000`. -/
def rc (t : Nat) : Bool :=
  if t % 255 = 0 then true
  else Nat.repeat rcStep (t % 255) 1 % 2 == 1

/-- The round constant of Algorithm 6 for round `iᵣ`: the lane with bit
`2ʲ - 1` equal to `rc(j + 7iᵣ)` for `j = 0 … 6` (`ℓ = 6`), and every other bit
0. -/
def RC (ir : Nat) : Lane :=
  (List.range 7).foldl (fun RC j => if rc (j + 7 * ir) then RC ||| (1#64 <<< (2 ^ j - 1)) else RC) 0

/-- Algorithm 6, ι: `A′[0, 0, z] = A[0, 0, z] ⊕ RC[z]`, other lanes unchanged. -/
def iota (A : State) (ir : Nat) : State := A.set 0 (A[0] ^^^ RC ir)

/-! ## The permutation (§3.3, §3.4) -/

/-- `Rnd(A, iᵣ) = ι(χ(π(ρ(θ(A)))), iᵣ)`. -/
def rnd (A : State) (ir : Nat) : State := iota (chi (pi (rho (theta A)))) ir

/-- Keccak-f[1600] = Keccak-p[1600, 24] (§3.4): Algorithm 7 with `nᵣ = 24`,
applying `Rnd` for `iᵣ` from `12 + 2ℓ - nᵣ = 0` to `23`. -/
def keccakF (A : State) : State := (List.range 24).foldl rnd A

/-! ## Bytes and states (Appendix B.1) -/

/-- The 200 bytes of a state, lane by lane, each lane little-endian. -/
def toBytes (A : State) : List Byte :=
  A.toList.flatMap fun a => (List.range 8).map fun k => a.extractLsb' (8 * k) 8

/-- The lane whose little-endian bytes are `b 0 … b 7`. -/
def laneOfBytes (b : Nat → Byte) : Lane :=
  b 7 ++ b 6 ++ b 5 ++ b 4 ++ b 3 ++ b 2 ++ b 1 ++ b 0

/-- `A` with the bytes `bs` XORed into its first `|bs|` bytes: for a block
`P` of `r` bytes, `S ⊕ (P ‖ 0ᶜ)` of Algorithm 8. -/
def xorBytes (A : State) (bs : List Byte) : State :=
  Vector.ofFn fun i => A[i] ^^^ laneOfBytes fun k => bs.getD (8 * i.val + k) 0

/-! ## The sponge (§4, §5.1)

`rate` is the rate `r` in bytes (`r / 8` in the standard's bits). -/

/-- `pad10*1` (§5.1) after the domain-separation suffix of the message, for
a message of bytes whose length is `ℓ mod r` bytes past its last whole
block: the `q = r - ℓ mod r` bytes (`1 ≤ q ≤ r`) that follow it.

The suffix (the bits `01` of SHA-3 or `1111` of SHAKE, §6) and the first `1`
bit of `pad10*1` fit in one byte, `suffix`, whose other bits are 0; the last
`1` bit of `pad10*1` is bit 7 of the last byte. So the padding is `suffix`,
then `q - 2` zero bytes, then `0x80`; or, when `q = 1`, the single byte
`suffix ⊕ 0x80` (Appendix B.2). -/
def padding (rate : Nat) (suffix : Byte) (ℓ : Nat) : List Byte :=
  let q := rate - ℓ % rate
  if q = 1 then [suffix ^^^ 0x80] else suffix :: List.replicate (q - 2) 0 ++ [0x80]

/-- `P = N ‖ pad(r, len(N))`, with the domain-separation suffix. -/
def pad (rate : Nat) (suffix : Byte) (m : List Byte) : List Byte :=
  m ++ padding rate suffix m.length

/-- Block `i` of `P`: bytes `r·i … r·i + r - 1`. -/
def block (rate : Nat) (P : List Byte) (i : Nat) : List Byte := (P.drop (rate * i)).take rate

/-- Algorithm 8, steps 1–6: the state after absorbing the `⌊|P| / r⌋` whole
blocks of `P`, from `S = 0ᵇ`, with `S = f(S ⊕ (Pᵢ ‖ 0ᶜ))` for each. -/
def absorb (rate : Nat) (P : List Byte) : State :=
  (List.range (P.length / rate)).foldl (fun S i => keccakF (xorBytes S (block rate P i))) zero

/-- `Trunc_r(S) ‖ Trunc_r(f(S)) ‖ …`: the first `r` bytes of each of `n`
successive states from `S`. -/
def squeezeBlocks (rate : Nat) (S : State) : (n : Nat) → List Byte
  | 0 => []
  | n + 1 => (toBytes S).take rate ++ squeezeBlocks rate (keccakF S) n

/-- Algorithm 8, steps 7–10: the first `d` bytes of output from the state
`S` after absorbing: `Z = Trunc_r(S)`, then `S = f(S)` and
`Z = Z ‖ Trunc_r(S)` until `d ≤ |Z|`, which takes `⌈d / r⌉` blocks (none
when `d = 0`). -/
def squeeze (rate : Nat) (S : State) (d : Nat) : List Byte :=
  (squeezeBlocks rate S ((d + rate - 1) / rate)).take d

/-- Bytes `pos … pos + d - 1` of the output `Trunc_r(S) ‖ Trunc_r(f(S)) ‖ …`
from the state `S`: the output of `squeeze` from offset `pos` on, for output
squeezed in pieces. -/
def squeezeFrom (rate : Nat) (S : State) (pos d : Nat) : List Byte :=
  ((squeezeBlocks rate S ((pos + d + rate - 1) / rate)).drop pos).take d

/-- `SPONGE[f, pad10*1, r](N ‖ suffix, d)` (Algorithm 8), for `d` bytes of
output. -/
def sponge (rate : Nat) (suffix : Byte) (m : List Byte) (d : Nat) : List Byte :=
  squeeze rate (absorb rate (pad rate suffix m)) d

/-! ## SHA-3 and SHAKE (§6) -/

/-- `M ‖ 01` (§6.1), and the first bit of `pad10*1`. -/
def sha3Suffix : Byte := 0x06

/-- `M ‖ 1111` (§6.2), and the first bit of `pad10*1`. -/
def shakeSuffix : Byte := 0x1f

/-- `KECCAK[c](N, d) = SPONGE[Keccak-p[1600, 24], pad10*1, 1600 - c](N, d)`
(§5.2), for a capacity `c` in bits and `d` bytes of output. -/
def keccak (c : Nat) (suffix : Byte) (m : List Byte) (d : Nat) : List Byte :=
  sponge ((1600 - c) / 8) suffix m d

/-- `SHA3-224(M) = KECCAK[448](M ‖ 01, 224)`. -/
def sha3_224 (m : List Byte) : List Byte := keccak 448 sha3Suffix m 28
/-- `SHA3-256(M) = KECCAK[512](M ‖ 01, 256)`. -/
def sha3_256 (m : List Byte) : List Byte := keccak 512 sha3Suffix m 32
/-- `SHA3-384(M) = KECCAK[768](M ‖ 01, 384)`. -/
def sha3_384 (m : List Byte) : List Byte := keccak 768 sha3Suffix m 48
/-- `SHA3-512(M) = KECCAK[1024](M ‖ 01, 512)`. -/
def sha3_512 (m : List Byte) : List Byte := keccak 1024 sha3Suffix m 64
/-- `SHAKE128(M, d) = KECCAK[256](M ‖ 1111, d)`, for `d` bytes. -/
def shake128 (m : List Byte) (d : Nat) : List Byte := keccak 256 shakeSuffix m d
/-- `SHAKE256(M, d) = KECCAK[512](M ‖ 1111, d)`, for `d` bytes. -/
def shake256 (m : List Byte) (d : Nat) : List Byte := keccak 512 shakeSuffix m d

/-! ## The state on memory

A state is stored as `[u64; 25]`: lane `i` as a native (little-endian)
`u64`, so the 200 bytes in memory are `toBytes` of the state. -/

/-- The state stored as `[u64; 25]` at `p`. -/
def stateAt (m : Mem) (p : Addr) : State :=
  Vector.ofFn fun i => m.readW (p + BitVec.ofNat 64 (8 * i.val)) 64

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-! ## Streaming

A message is absorbed in pieces into a state stored as `[u64; 25]`, with no
buffer: a block is XORed into the state as its bytes arrive, and the state
permuted when the block is complete. The position within the current block
(the message's length modulo the rate) is public, and not part of the
state: the caller keeps it and passes it to every call. -/

/-- The state at `p` represents the message `m`, for the rate `rate`: it is
the state after absorbing the `⌊|m| / r⌋` whole blocks of `m`, with the
remaining `|m| mod r` bytes of `m` XORed into its first bytes. (The all-zero
state represents the empty message.) -/
def Repr (mem : Mem) (p : Addr) (rate : Nat) (m : List Byte) : Prop :=
  stateAt mem p = xorBytes (absorb rate m) (m.drop (rate * (m.length / rate)))

end VG.Spec.Sha3
