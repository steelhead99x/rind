module

public import VerifiedGarbage.TCB.VectorCrypto -- shake: keep (re-exports the existing Arm names below)

/-!
# AArch64 AdvSIMD values and the cryptographic functions of the Arm ARM

**Trusted.** Helpers for the semantics of the AdvSIMD and cryptographic
instructions in `TCB/AArch64/Isa.lean`: the lanes of a 128-bit vector
register, and the shared pseudocode functions that the Arm Architecture
Reference Manual for A-profile (DDI 0487) uses in the descriptions of the
cryptographic instructions (chapter J1, "shared/functions/crypto").

Lanes are numbered from the least significant, as the pseudocode's
`Elem[vector, e, size]` does: lane `e` of size `size` is bits
`(e+1)*size-1 : e*size`. On a little-endian machine, lane `e` of a register
loaded by `LDR (immediate, SIMD&FP)` holds the `e`-th `size`-bit value in
memory.
-/

@[expose] public section

namespace VG.AArch64

-- Keep the existing names as aliases of the architecture-independent values.
export VectorCrypto (vbyte ofVBytes aesXtimes aesMul aesInv ofBits8 aesSbox aesInvSbox
  aesMapBytes aesShiftRows aesInvShiftRows aesMixWith aesMixColumns aesInvMixColumns polyMul)

/-- `Elem[x, e, 16]`: halfword `e` of `x`. -/
def vhalf (x : BitVec 128) (e : Nat) : BitVec 16 := x.extractLsb' (16 * e) 16

/-- `Elem[x, e, 32]`: word `e` of `x`. -/
def vword (x : BitVec 128) (e : Nat) : BitVec 32 := x.extractLsb' (32 * e) 32

/-- `Elem[x, e, 64]`: doubleword `e` of `x`. -/
def vdword (x : BitVec 128) (e : Nat) : BitVec 64 := x.extractLsb' (64 * e) 64

/-- The vector whose halfword `e` is `f e`. -/
def ofVHalves (f : Nat → BitVec 16) : BitVec 128 :=
  f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0

/-- The vector whose words are `w0` (bits 31:0), `w1`, `w2`, `w3` (bits 127:96). -/
def ofVWords (w0 w1 w2 w3 : BitVec 32) : BitVec 128 := w3 ++ w2 ++ w1 ++ w0

/-- The vector whose doublewords are `d0` (bits 63:0) and `d1` (bits 127:64). -/
def ofVDwords (d0 d1 : BitVec 64) : BitVec 128 := d1 ++ d0

/-- `PolynomialMult(op1, op2)` for 8-bit operands: `result = Zeros(16);
extended_op2 = ZeroExtend(op2, 16); for i = 0 to 7: if op1<i> == '1' then
result = result EOR LSL(extended_op2, i)` (as `polyMul`, for 64-bit ones). -/
def polyMul8 (a b : BitVec 8) : BitVec 16 :=
  (List.range 8).foldl (fun acc i => if a.getLsbD i then acc ^^^ (b.setWidth 16 <<< i) else acc) 0

/-! ## SHA (DDI 0487, J1, "shared/functions/crypto") -/

/-- `SHAchoose(x, y, z) = ((y EOR z) AND x) EOR z`. -/
def shaChoose (x y z : BitVec 32) : BitVec 32 := ((y ^^^ z) &&& x) ^^^ z

/-- `SHAmajority(x, y, z) = ((x AND y) OR ((x OR y) AND z))`. -/
def shaMajority (x y z : BitVec 32) : BitVec 32 := (x &&& y) ||| ((x ||| y) &&& z)

/-- `SHAparity(x, y, z) = (x EOR y EOR z)`. -/
def shaParity (x y z : BitVec 32) : BitVec 32 := x ^^^ y ^^^ z

/-- `SHAhashSIGMA0(x) = ROR(x, 2) EOR ROR(x, 13) EOR ROR(x, 22)`. -/
def shaHashSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- `SHAhashSIGMA1(x) = ROR(x, 6) EOR ROR(x, 11) EOR ROR(x, 25)`. -/
def shaHashSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- One iteration of the loops of SHA1C, SHA1P and SHA1M, with the function
`f` (`SHAchoose`, `SHAparity` or `SHAmajority`), on `(Y, X)`:
`t = f(X<63:32>, X<95:64>, X<127:96>); Y = Y + ROL(X<31:0>, 5) + t +
Elem[W, e, 32]; X<63:32> = ROL(X<63:32>, 30); <Y, X> = ROL(Y:X, 32)`.
The 160-bit rotation leaves `X<127:96>` in `Y` and `X<95:0>:Y` in `X`. -/
def sha1Step (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) (w : BitVec 32)
    (yx : BitVec 32 × BitVec 128) : BitVec 32 × BitVec 128 :=
  let (y, x) := yx
  let t := f (vword x 1) (vword x 2) (vword x 3)
  let y := y + (vword x 0).rotateLeft 5 + t + w
  let x := ofVWords (vword x 0) ((vword x 1).rotateLeft 30) (vword x 2) (vword x 3)
  (vword x 3, ofVWords y (vword x 0) (vword x 1) (vword x 2))

/-- SHA1C, SHA1P, SHA1M: `X = V[d]; Y = V[n]<31:0>; W = V[m]`, then the loop
`for e = 0 to 3` of `sha1Step`, and `V[d] = X`. -/
def sha1Hash (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) (x : BitVec 128)
    (y : BitVec 32) (w : BitVec 128) : BitVec 128 :=
  (sha1Step f (vword w 3) (sha1Step f (vword w 2) (sha1Step f (vword w 1)
    (sha1Step f (vword w 0) (y, x))))).2

/-- SHA1SU0: `result = operand2<63:0> : operand1<127:64>; result = result
EOR operand1 EOR operand3`, where `operand1 = V[d]`, `operand2 = V[n]`,
`operand3 = V[m]`. -/
def sha1Su0 (op1 op2 op3 : BitVec 128) : BitVec 128 :=
  ofVDwords (vdword op1 1) (vdword op2 0) ^^^ op1 ^^^ op3

/-- SHA1SU1: `T = X EOR LSR(Y, 32); W0 = ROL(T<31:0>, 1); W1 = ROL(T<63:32>,
1); W2 = ROL(T<95:64>, 1); W3 = ROL(T<127:96>, 1) EOR ROL(T<31:0>, 2);
V[d] = W3:W2:W1:W0`, where `X = V[d]`, `Y = V[n]`. -/
def sha1Su1 (x y : BitVec 128) : BitVec 128 :=
  let t := x ^^^ (y >>> 32)
  ofVWords ((vword t 0).rotateLeft 1) ((vword t 1).rotateLeft 1) ((vword t 2).rotateLeft 1)
    ((vword t 3).rotateLeft 1 ^^^ (vword t 0).rotateLeft 2)

/-- One iteration of the loop of `SHA256hash(X, Y, W, part1)`:
`chs = SHAchoose(Y<31:0>, Y<63:32>, Y<95:64>); maj = SHAmajority(X<31:0>,
X<63:32>, X<95:64>); t = Y<127:96> + SHAhashSIGMA1(Y<31:0>) + chs +
Elem[W, e, 32]; X<127:96> = t + X<127:96>; Y<127:96> = t +
SHAhashSIGMA0(X<31:0>) + maj; <Y, X> = ROL(Y : X, 32)`. The 256-bit
rotation leaves `Y<95:0>:X<127:96>` in `Y` and `X<95:0>:Y<127:96>` in `X`. -/
def sha256Step (w : BitVec 32) (xy : BitVec 128 × BitVec 128) : BitVec 128 × BitVec 128 :=
  let (x, y) := xy
  let chs := shaChoose (vword y 0) (vword y 1) (vword y 2)
  let maj := shaMajority (vword x 0) (vword x 1) (vword x 2)
  let t := vword y 3 + shaHashSigma1 (vword y 0) + chs + w
  let x3 := t + vword x 3
  let y3 := t + shaHashSigma0 (vword x 0) + maj
  (ofVWords y3 (vword x 0) (vword x 1) (vword x 2),
    ofVWords x3 (vword y 0) (vword y 1) (vword y 2))

/-- `SHA256hash(X, Y, W, part1)`: the loop `for e = 0 to 3` of `sha256Step`,
then `X` if `part1`, else `Y`. -/
def sha256Hash (x y w : BitVec 128) (part1 : Bool) : BitVec 128 :=
  let r := sha256Step (vword w 3) (sha256Step (vword w 2) (sha256Step (vword w 1)
    (sha256Step (vword w 0) (x, y))))
  if part1 then r.1 else r.2

/-- SHA256SU0: `T = operand2<31:0> : operand1<127:32>`; for `e = 0 to 3`:
`elt = Elem[T, e, 32]; elt = ROR(elt, 7) EOR ROR(elt, 18) EOR LSR(elt, 3);
Elem[result, e, 32] = elt + Elem[operand1, e, 32]`, where `operand1 =
V[d]`, `operand2 = V[n]`. -/
def sha256Su0 (op1 op2 : BitVec 128) : BitVec 128 :=
  let t := ofVWords (vword op1 1) (vword op1 2) (vword op1 3) (vword op2 0)
  let f (e : Nat) : BitVec 32 :=
    let elt := vword t e
    (elt.rotateRight 7 ^^^ elt.rotateRight 18 ^^^ elt >>> 3) + vword op1 e
  ofVWords (f 0) (f 1) (f 2) (f 3)

/-- SHA256SU1: `T0 = operand3<31:0> : operand2<127:32>; T1 = operand3<127:64>`;
for `e = 0 to 1`: `elt = Elem[T1, e, 32]; elt = ROR(elt, 17) EOR ROR(elt, 19)
EOR LSR(elt, 10); elt = elt + Elem[operand1, e, 32] + Elem[T0, e, 32];
Elem[result, e, 32] = elt`; then `T1 = result<63:0>` and for `e = 2 to 3`
the same with `Elem[T1, e-2, 32]`. `operand1 = V[d]`, `operand2 = V[n]`,
`operand3 = V[m]`. -/
def sha256Su1 (op1 op2 op3 : BitVec 128) : BitVec 128 :=
  let t0 := ofVWords (vword op2 1) (vword op2 2) (vword op2 3) (vword op3 0)
  let sig (x : BitVec 32) : BitVec 32 := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> 10
  let r0 := sig (vword op3 2) + vword op1 0 + vword t0 0
  let r1 := sig (vword op3 3) + vword op1 1 + vword t0 1
  let r2 := sig r0 + vword op1 2 + vword t0 2
  let r3 := sig r1 + vword op1 3 + vword t0 3
  ofVWords r0 r1 r2 r3

/-- `ROR(x, a) EOR ROR(x, b) EOR ROR(x, c)` on 64 bits. -/
def ror3 (x : BitVec 64) (a b c : Nat) : BitVec 64 :=
  x.rotateRight a ^^^ x.rotateRight b ^^^ x.rotateRight c

/-- SHA512H, with `X = V[n]`, `Y = V[m]`, `W = V[d]`:
`MSigma1 = ROR(Y<127:64>, 14) EOR ROR(Y<127:64>, 18) EOR ROR(Y<127:64>, 41);
Vtmp<127:64> = (Y<127:64> AND X<63:0>) EOR (NOT(Y<127:64>) AND X<127:64>);
Vtmp<127:64> = (Vtmp<127:64> + MSigma1 + W<127:64>); tmp = Vtmp<127:64> +
Y<63:0>; MSigma1 = ROR(tmp, 14) EOR ROR(tmp, 18) EOR ROR(tmp, 41);
Vtmp<63:0> = (tmp AND Y<127:64>) EOR (NOT(tmp) AND X<63:0>); Vtmp<63:0> =
(Vtmp<63:0> + MSigma1 + W<63:0>); V[d] = Vtmp`. -/
def sha512H (w x y : BitVec 128) : BitVec 128 :=
  let y1 := vdword y 1
  let hi := ((y1 &&& vdword x 0) ^^^ (~~~y1 &&& vdword x 1)) + ror3 y1 14 18 41 + vdword w 1
  let tmp := hi + vdword y 0
  let lo := ((tmp &&& y1) ^^^ (~~~tmp &&& vdword x 0)) + ror3 tmp 14 18 41 + vdword w 0
  ofVDwords lo hi

/-- SHA512H2, with `X = V[n]`, `Y = V[m]`, `W = V[d]`:
`NSigma0 = ROR(Y<63:0>, 28) EOR ROR(Y<63:0>, 34) EOR ROR(Y<63:0>, 39);
Vtmp<127:64> = (X<63:0> AND Y<127:64>) EOR (X<63:0> AND Y<63:0>) EOR
(Y<127:64> AND Y<63:0>); Vtmp<127:64> = (Vtmp<127:64> + NSigma0 +
W<127:64>); NSigma0 = ROR(Vtmp<127:64>, 28) EOR ROR(Vtmp<127:64>, 34) EOR
ROR(Vtmp<127:64>, 39); Vtmp<63:0> = (Vtmp<127:64> AND Y<63:0>) EOR
(Vtmp<127:64> AND Y<127:64>) EOR (Y<127:64> AND Y<63:0>); Vtmp<63:0> =
(Vtmp<63:0> + NSigma0 + W<63:0>); V[d] = Vtmp`. -/
def sha512H2 (w x y : BitVec 128) : BitVec 128 :=
  let x0 := vdword x 0
  let y0 := vdword y 0
  let y1 := vdword y 1
  let hi := ((x0 &&& y1) ^^^ (x0 &&& y0) ^^^ (y1 &&& y0)) + ror3 y0 28 34 39 + vdword w 1
  let lo := ((hi &&& y0) ^^^ (hi &&& y1) ^^^ (y1 &&& y0)) + ror3 hi 28 34 39 + vdword w 0
  ofVDwords lo hi

/-- SHA512SU0, with `operand1 = V[d]`, `operand2 = V[n]`:
`sig0 = ROR(operand1<127:64>, 1) EOR ROR(operand1<127:64>, 8) EOR
('0000000':operand1<127:71>); Vtmp<63:0> = operand1<63:0> + sig0;
sig0 = ROR(operand2<63:0>, 1) EOR ROR(operand2<63:0>, 8) EOR
('0000000':operand2<63:7>); Vtmp<127:64> = operand1<127:64> + sig0`. -/
def sha512Su0 (op1 op2 : BitVec 128) : BitVec 128 :=
  let sig (x : BitVec 64) : BitVec 64 := x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ x >>> 7
  ofVDwords (vdword op1 0 + sig (vdword op1 1)) (vdword op1 1 + sig (vdword op2 0))

/-- SHA512SU1, with `operand1 = V[d]`, `operand2 = V[n]`, `operand3 = V[m]`:
`sig1 = ROR(operand2<127:64>, 19) EOR ROR(operand2<127:64>, 61) EOR
('000000':operand2<127:70>); Vtmp<127:64> = operand1<127:64> + sig1 +
operand3<127:64>; sig1 = ROR(operand2<63:0>, 19) EOR ROR(operand2<63:0>, 61)
EOR ('000000':operand2<63:6>); Vtmp<63:0> = operand1<63:0> + sig1 +
operand3<63:0>`. -/
def sha512Su1 (op1 op2 op3 : BitVec 128) : BitVec 128 :=
  let sig (x : BitVec 64) : BitVec 64 := x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ x >>> 6
  ofVDwords (vdword op1 0 + sig (vdword op2 0) + vdword op3 0)
    (vdword op1 1 + sig (vdword op2 1) + vdword op3 1)

/-! ## SM4 (A64 ISA XML 2025-12, shared pseudocode `Sbox`; "SM4E", "SM4EKEY") -/

/-- The constant `sboxstring : bits(2048)` of the shared pseudocode function
`Sbox` ("Used in SM4E crypto instruction"), its sixteen 128-bit rows
concatenated (`::`) in the order the pseudocode lists them, row `F` first
(most significant):
`/*F*/ 0xd690e9fecce13db716b614c228fb2c05[127:0] :: … ::
/*0*/ 0x18f07dec3adc4d2079ee5f3ed7cb3948[127:0]`. -/
def sm4SboxString : BitVec 2048 :=
  (0xd690e9fecce13db716b614c228fb2c05#128 ++ 0x2b679a762abe04c3aa44132649860699#128 ++
   0x9c4250f491ef987a33540b43edcfac62#128 ++ 0xe4b31ca9c908e89580df94fa758f3fa6#128 ++
   0x4707a7fcf37317ba83593c19e6854fa8#128 ++ 0x686b81b27164da8bf8eb0f4b70569d35#128 ++
   0x1e240e5e6358d1a225227c3b01217887#128 ++ 0xd40046579fd327524c3602e7a0c4c89e#128 ++
   0xeabf8ad240c738b5a3f7f2cef96115a1#128 ++ 0xe0ae5da49b341a55ad933230f58cb1e3#128 ++
   0x1df6e22e8266ca60c02923ab0d534e6f#128 ++ 0xd5db3745defd8e2f03ff6a726d6c5b51#128 ++
   0x8d1baf92bbddbc7f11d95c411f105ad8#128 ++ 0x0ac13188a5cd7bbd2d74d012b8e5b4b0#128 ++
   0x8969974a0c96777e65b9f109c56ec684#128 ++ 0x18f07dec3adc4d2079ee5f3ed7cb3948#128 : BitVec 2048)

/-- `Sbox(sboxin)`: `let sboxindex : integer = 255 - UInt(sboxin); sboxout =
sboxstring[sboxindex*:8]` (the 8 bits from bit `8 * sboxindex`). -/
def sm4Sbox (sboxin : BitVec 8) : BitVec 8 :=
  sm4SboxString.extractLsb' (8 * (255 - sboxin.toNat)) 8

/-- `for i = 0 to 3 do intval[i*:8] = Sbox(intval[i*:8]); end`. -/
def sm4SboxWord (x : BitVec 32) : BitVec 32 :=
  sm4Sbox (x.extractLsb' 24 8) ++ sm4Sbox (x.extractLsb' 16 8) ++ sm4Sbox (x.extractLsb' 8 8) ++
    sm4Sbox (x.extractLsb' 0 8)

/-- One iteration of the loop `for index = 0 to 3` of SM4E and SM4EKEY, which
differ only in the line after the S-boxes (`lin`: `intval = intval XOR
ROL(intval, 2) XOR ROL(intval, 10) XOR ROL(intval, 18) XOR ROL(intval, 24)`
for SM4E, `intval = intval XOR ROL(intval, 13) XOR ROL(intval, 23)` for
SM4EKEY), with `k` the iteration's `roundkey = Vn[index*:32]` (SM4E) or
`const = Vm[index*:32]` (SM4EKEY):
`intval = roundresult[127:96] XOR roundresult[95:64] XOR roundresult[63:32]
XOR k; for i = 0 to 3 do intval[i*:8] = Sbox(intval[i*:8]); end; (lin);
intval = intval XOR roundresult[31:0]; roundresult[31:0] =
roundresult[63:32]; roundresult[63:32] = roundresult[95:64];
roundresult[95:64] = roundresult[127:96]; roundresult[127:96] = intval`. -/
def sm4Step (lin : BitVec 32 → BitVec 32) (roundresult : BitVec 128) (k : BitVec 32) : BitVec 128 :=
  let intval := vword roundresult 3 ^^^ vword roundresult 2 ^^^ vword roundresult 1 ^^^ k
  let intval := lin (sm4SboxWord intval)
  let intval := intval ^^^ vword roundresult 0
  ofVWords (vword roundresult 1) (vword roundresult 2) (vword roundresult 3) intval

/-- The four iterations, `index = 0` to `3`, from `roundresult`, with the
words of `ks` in turn. -/
def sm4Steps (lin : BitVec 32 → BitVec 32) (roundresult ks : BitVec 128) : BitVec 128 :=
  sm4Step lin (sm4Step lin (sm4Step lin (sm4Step lin roundresult (vword ks 0)) (vword ks 1))
    (vword ks 2)) (vword ks 3)

/-- SM4E, with `roundresult = V[d]` and the round keys `Vn = V[n]`: the four
iterations with `intval = intval XOR ROL(intval, 2) XOR ROL(intval, 10) XOR
ROL(intval, 18) XOR ROL(intval, 24)`; `V[d] = roundresult`. -/
def sm4E (vd vn : BitVec 128) : BitVec 128 :=
  sm4Steps (fun x => x ^^^ x.rotateLeft 2 ^^^ x.rotateLeft 10 ^^^ x.rotateLeft 18 ^^^ x.rotateLeft 24)
    vd vn

/-- SM4EKEY, with `roundresult = V[n]` and the constants `Vm = V[m]`: the four
iterations with `intval = intval XOR ROL(intval, 13) XOR ROL(intval, 23)`;
`V[d] = roundresult`. -/
def sm4EKey (vn vm : BitVec 128) : BitVec 128 :=
  sm4Steps (fun x => x ^^^ x.rotateLeft 13 ^^^ x.rotateLeft 23) vn vm

/-! ## SM3 (A64 ISA XML 2025-12: "SM3SS1", "SM3TT1A", "SM3TT1B", "SM3TT2A",
"SM3TT2B", "SM3PARTW1", "SM3PARTW2") -/

/-- SM3SS1, with `Vn = V[n]`, `Vm = V[m]`, `Va = V[a]`:
`result[127:96] = ROL((ROL(Vn[127:96], 12) + Vm[127:96] + Va[127:96]), 7);
result[95:0] = Zeros{96}; V[d] = result`. -/
def sm3Ss1 (vn vm va : BitVec 128) : BitVec 128 :=
  ofVWords 0 0 0 (((vword vn 3).rotateLeft 12 + vword vm 3 + vword va 3).rotateLeft 7)

/-- SM3TT1A (`b = false`) and SM3TT1B (`b = true`), with `Vd = V[d]`,
`Vn = V[n]` and `WjPrime = Vm[i*:32]`:
`SS2 = Vn[127:96] XOR ROL(Vd[127:96], 12);`
SM3TT1A: `TT1 = Vd[63:32] XOR (Vd[127:96] XOR Vd[95:64]);`
SM3TT1B: `TT1 = (Vd[127:96] AND Vd[63:32]) OR (Vd[127:96] AND Vd[95:64]) OR
(Vd[63:32] AND Vd[95:64]);`
`TT1 = (TT1 + Vd[31:0] + SS2 + WjPrime)[31:0]; result[31:0] = Vd[63:32];
result[63:32] = ROL(Vd[95:64], 9); result[95:64] = Vd[127:96];
result[127:96] = TT1; V[d] = result`. -/
def sm3Tt1 (b : Bool) (vd vn : BitVec 128) (wjPrime : BitVec 32) : BitVec 128 :=
  let ss2 := vword vn 3 ^^^ (vword vd 3).rotateLeft 12
  let tt1 :=
    if b then (vword vd 3 &&& vword vd 1) ||| (vword vd 3 &&& vword vd 2) ||| (vword vd 1 &&& vword vd 2)
    else vword vd 1 ^^^ (vword vd 3 ^^^ vword vd 2)
  let tt1 := tt1 + vword vd 0 + ss2 + wjPrime
  ofVWords (vword vd 1) ((vword vd 2).rotateLeft 9) (vword vd 3) tt1

/-- SM3TT2A (`b = false`) and SM3TT2B (`b = true`), with `Vd = V[d]`,
`Vn = V[n]` and `Wj = Vm[i*:32]`:
SM3TT2A: `TT2 = Vd[63:32] XOR (Vd[127:96] XOR Vd[95:64]);`
SM3TT2B: `TT2 = (Vd[127:96] AND Vd[95:64]) OR (NOT(Vd[127:96]) AND Vd[63:32]);`
`TT2 = (TT2 + Vd[31:0] + Vn[127:96] + Wj)[31:0]; result[31:0] = Vd[63:32];
result[63:32] = ROL(Vd[95:64], 19); result[95:64] = Vd[127:96];
result[127:96] = TT2 XOR ROL(TT2, 9) XOR ROL(TT2, 17); V[d] = result`. -/
def sm3Tt2 (b : Bool) (vd vn : BitVec 128) (wj : BitVec 32) : BitVec 128 :=
  let tt2 :=
    if b then (vword vd 3 &&& vword vd 2) ||| (~~~(vword vd 3) &&& vword vd 1)
    else vword vd 1 ^^^ (vword vd 3 ^^^ vword vd 2)
  let tt2 := tt2 + vword vd 0 + vword vn 3 + wj
  ofVWords (vword vd 1) ((vword vd 2).rotateLeft 19) (vword vd 3)
    (tt2 ^^^ tt2.rotateLeft 9 ^^^ tt2.rotateLeft 17)

/-- SM3PARTW1, with `Vd = V[d]`, `Vn = V[n]`, `Vm = V[m]`:
`result[95:0] = (Vd XOR Vn)[95:0] XOR (ROL(Vm[127:96], 15)::ROL(Vm[95:64],
15)::ROL(Vm[63:32], 15)); for i = 0 to 3 do if i == 3 then result[127:96] =
(Vd XOR Vn)[127:96] XOR (ROL(result[31:0], 15)); end; result[(32*i)+31:(32*i)]
= (result[(32*i)+31:(32*i)] XOR ROL(result[(32*i)+31:(32*i)], 15) XOR
ROL(result[(32*i)+31:(32*i)], 23)); end; V[d] = result`: word 3 is made
from word 0 after the loop has replaced word 0 (at `i = 0`). -/
def sm3PartW1 (vd vn vm : BitVec 128) : BitVec 128 :=
  let x := vd ^^^ vn
  let p (w : BitVec 32) : BitVec 32 := w ^^^ w.rotateLeft 15 ^^^ w.rotateLeft 23
  let r0 := p (vword x 0 ^^^ (vword vm 1).rotateLeft 15)
  let r1 := p (vword x 1 ^^^ (vword vm 2).rotateLeft 15)
  let r2 := p (vword x 2 ^^^ (vword vm 3).rotateLeft 15)
  let r3 := p (vword x 3 ^^^ r0.rotateLeft 15)
  ofVWords r0 r1 r2 r3

/-- SM3PARTW2, with `Vd = V[d]`, `Vn = V[n]`, `Vm = V[m]`:
`tmp[127:0] = (Vn XOR (ROL(Vm[127:96], 7) :: ROL(Vm[95:64], 7) ::
ROL(Vm[63:32], 7) :: ROL(Vm[31:0], 7))); result[127:0] = Vd[127:0] XOR
tmp[127:0]; tmp2 = ROL(tmp[31:0], 15); tmp2 = tmp2 XOR ROL(tmp2, 15) XOR
ROL(tmp2, 23); result[127:96] = result[127:96] XOR tmp2; V[d] = result`. -/
def sm3PartW2 (vd vn vm : BitVec 128) : BitVec 128 :=
  let tmp := vn ^^^ ofVWords ((vword vm 0).rotateLeft 7) ((vword vm 1).rotateLeft 7)
    ((vword vm 2).rotateLeft 7) ((vword vm 3).rotateLeft 7)
  let result := vd ^^^ tmp
  let tmp2 := (vword tmp 0).rotateLeft 15
  let tmp2 := tmp2 ^^^ tmp2.rotateLeft 15 ^^^ tmp2.rotateLeft 23
  ofVWords (vword result 0) (vword result 1) (vword result 2) (vword result 3 ^^^ tmp2)


end VG.AArch64
