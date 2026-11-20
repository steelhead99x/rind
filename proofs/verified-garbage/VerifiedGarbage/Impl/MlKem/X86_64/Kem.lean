module

public import VerifiedGarbage.Impl.MlKem.X86_64.Frag
public import VerifiedGarbage.Spec.MlKem.Contract

/-!
# ML-KEM on x86-64: what a parameter set fixes of the top-level functions

The key generation, encapsulation and decapsulation of ML-KEM-768 and
ML-KEM-1024 are the same code (`KeyGen.lean`, `Encrypt.lean`, `EncapsH.lean`,
`Decaps.lean`) for a `Kem`: the rank `k` and the widths `d_u` and `d_v` of
the parameter set, the size of `scratch`, where the matrix, the outputs of
`PRF₂`, the working space of their computation and the ciphertext of the
re-encryption are among its polynomials (`Frag.lean`), and the compression
the widths `d_u` and `d_v` call. Loops over `k` are unrolled: `Â[i, j]` is
polynomial `pA + k i + j`, sampled four entries at a time and then one at a
time (`samples`), and a sum of `k` products is accumulated left to right
(`dotN`).
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- What a parameter set fixes of the top-level functions. -/
structure Kem where
  /-- The parameter set (FIPS 203 Table 2): the rank `k`, and the widths
  `d_u` and `d_v`. -/
  p : Spec.MlKem.Params
  /-- The size of `scratch`, in bytes. -/
  scr : Nat
  /-- The polynomials of `Â` (from `pA`), of the working space of
  `vg_mlkem_sample_ntt4` and of `prfs` (from `pW`), of the outputs of `PRF₂`
  (from `pPR`), and of the ciphertext of the re-encryption (from `pCT`). -/
  pA : Nat
  pW : Nat
  pPR : Nat
  pCT : Nat
  /-- The `k + 1` polynomials of `u` and `v` before the errors (from `pU`),
  and the working space of `vg_mlkem*_encrypt_mul` (4 polynomials, from
  `pZ`). -/
  pU : Nat
  pZ : Nat
  /-- The compression and decompression to `d_u` and `d_v`, for the
  implementations `cs` of `vg_mlkem_compress_encode` and
  `vg_mlkem_decode_decompress`. -/
  ceN : Codecs → String
  ce : Codecs → Prog isa
  ddN : Codecs → String
  dd : Codecs → Prog isa
  /-- The compressions to `d_u` and to `d_v` of `vg_mlkem*_kpke_encrypt`, which
  runs them in an MXCSR region. -/
  ceU : Prog isa
  ceV : Prog isa

namespace Kem

variable (L : Kem)

abbrev k : Nat := L.p.k
abbrev du : Nat := L.p.du
abbrev dv : Nat := L.p.dv

/-- The lengths of the encapsulation key, the decapsulation key and the ciphertext. -/
abbrev ekLen : Nat := L.p.ekLen
abbrev dkLen : Nat := L.p.dkLen
abbrev ctLen : Nat := L.p.ctLen

/-- The outputs of `PRF₂` (128 bytes each). -/
def oPR : Nat := oP L.pPR
/-- The working space of `prfs` (2368 bytes), as a lane (32 bytes). -/
def lPW : Nat := oP L.pW / 32
/-- The ciphertext of the re-encryption. -/
def oCT : Nat := oP L.pCT

/-- `Â[i, j]`: polynomial `pA + k i + j`. -/
abbrev aS (i j : Nat) : Ptr := pS (L.pA + L.k * i + j)

/-- `ByteEncode_d(Compress_d(f))` to `out`, for `d = d_u` or `d_v`. -/
def ceAt (cs : Codecs) (f : Ptr) (d : Nat) (out : Ptr) : Prog isa := ceCall (L.ceN cs) (L.ce cs) f d out

/-- `NTT⁻¹(ŝ^⊺ ∘ NTT(u'))` to `w`, for the `k` polynomials `ŝ` from `s` and
`u'` from `u`, with the working space `z` (4096 bytes):
`vg_mlkem*_decrypt_mul`, with the arithmetic of `A`. -/
def decMulAt (A : Arith) (w s u z : Ptr) : Prog isa :=
  .seq (.block (lea .rdi w ++ lea .rsi s ++ lea .rdx u ++ lea .rcx z))
    (.call (L.p.fn "decrypt_mul" ++ A.sfx) (A.decMul L.k))

/-- `NTT⁻¹(Â^⊺ ∘ NTT(y))` and `NTT⁻¹(t̂^⊺ ∘ NTT(y))` to the `k + 1`
polynomials from `u`, for the `k²` polynomials of `Â` from `a` and the `k`
of `t̂` from `t` and of `y` from `y`, with the working space `z` (4096
bytes): `vg_mlkem*_encrypt_mul`, with the arithmetic of `A`. -/
def encMulAt (A : Arith) (u a t y z : Ptr) : Prog isa :=
  .seq (.block (lea .rdi u ++ lea .rsi a ++ lea .rdx t ++ lea .rcx y ++ lea .r8 z))
    (.call (L.p.fn "encrypt_mul" ++ A.sfx) (A.encMul L.k))

/-- `ŝ = NTT(s)` in place and `t̂ = Â ∘ ŝ + NTT(e)` to the `k` polynomials
from `t`, for the `k` polynomials of `s` from `s` and of `e` from `e` and
the `k²` of `Â` from `a`, with the working space `z` (4096 bytes):
`vg_mlkem*_keygen_mul`, with the arithmetic of `A`. -/
def kgMulAt (A : Arith) (t s a e z : Ptr) : Prog isa :=
  .seq (.block (lea .rdi t ++ lea .rsi s ++ lea .rdx a ++ lea .rcx e ++ lea .r8 z))
    (.call (L.p.fn "keygen_mul" ++ A.sfx) (keygenMul A.bodies L.k))

/-- `Decompress_d(ByteDecode_d(b))` to `f`, for `d = d_u` or `d_v`. -/
def ddAt (cs : Codecs) (b : Ptr) (d : Nat) (f : Ptr) : Prog isa := ddCall (L.ddN cs) (L.dd cs) b d f

/-- Entries `e, …, e + n - 1` of `Â` (entry `e = k i + j`), four at a time
(with `pW` as the working space) and the last `n mod 4` one at a time. -/
def ents (c : Callee4) : Nat → Nat → Prog isa
  | e, n + 5 => .seq (quad c L.k e (pS (L.pA + e)) (pS L.pW)) (ents c (e + 4) (n + 1))
  | e, 4 => quad c L.k e (pS (L.pA + e)) (pS L.pW)
  | e, n + 2 => .seq (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)) (ents c (e + 1) (n + 1))
  | e, 1 => sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)
  | _, 0 => .block []

/-- The `k²` entries of `Â`. -/
def samples (c : Callee4) : Prog isa := L.ents c 0 (L.k * L.k)

end Kem

/-- ML-KEM-768: `k = 3`, `d_u = 10`, `d_v = 4`; 28 polynomials in `scratch`:
`Â` in polynomials 6–14, the working space from 17, the outputs of `PRF₂`
in 20, and the ciphertext (1088 bytes) in 26 and 27; in encryption, `u` and
`v` in 16–19 and the working space of `vg_mlkem768_encrypt_mul` in 21–24. -/
def kem768 : Kem where
  p := Spec.MlKem.mlKem768
  scr := 32768
  pA := 6
  pW := 17
  pPR := 20
  pCT := 26
  pU := 16
  pZ := 21
  ceN := Codecs.ceN
  ce := Codecs.ce
  ddN := Codecs.ddN
  dd := Codecs.dd
  ceU := cm10
  ceV := cm4

end VG.Impl.MlKem.X86_64
