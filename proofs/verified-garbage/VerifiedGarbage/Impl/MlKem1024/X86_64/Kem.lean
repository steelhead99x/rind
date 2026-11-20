module

public import VerifiedGarbage.Impl.MlKem.X86_64.DecapsJ16
public import VerifiedGarbage.Impl.MlKem.X86_64.Encaps16
public import VerifiedGarbage.Impl.MlKem.X86_64.CheckEk
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Compress
public import VerifiedGarbage.Impl.MlKem1024.X86_64.CompressAvx2

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_keygen`, `vg_mlkem1024_encaps_h`, `vg_mlkem1024_decaps` and `vg_mlkem1024_check_ek`

The key generation, encapsulation and decapsulation of ML-KEM
(`Impl/MlKem/X86_64/`) for ML-KEM-1024 (`kem1024`): `k = 4`, `d_u = 11`
and `d_v = 5`, which `vg_mlkem1024_compress_encode` and
`vg_mlkem1024_decode_decompress` (`Compress.lean`) take, or, with the
implementations `Codecs.avx2`, `vg_mlkem1024_compress_encode_avx2` and
`vg_mlkem1024_decode_decompress_avx2` (`CompressAvx2.lean`). The 16 entries of
`Â` are polynomials 17–32 of the working space (`Â[i, j]` is polynomial
`17 + 4i + j`), after the accumulator (polynomial 15) and the products
(polynomial 16), and the ciphertext of the re-encryption (1568 bytes) is in
polynomials 33 and 34; the outputs of `PRF₂` are in polynomials 38 and 39,
and the working space of their computation and of `vg_mlkem_sample_ntt4`
from polynomial 35; in encryption, `u` and `v` are in polynomials 8–12 and
the working space of `vg_mlkem1024_encrypt_mul` in 40–43. `scratch` is 48
KiB (44 polynomials).
-/

@[expose] public section

namespace VG.Impl.MlKem1024.X86_64

open VG.X86_64 VG.Impl.MlKem.X86_64

/-- The compression and decompression of ML-KEM-1024's widths that go with the
implementations `cs` of ML-KEM-768's (`Codecs`): the baseline ones, or those
with AVX2. -/
def ceN1024 : Codecs → String
  | .base => "vg_mlkem1024_compress_encode"
  | .avx2 => "vg_mlkem1024_compress_encode_avx2"

def ce1024 : Codecs → Prog isa
  | .base => compressEncode1024
  | .avx2 => compressEncode1024Avx2

def ddN1024 : Codecs → String
  | .base => "vg_mlkem1024_decode_decompress"
  | .avx2 => "vg_mlkem1024_decode_decompress_avx2"

def dd1024 : Codecs → Prog isa
  | .base => decodeDecompress1024
  | .avx2 => decodeDecompress1024Avx2

/-- ML-KEM-1024. -/
def kem1024 : Kem where
  p := Spec.MlKem.mlKem1024
  scr := 49152
  pA := 17
  pW := 35
  pPR := 38
  pCT := 33
  pU := 8
  pZ := 40
  ceN := ceN1024
  ce := ce1024
  ddN := ddN1024
  dd := dd1024
  ceU := cm11
  ceV := cm5

/-- ML-KEM-1024's layout with 16-bit polynomials: `Â` 8192 bytes from 4096,
the others (at most 4608 bytes) from 12288, and the K-PKE functions' working
space (20480 bytes) from 16896. -/
def kem1024w : Kem16 where
  L := kem1024
  oA := 4096
  oR := 12288
  oZ := 16896
  oW := 16896
  oPR := 25088

abbrev keyGen1024 (c : Callee4) : Prog isa := kemKeyGenSel kem1024w c
abbrev encapsH1024 (c : Callee4) : Prog isa := kemEncapsHSel kem1024w c
abbrev encaps1024 (c : Callee4) : Prog isa := kemEncapsSel kem1024w c
abbrev decaps1024 (c : Callee4) : Prog isa := kemDecapsSel kem1024w c
abbrev checkEk1024 : Prog isa := checkEkK 4

end VG.Impl.MlKem1024.X86_64
