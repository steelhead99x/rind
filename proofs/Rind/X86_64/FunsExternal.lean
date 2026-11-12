module
public import Aeneas
public import Rind.X86_64.Types
public import Rind.X86_64.AesNi
public import Rind.X86_64.AesGcmModel
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
The rind functions the x86_64 translation leaves opaque, beside those
`Rind.X86_64.AesNi` and `Rind.X86_64.AesGcmModel` model. No proof assumes anything about them beyond what
`Rind.X86_64.S2nBignum`, `Rind.X86_64.AwsLc`, and `Rind.X86_64.ValeAesGcm`
state for s2n-bignum's, aws-lc's, and Vale's routines, what
`Rind.X86_64.CtEqual` states for the constant-time compares, and what each theorem
takes as a hypothesis.
-/

namespace rind.x86_64

/-! s2n-bignum's routines, transliterated to inline assembly. -/

opaque low.x86_64.curve25519_x25519base_alt.curve25519_x25519base_alt
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64
    4#usize)

opaque low.x86_64.curve25519_x25519base.curve25519_x25519base
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64
    4#usize)

opaque low.x86_64.sha3_keccak_f1600.sha3_keccak_f1600
  : Array Std.U64 25#usize → Array Std.U64 24#usize → Result (Array Std.U64 25#usize)

opaque low.x86_64.sha3_keccak4_f1600_alt.sha3_keccak4_f1600
  : Array (Array Std.U64 25#usize) 4#usize → Array Std.U64 24#usize → Array Std.U64 4#usize →
    Array Std.U64 4#usize → Result (Array (Array Std.U64 25#usize) 4#usize)

opaque low.x86_64.bignum_eq.bignum_eq
  : Slice Std.U64 → Slice Std.U64 → Result Bool

opaque low.x86_64.curve25519_x25519_alt.curve25519_x25519_alt
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Result (Array Std.U64 4#usize)

opaque low.x86_64.curve25519_x25519.curve25519_x25519
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Result (Array Std.U64 4#usize)

/-! OpenSSL's and aws-lc's SHA-512 routines, behind their Rust wrappers. -/

opaque low.x86_64.sha512.compress_sha512ext
  :
  low.x86_64.cpu.HaveSha512 → Array Std.U64 8#usize → Slice Std.U8 → Result
    (Array Std.U64 8#usize)

opaque low.x86_64.sha512.compress_avx2
  :
  low.x86_64.cpu.HaveAvx2 → Array Std.U64 8#usize → Slice Std.U8 → Result
    (Array Std.U64 8#usize)

opaque low.x86_64.sha512.compress_avx
  :
  low.x86_64.cpu.HaveAvx → Array Std.U64 8#usize → Slice Std.U8 → Result
    (Array Std.U64 8#usize)

opaque low.x86_64.sha512.compress_nohw
  : Array Std.U64 8#usize → Slice Std.U8 → Result (Array Std.U64 8#usize)

/-! Vale's AES-GCM routines, behind their Rust wrappers. -/

opaque low.x86_64.aes_gcm_avx.counter_block
  :
  Std.Array Std.U8 12#usize → Std.Array Std.U8 16#usize →
    Std.Array core.core_arch.x86.__m128i 8#usize → low.x86_64.cpu.HaveAvxMovbeForAesGcm →
    Result (Std.Array Std.U8 16#usize)

opaque low.x86_64.aes_gcm_avx.aead
  (ENC : Bool) :
  low.x86_64.aes.HwKey → Std.Array core.core_arch.x86.__m128i 8#usize →
    low.x86_64.aes_gcm_avx.Buffers → low.x86_64.cpu.HaveAvxMovbeForAesGcm →
    Result (Std.U64 × low.x86_64.aes_gcm_avx.Buffers)

/-! The constant-time compares behind `low::generic::ct_equal`, whose inline
assembly `Rind.X86_64.CtEqual` states HOL Light's theorems about. -/

opaque low.x86_64.cpu.ct_compare_16
  : Array Std.U8 16#usize → Array Std.U8 16#usize → Result Std.Usize

opaque low.x86_64.cpu.ct_compare_bytes : Slice Std.U8 → Slice Std.U8 → Result Std.U8

opaque low.x86_64.vpaes_x86_64.VpaesKey.new
  : Slice Std.U8 → low.x86_64.cpu.HaveSsse3 → Result low.x86_64.vpaes_x86_64.VpaesKey

opaque low.x86_64.vpaes_x86_64.VpaesKey.encrypt_block
  : low.x86_64.vpaes_x86_64.VpaesKey → Std.Array Std.U8 16#usize → Result (Std.Array Std.U8 16#usize)

/-! AES-192's key expansion and block cipher. Vale has no AES-192 routine, so
no proof reaches them. -/

opaque low.x86_64.aes.aes192_expand
  : Std.Array Std.U8 24#usize → Result (Std.Array core.core_arch.x86.__m128i 13#usize)

opaque low.x86_64.aes.aes_block {N : Std.Usize}
  : Std.Array core.core_arch.x86.__m128i N → Std.Array Std.U8 16#usize → Result (Std.Array Std.U8 16#usize)

opaque low.x86_64.aes_nohw.NohwKey.new : Slice Std.U8 → Result low.x86_64.aes_nohw.NohwKey

opaque low.x86_64.aes_nohw.NohwKey.encrypt_block
  : low.x86_64.aes_nohw.NohwKey → Std.Array Std.U8 16#usize → Result (Std.Array Std.U8 16#usize)

opaque low.x86_64.ghash_ssse3_x86_64.Ssse3Table.new
  : Std.Array Std.U8 16#usize → low.x86_64.cpu.HaveSsse3 → Result low.x86_64.ghash_ssse3_x86_64.Ssse3Table

opaque low.x86_64.ghash_nohw.NohwTable.new
  : Std.Array Std.U8 16#usize → Result low.x86_64.ghash_nohw.NohwTable

opaque low.x86_64.ghash.ClmulTable.from_powers
  : Slice core.core_arch.x86.__m128i → low.x86_64.cpu.HaveAesHardware → Result low.x86_64.ghash.ClmulTable

opaque low.x86_64.aes_gcm_vaes.VaesKernel.powers
  : low.x86_64.aes_gcm_vaes.VaesKernel → Result (Slice core.core_arch.x86.__m128i)

opaque low.x86_64.aes_gcm_vaes.VaesKernel.avx512
  : Std.U128 → low.x86_64.cpu.HaveAvx512ForAesGcm → Result low.x86_64.aes_gcm_vaes.VaesKernel

opaque low.x86_64.aes_gcm_vaes.VaesKernel.avx2
  : Std.U128 → low.x86_64.cpu.HaveVaesAvx2ForAesGcm → Result low.x86_64.aes_gcm_vaes.VaesKernel

/-- Wiping a value, which no proof observes: the translation ignores drops. -/
opaque low.generic.zeroise.zeroise_value {T : Type} (ZeroableInst : low.generic.zeroise.Zeroable T) :
  T → Result T

/-! ChaCha20-Poly1305's routines: aws-lc's one-pass seal and open, behind
their Rust wrapper, whose contract `Rind.X86_64.ChaCha20Poly1305`'s `OnePass`
states as a hypothesis, and the separate passes CPUs without SSE4.1 run,
which no theorem is about. -/

opaque low.x86_64.chacha20poly1305.one_pass
  : low.x86_64.cpu.HaveSse41 → Option low.x86_64.cpu.HaveAvx2 → Std.Array Std.U8 32#usize →
    Std.Array Std.U8 12#usize → Slice Std.U8 → Slice Std.U8 → Bool →
    Result ((Std.Array Std.U8 16#usize) × (Slice Std.U8))

opaque low.generic.chacha20poly1305.seal
  : Std.Array Std.U8 32#usize → Std.Array Std.U8 12#usize → Slice Std.U8 → Slice Std.U8 →
    Result ((Std.Array Std.U8 16#usize) × (Slice Std.U8))

opaque low.generic.chacha20poly1305.open
  : Std.Array Std.U8 32#usize → Std.Array Std.U8 12#usize → Slice Std.U8 → Slice Std.U8 →
    Result ((Std.Array Std.U8 16#usize) × (Slice Std.U8))

/-! s2n-bignum's Ed25519 routines, transliterated to inline assembly. -/

opaque low.x86_64.edwards25519_decode.edwards25519_decode
  :
  Array Std.U64 8#usize → Array Std.U8 32#usize → Result (Bool × (Array
    Std.U64 8#usize))

opaque low.x86_64.edwards25519_scalarmulbase.edwards25519_scalarmulbase
  :
  Array Std.U64 8#usize → Array Std.U64 4#usize → Result (Array Std.U64
    8#usize)

opaque low.x86_64.edwards25519_scalarmuldouble.edwards25519_scalarmuldouble
  :
  Array Std.U64 8#usize → Array Std.U64 4#usize → Array Std.U64 8#usize →
    Array Std.U64 4#usize → Result (Array Std.U64 8#usize)

opaque low.x86_64.bignum_madd_n25519.bignum_madd_n25519
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.x86_64.edwards25519_decode_alt.edwards25519_decode_alt
  :
  Array Std.U64 8#usize → Array Std.U8 32#usize → Result (Bool × (Array
    Std.U64 8#usize))

opaque low.x86_64.edwards25519_scalarmulbase_alt.edwards25519_scalarmulbase_alt
  :
  Array Std.U64 8#usize → Array Std.U64 4#usize → Result (Array Std.U64
    8#usize)

opaque low.x86_64.edwards25519_scalarmuldouble_alt.edwards25519_scalarmuldouble_alt
  :
  Array Std.U64 8#usize → Array Std.U64 4#usize → Array Std.U64 8#usize →
    Array Std.U64 4#usize → Result (Array Std.U64 8#usize)

opaque low.x86_64.edwards25519_scalarmuldouble_avx2.edwards25519_scalarmuldouble
  :
  Array Std.U64 8#usize → Array Std.U64 4#usize → Array Std.U64 8#usize →
    Array Std.U64 4#usize → low.x86_64.cpu.HaveAvx2 → Result (Array Std.U64 8#usize)

opaque low.x86_64.bignum_madd_n25519_alt.bignum_madd_n25519_alt
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.x86_64.bignum_mod_n25519.bignum_mod_n25519
  : Array Std.U64 4#usize → Slice Std.U64 → Result (Array Std.U64 4#usize)

opaque low.x86_64.bignum_neg_p25519.bignum_neg_p25519
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64
    4#usize)

opaque low.x86_64.bignum_cmp_lt.bignum_cmp_lt
  : Slice Std.U64 → Slice Std.U64 → Result Std.U64

/-! The wipe a drop runs, which no theorem calls. -/

opaque low.generic.zeroise.zeroise
  {T : Type _} (ZeroableInst : low.generic.zeroise.Zeroable T) :
  Slice T → Result (Slice T)

/-- `ZeroableRef::new`, as `Rind.X86_64.Dispatch` models a `ZeroableRef`: its
value. -/
def low.generic.zeroise.ZeroableRef.new {T : Type} (value : T) :
    Result (low.generic.zeroise.ZeroableRef T) :=
  ok value

/-! The entry guard and CPU dispatch, which read no input. -/

opaque low.entry.Entry.new_secret : Result low.entry.Entry

opaque low.entry.Entry.new_public : Result low.entry.Entry

/-- Whether an entry guard is held, which a debug build asserts. -/
opaque low.entry.Entry.assert_held : Result Unit

opaque low.x86_64.sha512.path : Result low.x86_64.sha512.Path

opaque low.x86_64.cpu.HaveBmi2Adx.check
  : Result (Option low.x86_64.cpu.HaveBmi2Adx)

opaque low.x86_64.cpu.HaveAvx2.check : Result (Option low.x86_64.cpu.HaveAvx2)

opaque low.x86_64.cpu.HaveAesHardware.check : Result (Option low.x86_64.cpu.HaveAesHardware)

opaque low.x86_64.cpu.HaveAvxMovbeForAesGcm.check
  : Result (Option low.x86_64.cpu.HaveAvxMovbeForAesGcm)

opaque low.x86_64.cpu.HaveVaesAvx2ForAesGcm.check
  : Result (Option low.x86_64.cpu.HaveVaesAvx2ForAesGcm)

opaque low.x86_64.cpu.HaveAvx512ForAesGcm.check
  : Result (Option low.x86_64.cpu.HaveAvx512ForAesGcm)

opaque low.x86_64.cpu.HaveVaesAvx2ForAesGcm.avx_movbe
  : low.x86_64.cpu.HaveVaesAvx2ForAesGcm → Result low.x86_64.cpu.HaveAvxMovbeForAesGcm

opaque low.x86_64.cpu.HaveSsse3.check : Result (Option low.x86_64.cpu.HaveSsse3)

opaque low.x86_64.cpu.HaveSse41.check : Result (Option low.x86_64.cpu.HaveSse41)

/-- The SHA-1 and SHA-256 routines the CPU runs, each picked once. -/
opaque low.x86_64.sha1_mux.path : Result low.x86_64.sha1_mux.Path

opaque low.x86_64.sha256_mux.path : Result low.x86_64.sha256_mux.Path

/-! SHA-1 and SHA-256's block and finishing functions, whose contracts `Rind.X86_64.ShaBlocks`
states as hypotheses. SHA-1's block function is its whole dispatch, which `Sha1Blocks` states
as one. -/

opaque low.x86_64.sha1_mux.sha1_compress_blocks
  : Array Std.U32 5#usize → Slice Std.U8 → Result (Array Std.U32 5#usize)

opaque low.x86_64.sha1.sha1_compress_padded_shaext
  : Array Std.U32 5#usize → Slice Std.U8 → Array Std.U8 8#usize → low.x86_64.cpu.HaveSha1 →
    Result (Array Std.U32 5#usize)

opaque low.x86_64.sha256.sha256_compress_blocks_shaext
  : Array Std.U32 8#usize → Slice Std.U8 → low.x86_64.cpu.HaveSha256 →
    Result (Array Std.U32 8#usize)

opaque low.x86_64.sha256.sha256_finish_shaext
  : Array Std.U32 8#usize → Slice Std.U8 → Array Std.U8 8#usize → low.x86_64.cpu.HaveSha256 →
    Result (Array Std.U8 32#usize)

opaque low.x86_64.sha256.sha256_compress_blocks_avx
  : Array Std.U32 8#usize → Slice Std.U8 → low.x86_64.cpu.HaveAvx → Result (Array Std.U32 8#usize)

opaque low.x86_64.sha256.sha256_compress_blocks_avx2
  : Array Std.U32 8#usize → Slice Std.U8 → low.x86_64.cpu.HaveAvx2 → Result (Array Std.U32 8#usize)

opaque low.x86_64.sha256.sha256_compress_blocks_ssse3
  : Array Std.U32 8#usize → Slice Std.U8 → low.x86_64.cpu.HaveSsse3 →
    Result (Array Std.U32 8#usize)

opaque low.x86_64.sha256.sha256_compress_blocks_nohw
  : Array Std.U32 8#usize → Slice Std.U8 → Result (Array Std.U32 8#usize)

/-! P-384's s2n-bignum routines, its table select, and `bignum_mux`. -/

opaque low.x86_64.bignum_add_p384.bignum_add_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Array Std.U64 6#usize →
    Result (Array Std.U64 6#usize)

opaque low.x86_64.bignum_demont_p384.bignum_demont_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.bignum_demont_p384_alt.bignum_demont_p384_alt
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.bignum_inv_p384.bignum_inv_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.bignum_montmul_p384.bignum_montmul_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Array Std.U64 6#usize →
    Result (Array Std.U64 6#usize)

opaque low.x86_64.bignum_montmul_p384_alt.bignum_montmul_p384_alt
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Array Std.U64 6#usize →
    Result (Array Std.U64 6#usize)

opaque low.x86_64.bignum_montsqr_p384.bignum_montsqr_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.bignum_montsqr_p384_alt.bignum_montsqr_p384_alt
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.bignum_mux.bignum_mux
  :
  Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Result
    (Slice Std.U64)

opaque low.x86_64.bignum_neg_p384.bignum_neg_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.bignum_point_select.bignum_aff_point_select_p384
  :
  Array Std.U64 12#usize → Slice Std.U64 → Std.U8 → Result (Array Std.U64
    12#usize)

opaque low.x86_64.bignum_tomont_p384.bignum_tomont_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.bignum_tomont_p384_alt.bignum_tomont_p384_alt
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.p384_montjdouble.p384_montjdouble
  :
  Array Std.U64 18#usize → Array Std.U64 18#usize → Result (Array Std.U64
    18#usize)

opaque low.x86_64.p384_montjdouble_alt.p384_montjdouble_alt
  :
  Array Std.U64 18#usize → Array Std.U64 18#usize → Result (Array Std.U64
    18#usize)

opaque low.x86_64.p384_montjmixadd.p384_montjmixadd
  :
  Array Std.U64 18#usize → Array Std.U64 18#usize → Array Std.U64 12#usize
    → Result (Array Std.U64 18#usize)

opaque low.x86_64.p384_montjmixadd_alt.p384_montjmixadd_alt
  :
  Array Std.U64 18#usize → Array Std.U64 18#usize → Array Std.U64 12#usize
    → Result (Array Std.U64 18#usize)

opaque low.x86_64.p384_montjscalarmul.p384_montjscalarmul
  :
  Array Std.U64 18#usize → Array Std.U64 6#usize → Array Std.U64 18#usize
    → Result (Array Std.U64 18#usize)

opaque low.x86_64.p384_montjscalarmul_alt.p384_montjscalarmul_alt
  :
  Array Std.U64 18#usize → Array Std.U64 6#usize → Array Std.U64 18#usize
    → Result (Array Std.U64 18#usize)

opaque high.sec1.decode
  : Slice Std.U8 → high.asn1.ObjectId → Result (core.result.Result high.sec1.Decoded error.Error)

opaque high.sec1.decode_pkcs8
  : Slice Std.U8 → high.asn1.ObjectId → Result (core.result.Result high.sec1.Decoded error.Error)

opaque low.x86_64.bignum_mod_n384.bignum_mod_n384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque high.curve.P384.Insts.RindHighCurveCurveStaticPrivateKeyVerifyingKeyScalar.oid
  : Result high.asn1.ObjectId

/-! The other curves, which X25519's results never depend on. -/

opaque mid.p521.PrivateKey.new_random
  : Result (core.result.Result mid.p521.PrivateKey error.Error)

opaque mid.p384.PrivateKey.new_random
  : Result (core.result.Result mid.p384.PrivateKey error.Error)

opaque mid.p256.PrivateKey.new_random
  : Result (core.result.Result mid.p256.PrivateKey error.Error)

opaque mid.p521.PrivateKey.public_key_uncompressed
  : mid.p521.PrivateKey → Result (Array Std.U8 133#usize)

opaque mid.p256.PrivateKey.public_key_uncompressed
  : mid.p256.PrivateKey → Result (Array Std.U8 65#usize)

opaque mid.p521.PrivateKey.diffie_hellman
  :
  mid.p521.PrivateKey → mid.p521.PublicKey → Result (core.result.Result
    mid.p521.SharedSecret error.Error)

opaque mid.p521.PublicKey.from_x962_uncompressed
  : Slice Std.U8 → Result (core.result.Result mid.p521.PublicKey error.Error)

opaque mid.p256.PrivateKey.diffie_hellman
  :
  mid.p256.PrivateKey → mid.p256.PublicKey → Result (core.result.Result
    mid.p256.SharedSecret error.Error)

opaque mid.p256.PublicKey.from_x962_uncompressed
  : Slice Std.U8 → Result (core.result.Result mid.p256.PublicKey error.Error)

/-! MD5, which no proof covers. -/

opaque mid.md5.Md5State.new : Result mid.md5.Md5State

opaque mid.md5.Md5State.finish_with
  : mid.md5.Md5State → Slice Std.U8 → Result (Array Std.U8 16#usize)

opaque mid.md5.Md5Context.new : Result mid.md5.Md5Context

opaque mid.md5.Md5Context.update : mid.md5.Md5Context → Slice Std.U8 → Result mid.md5.Md5Context

opaque mid.md5.Md5Context.finish : mid.md5.Md5Context → Result (Array Std.U8 16#usize)

opaque mid.md5.Md5Context.Insts.CoreCloneClone.clone : mid.md5.Md5Context → Result mid.md5.Md5Context

/-! Agreement key encodings, and loading on the curves no theorem loads a key
on, whose DER no proof covers. -/

opaque high.agreement.x25519_from_pkcs8
  : high.agreement.Algorithm → Slice Std.U8 →
    Result (core.result.Result (mid.x25519.PrivateKey × high.agreement.PublicKey) error.Error)

opaque high.agreement.X25519Curve.Insts.RindHighAgreementAgreePrivateKey.encode_pkcs8
  : mid.x25519.PrivateKey → Slice Std.U8 → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.agreement.X25519Curve.Insts.RindHighAgreementAgreePrivateKey.encode_scalar
  : mid.x25519.PrivateKey → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.curve.P256.Insts.RindHighAgreementAgreePrivateKey.encode_pkcs8
  : mid.p256.PrivateKey → Slice Std.U8 → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.curve.P256.Insts.RindHighAgreementAgreePrivateKey.encode_scalar
  : mid.p256.PrivateKey → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.curve.P384.Insts.RindHighAgreementAgreePrivateKey.encode_pkcs8
  : mid.p384.PrivateKey → Slice Std.U8 → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.curve.P384.Insts.RindHighAgreementAgreePrivateKey.encode_scalar
  : mid.p384.PrivateKey → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.curve.P521.Insts.RindHighAgreementAgreePrivateKey.encode_pkcs8
  : mid.p521.PrivateKey → Slice Std.U8 → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.curve.P521.Insts.RindHighAgreementAgreePrivateKey.encode_scalar
  : mid.p521.PrivateKey → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.curve.P521.Insts.RindHighAgreementAgreePrivateKey.load
  : high.agreement.Algorithm → high.agreement.Source →
    Result (core.result.Result (mid.p521.PrivateKey × high.agreement.PublicKey) error.Error)

opaque high.curve.P256.Insts.RindHighAgreementAgreePrivateKey.load
  : high.agreement.Algorithm → high.agreement.Source →
    Result (core.result.Result (mid.p256.PrivateKey × high.agreement.PublicKey) error.Error)

/-! s2n-bignum's routines for RSA, transliterated to inline assembly. -/

opaque low.x86_64.bignum_negmodinv.bignum_negmodinv
  : Slice Std.U64 → Slice Std.U64 → Result (Slice Std.U64)

opaque low.x86_64.bignum_bitsize.bignum_bitsize
  : Slice Std.U64 → Result Std.Usize

opaque low.x86_64.bignum_optsub.bignum_optsub
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Std.U64 → Result
    (Slice Std.U64)

opaque low.x86_64.bignum_emontredc_8n.bignum_emontredc_8n
  :
  Slice Std.U64 → Slice Std.U64 → Std.U64 → Result (Std.U64 × (Slice
    Std.U64))

opaque low.x86_64.bignum_kmul_16_32.bignum_kmul_16_32
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Array Std.U64 32#usize
    → Result ((Slice Std.U64) × (Array Std.U64 32#usize))

opaque low.x86_64.bignum_kmul_32_64.bignum_kmul_32_64
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Array Std.U64 96#usize
    → Result ((Slice Std.U64) × (Array Std.U64 96#usize))

opaque low.x86_64.bignum_ksqr_16_32.bignum_ksqr_16_32
  :
  Slice Std.U64 → Slice Std.U64 → Array Std.U64 24#usize → Result ((Slice
    Std.U64) × (Array Std.U64 24#usize))

opaque low.x86_64.bignum_ksqr_32_64.bignum_ksqr_32_64
  :
  Slice Std.U64 → Slice Std.U64 → Array Std.U64 72#usize → Result ((Slice
    Std.U64) × (Array Std.U64 72#usize))

opaque low.x86_64.bignum_montmul.bignum_montmul
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 →
    Result (Slice Std.U64)

/-! aws-lc's Montgomery products, behind their Rust wrappers, which
`Rind.X86_64.RsaMont`'s `AwsLcMont` states for the theorems that need them. -/

opaque low.x86_64.mont.nohw
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 →
    Std.U64 → Result (Slice Std.U64)

opaque low.x86_64.mont.mul4x
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 →
    Std.U64 → Option low.x86_64.cpu.HaveBmi2Adx → Result (Slice Std.U64)

opaque low.x86_64.mont.sqr8x
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Std.U64 → Option
    low.x86_64.cpu.HaveBmi2Adx → Result (Slice Std.U64)

/-! RSA's DER parsing and encoding, which the ✓ leaves out. -/

opaque high.rsa.der_components
  :
  Slice Std.U8 → Result (core.result.Result ((Slice Std.U8) × (Slice
    Std.U8)) error.Error)

opaque high.rsa.VerifyingKey.to_pkcs1_der
  :
  high.rsa.VerifyingKey → Slice Std.U8 → Result ((core.result.Result (Slice
    Std.U8) error.Error) × (Slice Std.U8))

end rind.x86_64
