module
public import Aeneas
public import Rind.Aarch64.Types
public import Rind.Aarch64.Neon
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
The rind functions the aarch64 translation leaves opaque. No proof assumes anything
about them beyond what `Rind.Aarch64.S2nBignum` and `Rind.Aarch64.AwsLc` state for
s2n-bignum's and aws-lc's routines and what each theorem takes as a hypothesis.
-/

namespace rind.aarch64

/-! s2n-bignum's routines, transliterated to inline assembly. -/

opaque low.aarch64.curve25519_x25519base.curve25519_x25519base
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64
    4#usize)

opaque low.aarch64.curve25519_x25519.curve25519_x25519
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Result (Array Std.U64 4#usize)

opaque low.aarch64.sha3_keccak_f1600.sha3_keccak_f1600
  : Array Std.U64 25#usize → Array Std.U64 24#usize → Result (Array Std.U64 25#usize)

opaque low.aarch64.sha3_keccak_f1600_alt.sha3_keccak_f1600
  : Array Std.U64 25#usize → Array Std.U64 24#usize → Result (Array Std.U64 25#usize)

opaque low.aarch64.sha3_keccak2_f1600.sha3_keccak2_f1600
  : Array (Array Std.U64 25#usize) 2#usize → Array Std.U64 24#usize →
    Result (Array (Array Std.U64 25#usize) 2#usize)

opaque low.aarch64.bignum_eq.bignum_eq
  : Slice Std.U64 → Slice Std.U64 → Result Bool

opaque low.aarch64.bignum_tomont_p256.bignum_tomont_p256
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.aarch64.bignum_demont_p256.bignum_demont_p256
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.aarch64.bignum_add_p256.bignum_add_p256
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Result (Array Std.U64 4#usize)

opaque low.aarch64.bignum_montmul_p256.bignum_montmul_p256
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Result (Array Std.U64 4#usize)

opaque low.aarch64.bignum_montsqr_p256.bignum_montsqr_p256
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.aarch64.bignum_mod_n256.bignum_mod_n256
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.aarch64.p256_scalarmul.p256_scalarmul
  :
  Array Std.U64 8#usize → Array Std.U64 4#usize → Array Std.U64 8#usize →
    Result (Array Std.U64 8#usize)

opaque low.aarch64.p256_scalarmulbase.p256_scalarmulbase
  :
  Array Std.U64 8#usize → Array Std.U64 4#usize → Array (Array Std.U64
    256#usize) 43#usize → Result (Array Std.U64 8#usize)

opaque low.aarch64.bignum_inv_p256.bignum_inv_p256
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.aarch64.bignum_neg_p256.bignum_neg_p256
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.aarch64.p256_montjadd.p256_montjadd
  :
  Array Std.U64 12#usize → Array Std.U64 12#usize → Array Std.U64 12#usize →
    Result (Array Std.U64 12#usize)

opaque low.aarch64.p256_montjdouble.p256_montjdouble
  : Array Std.U64 12#usize → Array Std.U64 12#usize → Result (Array Std.U64 12#usize)

opaque low.aarch64.p256_montjmixadd.p256_montjmixadd
  :
  Array Std.U64 12#usize → Array Std.U64 12#usize → Array Std.U64 8#usize →
    Result (Array Std.U64 12#usize)

opaque low.aarch64.bignum_modadd.bignum_modadd
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 →
    Result (Slice Std.U64)

opaque low.aarch64.bignum_montmul.bignum_montmul
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 →
    Result (Slice Std.U64)

opaque low.aarch64.bignum_demont.bignum_demont
  : Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Result (Slice Std.U64)

opaque low.aarch64.bignum_modinv.bignum_modinv
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 →
    Result ((Slice Std.U64) × (Slice Std.U64))

/-! P-256's key generation, which draws through a `dyn RandomSource`:
`Rind.Aarch64.P256Dispatch` models it. -/

opaque mid.p256.PrivateKey.new_random
  : Result (core.result.Result mid.p256.PrivateKey error.Error)

/-! aws-lc's SHA-512 routines, behind their Rust wrappers. -/

opaque low.aarch64.sha512.compress_hw
  :
  low.aarch64.cpu.HaveSha3 → Array Std.U64 8#usize → Slice Std.U8 → Result
    (Array Std.U64 8#usize)

opaque low.aarch64.sha512.compress_nohw
  : Array Std.U64 8#usize → Slice Std.U8 → Result (Array Std.U64 8#usize)

/-! s2n-bignum's Ed25519 routines, transliterated to inline assembly. -/

opaque low.aarch64.edwards25519_decode.edwards25519_decode
  :
  Array Std.U64 8#usize → Array Std.U8 32#usize → Result (Bool × (Array
    Std.U64 8#usize))

opaque low.aarch64.edwards25519_scalarmulbase.edwards25519_scalarmulbase
  :
  Array Std.U64 8#usize → Array Std.U64 4#usize → Result (Array Std.U64
    8#usize)

opaque low.aarch64.edwards25519_scalarmuldouble.edwards25519_scalarmuldouble
  :
  Array Std.U64 8#usize → Array Std.U64 4#usize → Array Std.U64 8#usize →
    Array Std.U64 4#usize → Result (Array Std.U64 8#usize)

opaque low.aarch64.bignum_madd_n25519.bignum_madd_n25519
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.aarch64.bignum_mod_n25519.bignum_mod_n25519
  : Array Std.U64 4#usize → Slice Std.U64 → Result (Array Std.U64 4#usize)

opaque low.aarch64.bignum_neg_p25519.bignum_neg_p25519
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64
    4#usize)

opaque low.aarch64.bignum_cmp_lt.bignum_cmp_lt
  : Slice Std.U64 → Slice Std.U64 → Result Std.U64

/-! P-256's ECDSA key generation, which the signing theorems model, and its
PKCS#8 OID, which none states. -/

opaque high.curve.P256.Insts.RindHighCurveCurveStaticPrivateKeyVerifyingKeyScalar.generate_random_key
  {T0 : Type _} (midrngRandomSourceInst : mid.rng.RandomSource T0) :
  T0 → Result ((core.result.Result mid.p256.StaticPrivateKey error.Error) × T0)

opaque high.curve.P256.Insts.RindHighCurveCurveStaticPrivateKeyVerifyingKeyScalar.oid
  : Result high.asn1.ObjectId

/-! The HMAC-DRBG an ECDSA signature draws its nonces from. -/

opaque high.hmac_drbg.HmacDrbg.new
  {H : Type _} {Clause0_Context : Type _} {Clause0_State : Type _}
  (hashHashInst : high.hash.Hash H Clause0_Context Clause0_State) :
  Slice Std.U8 → Slice Std.U8 → Slice Std.U8 →
    Result (high.hmac_drbg.HmacDrbg H Clause0_Context Clause0_State)

opaque high.hmac_drbg.HmacDrbg.Insts.RindMidRngRandomSource.fill
  {H : Type _} {Clause0_Context : Type _} {Clause0_State : Type _}
  (hashHashInst : high.hash.Hash H Clause0_Context Clause0_State) :
  high.hmac_drbg.HmacDrbg H Clause0_Context Clause0_State → Slice Std.U8 →
    Result ((core.result.Result Unit error.Error) × (high.hmac_drbg.HmacDrbg H
    Clause0_Context Clause0_State) × (Slice Std.U8))

/-! The verifying key's caches of P, ..., 15P and 17P, ..., 31P, which ECDSA
verification's theorems take what they need of as a hypothesis. -/

opaque low.generic.reuse_cache.ReuseCache.new
  {T : Type _} (coremarkerCopyInst : core.marker.Copy T)
  (coredefaultDefaultInst : core.default.Default T) :
  Result (low.generic.reuse_cache.ReuseCache T)

opaque low.generic.reuse_cache.ReuseCache.get_or_build_now
  {T : Type _} {T1 : Type _} (coremarkerCopyInst : core.marker.Copy T)
  (coredefaultDefaultInst : core.default.Default T)
  (coreopsfunctionFnOnceT1TupleTInst : core.ops.function.FnOnce T1 Unit T) :
  low.generic.reuse_cache.ReuseCache T → T1 → Result T

opaque low.generic.reuse_cache.ReuseCache.get_or_build
  {T : Type _} {T1 : Type _} (coremarkerCopyInst : core.marker.Copy T)
  (coredefaultDefaultInst : core.default.Default T)
  (coreopsfunctionFnOnceT1TupleTInst : core.ops.function.FnOnce T1 Unit T) :
  low.generic.reuse_cache.ReuseCache T → T1 → Result (Option T)

opaque low.generic.reuse_cache.ReuseCache.Insts.CoreCloneClone.clone
  {T : Type _} (coremarkerCopyInst : core.marker.Copy T)
  (coredefaultDefaultInst : core.default.Default T) :
  low.generic.reuse_cache.ReuseCache T → Result
    (low.generic.reuse_cache.ReuseCache T)

/-! The wipe a drop runs, which no theorem calls. -/

opaque low.generic.zeroise.zeroise
  {T : Type _} (ZeroableInst : low.generic.zeroise.Zeroable T) :
  Slice T → Result (Slice T)

/-- Wiping a value, which no proof observes: the translation ignores drops. -/
opaque low.generic.zeroise.zeroise_value {T : Type} (ZeroableInst : low.generic.zeroise.Zeroable T) :
  T → Result T

/-- `ZeroableRef::new`, as `Rind.Aarch64.Dispatch` models a `ZeroableRef`: its
value. -/
def low.generic.zeroise.ZeroableRef.new {T : Type} (value : T) :
    Result (low.generic.zeroise.ZeroableRef T) :=
  ok value

/-! The entry guard and CPU dispatch, which read no input. -/

opaque low.entry.Entry.new_secret : Result low.entry.Entry

opaque low.entry.Entry.new_public : Result low.entry.Entry

/-- Whether an entry guard is held, which a debug build asserts. -/
opaque low.entry.Entry.assert_held : Result Unit

opaque low.aarch64.cpu.HaveSha3.check : Result (Option low.aarch64.cpu.HaveSha3)

opaque low.aarch64.cpu.HaveCryptoExt.check : Result (Option low.aarch64.cpu.HaveCryptoExt)

/-! SHA-1's block function, whose contract `Rind.Aarch64.ShaBlocks` states as a
hypothesis. It picks between aws-lc's routines by the CPU through raw
pointers, which Aeneas cannot translate. -/

opaque low.aarch64.sha1.sha1_compress_blocks
  : Array Std.U32 5#usize → Slice Std.U8 → Result (Array Std.U32 5#usize)

/-! aws-lc's SHA-256 routines, behind their Rust wrappers. `Rind.Aarch64.Sha256Hw`
states the first's contract, rind's HOL Light proof's theorem. -/

opaque low.aarch64.sha256.compress_hw
  :
  low.aarch64.cpu.HaveCryptoExt → Array Std.U32 8#usize → Slice Std.U8 → Result
    (Array Std.U32 8#usize)

opaque low.aarch64.sha256.compress_nohw
  : Array Std.U32 8#usize → Slice Std.U8 → Result (Array Std.U32 8#usize)

/-! P-384's s2n-bignum routines, its table select, and `bignum_mux`. -/

opaque low.aarch64.bignum_add_p384.bignum_add_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Array Std.U64 6#usize →
    Result (Array Std.U64 6#usize)

opaque low.aarch64.bignum_demont_p384.bignum_demont_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.aarch64.bignum_inv_p384.bignum_inv_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.aarch64.bignum_montmul_p384.bignum_montmul_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Array Std.U64 6#usize →
    Result (Array Std.U64 6#usize)

opaque low.aarch64.bignum_montsqr_p384.bignum_montsqr_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.aarch64.bignum_mux.bignum_mux
  :
  Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Result
    (Slice Std.U64)

opaque low.aarch64.bignum_neg_p384.bignum_neg_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.aarch64.bignum_point_select.bignum_aff_point_select_p384
  :
  Array Std.U64 12#usize → Slice Std.U64 → Std.U8 → Result (Array Std.U64
    12#usize)

opaque low.aarch64.bignum_tomont_p384.bignum_tomont_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.aarch64.p384_montjdouble.p384_montjdouble
  :
  Array Std.U64 18#usize → Array Std.U64 18#usize → Result (Array Std.U64
    18#usize)

opaque low.aarch64.p384_montjmixadd.p384_montjmixadd
  :
  Array Std.U64 18#usize → Array Std.U64 18#usize → Array Std.U64 12#usize
    → Result (Array Std.U64 18#usize)

opaque low.aarch64.p384_montjscalarmul.p384_montjscalarmul
  :
  Array Std.U64 18#usize → Array Std.U64 6#usize → Array Std.U64 18#usize
    → Result (Array Std.U64 18#usize)

opaque low.aarch64.bignum_mod_n384.bignum_mod_n384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque high.curve.P384.Insts.RindHighCurveCurveStaticPrivateKeyVerifyingKeyScalar.oid
  : Result high.asn1.ObjectId

/-! The other curves, which X25519's and P-256's results never depend on. -/

opaque mid.p521.PrivateKey.new_random
  : Result (core.result.Result mid.p521.PrivateKey error.Error)

opaque mid.p384.PrivateKey.new_random
  : Result (core.result.Result mid.p384.PrivateKey error.Error)

opaque mid.p521.PrivateKey.public_key_uncompressed
  : mid.p521.PrivateKey → Result (Array Std.U8 133#usize)

opaque mid.p521.PrivateKey.diffie_hellman
  :
  mid.p521.PrivateKey → mid.p521.PublicKey → Result (core.result.Result
    mid.p521.SharedSecret error.Error)

opaque mid.p521.PublicKey.from_x962_uncompressed
  : Slice Std.U8 → Result (core.result.Result mid.p521.PublicKey error.Error)

/-! NEON's AES, which CPUs without the crypto extension run, and which no proof covers. -/

opaque low.aarch64.vpaes_armv8.VpaesKey.new
  : Slice Std.U8 → Result low.aarch64.vpaes_armv8.VpaesKey

opaque low.aarch64.vpaes_armv8.VpaesKey.encrypt_block
  : low.aarch64.vpaes_armv8.VpaesKey → Array Std.U8 16#usize → Result (Array Std.U8 16#usize)

opaque low.aarch64.vpaes_armv8.VpaesDecKey.new
  : Slice Std.U8 → Result low.aarch64.vpaes_armv8.VpaesDecKey

opaque low.aarch64.vpaes_armv8.VpaesDecKey.decrypt_block
  : low.aarch64.vpaes_armv8.VpaesDecKey → Array Std.U8 16#usize → Result (Array Std.U8 16#usize)

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

opaque high.sec1.decode
  : Slice Std.U8 → high.asn1.ObjectId → Result (core.result.Result high.sec1.Decoded error.Error)

opaque high.sec1.decode_pkcs8
  : Slice Std.U8 → high.asn1.ObjectId → Result (core.result.Result high.sec1.Decoded error.Error)

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

/-! The constant-time compares behind `low::generic::ct_equal`, whose inline
assembly `Rind.Aarch64.CtEqual` states HOL Light's theorems about. -/

opaque low.aarch64.cpu.ct_compare_16
  : Array Std.U8 16#usize → Array Std.U8 16#usize → Result Std.Usize

opaque low.aarch64.cpu.ct_compare_bytes : Slice Std.U8 → Slice Std.U8 → Result Std.U8


/-! Field and curve routines `low::aarch64::wide_mux` also exports. The
translation leaves `crate::low` opaque, so each is named here for the abbrev
below. The type is the one Aeneas gives the Rust signature: a `&mut` buffer
is an argument and the result, and a returned word is the result's first
component. -/

opaque low.aarch64.bignum_invsqrt_p25519.bignum_invsqrt_p25519
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Std.U64 × (Array
    Std.U64 4#usize))

opaque low.aarch64.bignum_mul_p25519.bignum_mul_p25519
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Result (Array Std.U64 4#usize)

opaque low.aarch64.bignum_sqr_p25519.bignum_sqr_p25519
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.aarch64.edwards25519_epadd.edwards25519_epadd
  :
  Array Std.U64 16#usize → Array Std.U64 16#usize → Array Std.U64 16#usize →
    Result (Array Std.U64 16#usize)

opaque low.aarch64.edwards25519_epdouble.edwards25519_epdouble
  :
  Array Std.U64 16#usize → Array Std.U64 12#usize → Result (Array Std.U64
    16#usize)

opaque low.aarch64.edwards25519_pdouble.edwards25519_pdouble
  :
  Array Std.U64 12#usize → Array Std.U64 12#usize → Result (Array Std.U64
    12#usize)

opaque low.aarch64.p521_jadd.p521_jadd
  :
  Array Std.U64 27#usize → Array Std.U64 27#usize → Array Std.U64 27#usize →
    Result (Array Std.U64 27#usize)

opaque low.aarch64.p521_jdouble.p521_jdouble
  :
  Array Std.U64 27#usize → Array Std.U64 27#usize → Result (Array Std.U64
    27#usize)

opaque low.aarch64.p521_jmixadd.p521_jmixadd
  :
  Array Std.U64 27#usize → Array Std.U64 27#usize → Array Std.U64 18#usize →
    Result (Array Std.U64 27#usize)

opaque low.aarch64.p521_jscalarmul.p521_jscalarmul
  :
  Array Std.U64 27#usize → Array Std.U64 9#usize → Array Std.U64 27#usize →
    Result (Array Std.U64 27#usize)

/-! `low::aarch64::wide_mux` picks each routine's `_alt` or narrow schedule by
the core's multiplier, which the translation cannot see. This model is the
wide schedule: each mux name is the `_alt` function. The narrow schedules are
outside this claim. -/

abbrev low.aarch64.wide_mux.bignum_invsqrt_p25519 := @low.aarch64.bignum_invsqrt_p25519.bignum_invsqrt_p25519
abbrev low.aarch64.wide_mux.bignum_madd_n25519 := @low.aarch64.bignum_madd_n25519.bignum_madd_n25519
abbrev low.aarch64.wide_mux.bignum_mul_p25519 := @low.aarch64.bignum_mul_p25519.bignum_mul_p25519
abbrev low.aarch64.wide_mux.bignum_sqr_p25519 := @low.aarch64.bignum_sqr_p25519.bignum_sqr_p25519
abbrev low.aarch64.wide_mux.curve25519_x25519 := @low.aarch64.curve25519_x25519.curve25519_x25519
abbrev low.aarch64.wide_mux.curve25519_x25519base := @low.aarch64.curve25519_x25519base.curve25519_x25519base
abbrev low.aarch64.wide_mux.edwards25519_decode := @low.aarch64.edwards25519_decode.edwards25519_decode
abbrev low.aarch64.wide_mux.edwards25519_epadd := @low.aarch64.edwards25519_epadd.edwards25519_epadd
abbrev low.aarch64.wide_mux.edwards25519_epdouble := @low.aarch64.edwards25519_epdouble.edwards25519_epdouble
abbrev low.aarch64.wide_mux.edwards25519_pdouble := @low.aarch64.edwards25519_pdouble.edwards25519_pdouble
abbrev low.aarch64.wide_mux.edwards25519_scalarmulbase := @low.aarch64.edwards25519_scalarmulbase.edwards25519_scalarmulbase
abbrev low.aarch64.wide_mux.edwards25519_scalarmuldouble := @low.aarch64.edwards25519_scalarmuldouble.edwards25519_scalarmuldouble
abbrev low.aarch64.wide_mux.p256_montjmixadd := @low.aarch64.p256_montjmixadd.p256_montjmixadd
abbrev low.aarch64.wide_mux.p256_scalarmul := @low.aarch64.p256_scalarmul.p256_scalarmul
abbrev low.aarch64.wide_mux.p256_scalarmulbase := @low.aarch64.p256_scalarmulbase.p256_scalarmulbase
abbrev low.aarch64.wide_mux.p384_montjmixadd := @low.aarch64.p384_montjmixadd.p384_montjmixadd
abbrev low.aarch64.wide_mux.p384_montjscalarmul := @low.aarch64.p384_montjscalarmul.p384_montjscalarmul
abbrev low.aarch64.wide_mux.p521_jadd := @low.aarch64.p521_jadd.p521_jadd
abbrev low.aarch64.wide_mux.p521_jdouble := @low.aarch64.p521_jdouble.p521_jdouble
abbrev low.aarch64.wide_mux.p521_jmixadd := @low.aarch64.p521_jmixadd.p521_jmixadd
abbrev low.aarch64.wide_mux.p521_jscalarmul := @low.aarch64.p521_jscalarmul.p521_jscalarmul

end rind.aarch64
