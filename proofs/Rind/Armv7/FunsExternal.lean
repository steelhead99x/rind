module
public import Aeneas
public import Rind.Armv7.Types
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
The rind functions the armv7 translation leaves opaque. No proof assumes anything
about them beyond what each theorem takes as a hypothesis.
-/

namespace rind.armv7

/-! The entry guards, which read no input. -/

opaque low.entry.Entry.new_secret : Result low.entry.Entry

opaque low.entry.Entry.new_public : Result low.entry.Entry

/-- Whether an entry guard is held, which a debug build asserts. -/
opaque low.entry.Entry.assert_held : Result Unit

/-- Wiping a value, which no proof observes: the translation ignores drops. -/
opaque low.generic.zeroise.zeroise_value {T : Type} (ZeroableInst : low.generic.zeroise.Zeroable T) :
  T → Result T

/-- What `zeroise` leaves in `v`, as `Rind.X86_64.FunsExternal` models it: no
proof reads a slice after its wipe. -/
opaque low.generic.zeroise.wiped {T : Type _} (v : Slice T) : Slice T := v

/-- `zeroise`, which returns, as `Rind.X86_64.FunsExternal` models it. -/
def low.generic.zeroise.zeroise {T : Type _} (_ZeroableInst : low.generic.zeroise.Zeroable T)
    (v : Slice T) : Result (Slice T) :=
  ok (low.generic.zeroise.wiped v)

/-! aws-lc's `sha512-armv4` routines, behind their Rust wrappers, which
`Rind.Armv7.Sha512Entry` states. -/

opaque low.arm.sha_armv4.compress_neon
  : low.arm.cpu.HaveNeon → Array Std.U64 8#usize → Slice Std.U8 → Result (Array Std.U64 8#usize)

opaque low.arm.sha_armv4.compress_nohw
  : Array Std.U64 8#usize → Slice Std.U8 → Result (Array Std.U64 8#usize)

/-- `ZeroableRef::new`, as `Rind.Armv7.Dispatch` models a `ZeroableRef`: its
value. -/
def low.generic.zeroise.ZeroableRef.new {T : Type} (value : T) :
    Result (low.generic.zeroise.ZeroableRef T) :=
  ok value

/-! AES, whose header protection no proof covers. -/

opaque mid.aes.Aes.new
  : cipher.Algorithm → Slice Std.U8 → Result (core.result.Result mid.aes.Aes error.Error)

opaque mid.aes.Aes.header_protection_mask
  : mid.aes.Aes → Array Std.U8 16#usize → Result (Array Std.U8 5#usize)

/-! curve25519-dalek's X25519, whose Beneficial AI Foundation theorems
`Rind.Armv7.Dalek` restates, and BoringSSL's NEON ladder, which no proof
covers: `Rind.Armv7.X25519`'s shared-secret theorems are about a CPU without
NEON. -/

opaque curve25519_dalek.montgomery.MontgomeryPoint.mul_clamped
  : curve25519_dalek.montgomery.MontgomeryPoint → Array Std.U8 32#usize →
    Result curve25519_dalek.montgomery.MontgomeryPoint

opaque curve25519_dalek.montgomery.MontgomeryPoint.mul_base_clamped
  : Array Std.U8 32#usize → Result curve25519_dalek.montgomery.MontgomeryPoint

/-! curve25519-dalek's Ed25519 arithmetic, whose Beneficial AI Foundation
theorems `Rind.Armv7.Dalek` restates too. -/

opaque curve25519_dalek.edwards.CompressedEdwardsY.decompress
  : curve25519_dalek.edwards.CompressedEdwardsY → Result (Option curve25519_dalek.edwards.EdwardsPoint)

opaque curve25519_dalek.edwards.EdwardsPoint.compress
  : curve25519_dalek.edwards.EdwardsPoint → Result curve25519_dalek.edwards.CompressedEdwardsY

opaque curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint.neg
  : curve25519_dalek.edwards.EdwardsPoint → Result curve25519_dalek.edwards.EdwardsPoint

opaque curve25519_dalek.edwards.EdwardsPoint.mul_base
  : curve25519_dalek.scalar.Scalar → Result curve25519_dalek.edwards.EdwardsPoint

opaque curve25519_dalek.edwards.EdwardsPoint.vartime_double_scalar_mul_basepoint
  : curve25519_dalek.scalar.Scalar → curve25519_dalek.edwards.EdwardsPoint →
    curve25519_dalek.scalar.Scalar → Result curve25519_dalek.edwards.EdwardsPoint

opaque curve25519_dalek.scalar.Scalar.from_bytes_mod_order
  : Array Std.U8 32#usize → Result curve25519_dalek.scalar.Scalar

opaque curve25519_dalek.scalar.Scalar.from_bytes_mod_order_wide
  : Array Std.U8 64#usize → Result curve25519_dalek.scalar.Scalar

opaque curve25519_dalek.scalar.Scalar.from_canonical_bytes
  : Array Std.U8 32#usize → Result (subtle.CtOption curve25519_dalek.scalar.Scalar)

opaque curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulScalarScalar.mul
  : curve25519_dalek.scalar.Scalar → curve25519_dalek.scalar.Scalar → Result curve25519_dalek.scalar.Scalar

opaque curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithAddScalarScalar.add
  : curve25519_dalek.scalar.Scalar → curve25519_dalek.scalar.Scalar → Result curve25519_dalek.scalar.Scalar

/-! Three getters whose bodies the translation does not reach: subtle's two
that its `From<CtOption<T>> for Option<T>`, which the translation reads from
subtle's source, calls, and dalek's `Scalar::as_bytes`. `admin/prove` fails
unless these quotes are still the source Cargo.lock pins:

```rust
    pub fn unwrap_u8(&self) -> u8 {
        self.0
    }

    pub fn is_some(&self) -> Choice {
        self.is_some
    }

    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }

```
-/

/-- `Choice::unwrap_u8`: its byte. -/
def subtle.Choice.unwrap_u8 (c : subtle.Choice) : Result Std.U8 := ok c

/-- `CtOption::is_some`: its `is_some` field. -/
def subtle.CtOption.impl.is_some {T : Type _} (o : subtle.CtOption T) : Result subtle.Choice :=
  ok o.is_some

/-- `Scalar::as_bytes`: its bytes. -/
def curve25519_dalek.scalar.Scalar.as_bytes (s : curve25519_dalek.scalar.Scalar) :
    Result (Array Std.U8 32#usize) :=
  ok s.bytes

opaque low.arm.curve25519.ladder_neon
  : low.arm.cpu.HaveNeon → Array Std.U8 32#usize → Array Std.U8 32#usize →
    Result (Array Std.U8 32#usize)

/-! Agreement key encodings, and the NIST curves, whose fiat-crypto
arithmetic and DER no armv7 proof covers. -/

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

opaque high.curve.P256.Insts.RindHighCurveCurveStaticPrivateKeyVerifyingKeyScalar.oid
  : Result high.asn1.ObjectId

opaque high.curve.P384.Insts.RindHighCurveCurveStaticPrivateKeyVerifyingKeyScalar.oid
  : Result high.asn1.ObjectId

opaque mid.p256.Scalar.BYTES : Result Std.Usize

opaque mid.p256.PrivateKey.from_bytes
  : Slice Std.U8 → Result (core.result.Result mid.p256.PrivateKey error.Error)

opaque mid.p256.PrivateKey.new_random : Result (core.result.Result mid.p256.PrivateKey error.Error)

opaque mid.p256.PrivateKey.public_key_uncompressed : mid.p256.PrivateKey → Result (Array Std.U8 65#usize)

opaque mid.p256.PublicKey.from_x962_uncompressed
  : Slice Std.U8 → Result (core.result.Result mid.p256.PublicKey error.Error)

opaque mid.p256.PrivateKey.diffie_hellman
  : mid.p256.PrivateKey → mid.p256.PublicKey → Result (core.result.Result mid.p256.SharedSecret error.Error)

opaque mid.p384.Scalar.BYTES : Result Std.Usize

opaque mid.p384.PrivateKey.from_bytes
  : Slice Std.U8 → Result (core.result.Result mid.p384.PrivateKey error.Error)

opaque mid.p384.PrivateKey.new_random : Result (core.result.Result mid.p384.PrivateKey error.Error)

opaque mid.p384.PrivateKey.public_key_uncompressed : mid.p384.PrivateKey → Result (Array Std.U8 97#usize)

opaque mid.p384.PublicKey.from_x962_uncompressed
  : Slice Std.U8 → Result (core.result.Result mid.p384.PublicKey error.Error)

opaque mid.p384.PrivateKey.diffie_hellman
  : mid.p384.PrivateKey → mid.p384.PublicKey → Result (core.result.Result mid.p384.SharedSecret error.Error)

opaque mid.p521.PrivateKey.new_random : Result (core.result.Result mid.p521.PrivateKey error.Error)

opaque mid.p521.PrivateKey.public_key_uncompressed : mid.p521.PrivateKey → Result (Array Std.U8 133#usize)

opaque mid.p521.PublicKey.from_x962_uncompressed
  : Slice Std.U8 → Result (core.result.Result mid.p521.PublicKey error.Error)

opaque mid.p521.PrivateKey.diffie_hellman
  : mid.p521.PrivateKey → mid.p521.PublicKey → Result (core.result.Result mid.p521.SharedSecret error.Error)

/-! ChaCha20-Poly1305, which `aead::Key` holds and whose armv7 code no proof
covers yet. -/

opaque mid.chacha20poly1305.ChaCha20Poly1305.new
  : Array Std.U8 32#usize → Result mid.chacha20poly1305.ChaCha20Poly1305

opaque mid.chacha20poly1305.ChaCha20Poly1305.encrypt
  : mid.chacha20poly1305.ChaCha20Poly1305 → Array Std.U8 12#usize → Slice Std.U8 → Slice Std.U8 →
    Array Std.U8 16#usize →
    Result ((core.result.Result Unit error.Error) × (Slice Std.U8) × (Array Std.U8 16#usize))

opaque mid.chacha20poly1305.ChaCha20Poly1305.decrypt
  : mid.chacha20poly1305.ChaCha20Poly1305 → Array Std.U8 12#usize → Slice Std.U8 → Slice Std.U8 →
    Array Std.U8 16#usize → Result ((core.result.Result Unit error.Error) × (Slice Std.U8))

/-! The CPU feature checks. `Rind.Armv7.AesGcm`'s theorems take each one's
answer as a hypothesis: no feature, on the CPUs they are about. -/

opaque low.arm.cpu.HaveCryptoExt.check : Result (Option low.arm.cpu.HaveCryptoExt)

opaque low.arm.cpu.HaveNeon.check : Result (Option low.arm.cpu.HaveNeon)

/-! The constant-time compares behind `low::generic::ct_equal`, which call
A32 routines that `proofs/hol-light/armv7/ct_compare_*.ml` prove. -/

opaque low.arm.cpu.ct_compare_16
  : Array Std.U8 16#usize → Array Std.U8 16#usize → Result Std.Usize

opaque low.arm.cpu.ct_compare_bytes : Slice Std.U8 → Slice Std.U8 → Result Std.U8

/-! aws-lc's AES and GHASH assembly for the crypto extension, and its AES
for NEON, which no proof covers. -/

opaque low.arm.aesv8_armx.AesHwKey.new
  : Slice Std.U8 → low.arm.cpu.HaveCryptoExt → Result low.arm.aesv8_armx.AesHwKey

opaque low.arm.aesv8_armx.AesHwKey.encrypt_block
  : low.arm.aesv8_armx.AesHwKey → Array Std.U8 16#usize → Result (Array Std.U8 16#usize)

opaque low.arm.aesv8_armx.AesHwKey.ctr32
  : low.arm.aesv8_armx.AesHwKey → Array Std.U8 16#usize → Slice (Array Std.U8 16#usize) →
    Result (Slice (Array Std.U8 16#usize))

opaque low.arm.ghashv8_armx.GhashTable.new
  : Array Std.U8 16#usize → low.arm.cpu.HaveCryptoExt → Result low.arm.ghashv8_armx.GhashTable

opaque low.arm.ghashv8_armx.GhashTable.ghash
  : low.arm.ghashv8_armx.GhashTable → Array Std.U8 16#usize → Slice (Array Std.U8 16#usize) →
    Result (Array Std.U8 16#usize)

opaque low.arm.vpaes_armv7.NeonKey.new
  : Slice Std.U8 → low.arm.cpu.HaveNeon → Result low.arm.vpaes_armv7.NeonKey

opaque low.arm.vpaes_armv7.NeonKey.encrypt_block
  : low.arm.vpaes_armv7.NeonKey → Array Std.U8 16#usize → Result (Array Std.U8 16#usize)

opaque low.arm.vpaes_armv7.NeonKey.ctr32
  : low.arm.vpaes_armv7.NeonKey → Array Std.U8 16#usize → Slice (Array Std.U8 16#usize) →
    Result (Slice (Array Std.U8 16#usize))

/-! aws-lc's GHASH for NEON, whose HOL Light proofs `Rind.Armv7.GhashNeon`
restates. -/

opaque low.arm.ghash_armv4.NeonTable.new
  : Array Std.U8 16#usize → low.arm.cpu.HaveNeon → Result low.arm.ghash_armv4.NeonTable

opaque low.arm.ghash_armv4.NeonTable.ghash
  : low.arm.ghash_armv4.NeonTable → Array Std.U8 16#usize → Slice (Array Std.U8 16#usize) →
    Result (Array Std.U8 16#usize)

end rind.armv7
