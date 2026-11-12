module
public import Aeneas
public import Rind.Core
public import Rind.Aarch64.DigestAlgorithm
public import Rind.Aarch64.Neon
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-! The rind types the aarch64 translation leaves opaque. `Rind.Aarch64.Dispatch` and
`Rind.Aarch64.DigestDispatch` model the last five, and `Rind.Aarch64.DigestAlgorithm`
`Algorithm` and `Digest`, and `Rind.Aarch64.Neon` the vector types. -/

namespace rind.aarch64

/-- The entry guard every operation holds, which changes no value. -/
opaque low.entry.Entry : Type

/-- The token proving the CPU has the SHA-512 instructions. -/
opaque low.aarch64.cpu.HaveSha3 : Type

/-- The token proving the CPU has the crypto extension's instructions, SHA-256's
among them. -/
opaque low.aarch64.cpu.HaveCryptoExt : Type

/-- A value its owner builds once and keeps, whose atomics Aeneas cannot
translate. -/
opaque low.generic.reuse_cache.ReuseCache (T : Type) : Type

/-- The HMAC-DRBG an ECDSA signature draws its nonces from, whose output the
functional spec leaves out. -/
opaque high.hmac_drbg.HmacDrbg (H : Type _) (Clause0_Context : Type _) (Clause0_State : Type _) : Type

/-- The NEON AES keys aarch64 CPUs without the crypto extension run. -/
opaque low.aarch64.vpaes_armv8.VpaesKey : Type
opaque low.aarch64.vpaes_armv8.VpaesDecKey : Type

/-- MD5's chaining state, which no proof covers. -/
opaque mid.md5.Md5State : Type

/-- An MD5 context, which no proof covers. -/
opaque mid.md5.Md5Context : Type

/-- A `&'static T` that a wiped value may hold, as `Rind.Aarch64.Dispatch` models it:
the `T`, since only the drop that wipes it leaves it `None`. -/
@[reducible] def low.generic.zeroise.ZeroableRef (T : Type) : Type := T

/-- `&'static high::agreement::Algorithm`, as `Rind.Aarch64.Dispatch` models it:
which of the four statics, since `high::agreement` builds no other. -/
inductive high.agreement.Algorithm where
  | X25519
  | ECDH_P256
  | ECDH_P384
  | ECDH_P521
deriving DecidableEq

/-- A curve's key agreement functions, as `Rind.Aarch64.Dispatch` models them:
nothing, since `Keyed::private_key` builds each `Ops<K::Key>` from the curve
marker `K`'s own `Agree` functions, which the model calls directly. -/
@[reducible] def high.agreement.Ops (_Key : Type) : Type := Unit

/-- A header-protection key with its cipher's mask, as `Rind.Aarch64.Dispatch` models it:
the key, since `Masker::new` builds every one with `C`'s own `mask`, which the
model calls directly. -/
@[reducible] def aead.quic.Masker (C : Type) : Type := C

/-- A hash's context functions, as `Rind.Aarch64.DigestDispatch` models them:
nothing, since `Hashing::start` builds the only one, of `C`'s own
`HashContext` functions, which the model calls directly. -/
@[reducible] def high.digest.Ops (_C : Type) : Type := Unit

end rind.aarch64
