module
public import Aeneas
public import Rind.Core
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-! The rind types the armv7 translation leaves opaque. `Rind.Armv7.Dispatch`
and `Rind.Armv7.QuicDispatch` model the last four. -/

namespace rind.armv7

/-- The entry guard every operation holds, which changes no value. -/
opaque low.entry.Entry : Type

/-- An AES key, whose header protection no proof covers. -/
opaque mid.aes.Aes : Type

/-! The CPU feature tokens, and the keys and GHASH tables of the assembly they
gate, which no proof covers: `Rind.Armv7.AesGcm`'s theorems are about a CPU
with neither feature. -/

/-- The token that the CPU has the crypto extension. -/
opaque low.arm.cpu.HaveCryptoExt : Type

/-- The token that the CPU has NEON. -/
opaque low.arm.cpu.HaveNeon : Type

/-- The crypto extension's AES key. -/
opaque low.arm.aesv8_armx.AesHwKey : Type

/-- The crypto extension's GHASH table. -/
opaque low.arm.ghashv8_armx.GhashTable : Type

/-- NEON's AES key. -/
opaque low.arm.vpaes_armv7.NeonKey : Type

/-- NEON's GHASH table. -/
opaque low.arm.ghash_armv4.NeonTable : Type

/-! The NIST curves' keys, whose fiat-crypto arithmetic no armv7 proof covers. -/

opaque mid.p256.PrivateKey : Type

opaque mid.p256.PublicKey : Type

opaque mid.p384.PrivateKey : Type

opaque mid.p384.PublicKey : Type

opaque mid.p521.PrivateKey : Type

opaque mid.p521.PublicKey : Type

/-- A `&'static T` that a wiped value may hold, as `Rind.Armv7.Dispatch` models it:
the `T`, since only the drop that wipes it leaves it `None`. -/
@[reducible] def low.generic.zeroise.ZeroableRef (T : Type) : Type := T

/-- `&'static high::agreement::Algorithm`, as `Rind.Armv7.Dispatch` models it:
which of the four statics, since `high::agreement` builds no other. -/
inductive high.agreement.Algorithm where
  | X25519
  | ECDH_P256
  | ECDH_P384
  | ECDH_P521
deriving DecidableEq

/-- A curve's key agreement functions, as `Rind.Armv7.Dispatch` models them:
nothing, since `Keyed::private_key` builds each `Ops<K::Key>` from the curve
marker `K`'s own `Agree` functions, which the model calls directly. -/
@[reducible] def high.agreement.Ops (_Key : Type) : Type := Unit

/-- A header-protection key with its cipher's mask, as `Rind.Armv7.QuicDispatch` models it:
the key, since `Masker::new` builds every one with `C`'s own `mask`, which the
model calls directly. -/
@[reducible] def aead.quic.Masker (C : Type) : Type := C

end rind.armv7
