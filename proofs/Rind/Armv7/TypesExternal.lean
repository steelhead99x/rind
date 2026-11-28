module
public import Aeneas
public import Rind.Core
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-! The rind types the armv7 translation leaves opaque. `Rind.Armv7.Dispatch`,
`Rind.Armv7.QuicDispatch`, and `Rind.Armv7.AeadDispatch` model the last five. -/

namespace rind.armv7

/-- The entry guard every operation holds, which changes no value. -/
opaque low.entry.Entry : Type

/-- An AES key, whose header protection no proof covers. -/
opaque mid.aes.Aes : Type

/-! The CPU feature tokens, and the keys and GHASH tables of the assembly they
gate: `Rind.Armv7.AesGcm`'s theorems are about a CPU with neither feature,
and only NEON's GHASH table is proven, in `Rind.Armv7.GhashNeon`. -/

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

/-- curve25519-dalek's point, which the translation leaves opaque: rind only
passes it between dalek's functions, and `Rind.Armv7.Dalek` states what they
do to the point it represents. -/
opaque curve25519_dalek.edwards.EdwardsPoint : Type

/-- ChaCha20-Poly1305's key, which `aead::Key` holds and whose armv7 code no
proof covers yet. -/
opaque mid.chacha20poly1305.ChaCha20Poly1305 : Type

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

/-- An expanded AEAD key with its cipher's functions, as `Rind.Armv7.AeadDispatch`
models it: the key, since `Sealer::expand` builds every one with `C`'s own
`seal` and `open`, which the model calls directly. -/
@[reducible] def aead.Sealer (C : Type) : Type := C

/-- A header-protection key with its cipher's mask, as `Rind.Armv7.QuicDispatch` models it:
the key, since `Masker::new` builds every one with `C`'s own `mask`, which the
model calls directly. -/
@[reducible] def aead.quic.Masker (C : Type) : Type := C

end rind.armv7
