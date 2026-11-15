module
public import Aeneas
public import Rind.Core
public import Rind.Portable.DigestAlgorithm
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-! The rind types the portable translation leaves opaque.
`Rind.Portable.QuicDispatch` and `Rind.Portable.DigestDispatch` model the last
two, and `Rind.Portable.DigestAlgorithm` `Algorithm` and `Digest`. -/

namespace rind.portable

/-- The entry guard every operation holds, which changes no value. -/
opaque low.entry.Entry : Type

/-- An AES key, whose header protection no proof covers. -/
opaque mid.aes.Aes : Type

/-- MD5's chaining state, which no proof covers. -/
opaque mid.md5.Md5State : Type

/-- An MD5 context, which no proof covers. -/
opaque mid.md5.Md5Context : Type

/-- A SHA-3 context, whose sponge no proof covers. -/
opaque mid.sha3.Sha3Context (R : Std.Usize) (OUT : Std.Usize) : Type

/-- A header-protection key with its cipher's mask, as
`Rind.Portable.QuicDispatch` models it: the key, since `Masker::new` builds
every one with `C`'s own `mask`, which the model calls directly. -/
@[reducible] def aead.quic.Masker (C : Type) : Type := C

/-- A hash's context functions, as `Rind.Portable.DigestDispatch` models them:
nothing, since `Hashing::start` builds the only one, of `C`'s own
`HashContext` functions, which the model calls directly. -/
@[reducible] def high.digest.Ops (_C : Type) : Type := Unit

end rind.portable
