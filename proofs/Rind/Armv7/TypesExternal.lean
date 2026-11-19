module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-! The rind types the armv7 translation leaves opaque. `Rind.Armv7.QuicDispatch`
models the last. -/

namespace rind.armv7

/-- The entry guard every operation holds, which changes no value. -/
opaque low.entry.Entry : Type

/-- An AES key, whose header protection no proof covers. -/
opaque mid.aes.Aes : Type

/-- A header-protection key with its cipher's mask, as `Rind.Armv7.QuicDispatch` models it:
the key, since `Masker::new` builds every one with `C`'s own `mask`, which the
model calls directly. -/
@[reducible] def aead.quic.Masker (C : Type) : Type := C

end rind.armv7
