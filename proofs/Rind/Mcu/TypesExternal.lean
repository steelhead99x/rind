module
public import Aeneas
public import Rind.Core
public import Rind.Mcu.DigestAlgorithm
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-! The rind types the translation for 32-bit microcontrollers leaves opaque.
`Rind.Mcu.QuicDispatch` and `Rind.Mcu.DigestDispatch` model `Masker` and
`Ops`, `Rind.Mcu.DigestAlgorithm` `Algorithm` and `Digest`, and
`Rind.Mcu.Sha256IramModel` the methods of the last three, the IRAM SHA-256's
cursors and window, which read through raw pointers or `MaybeUninit`. -/

namespace rind.mcu

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
`Rind.Mcu.QuicDispatch` models it: the key, since `Masker::new` builds
every one with `C`'s own `mask`, which the model calls directly. -/
@[reducible] def aead.quic.Masker (C : Type) : Type := C

/-- A hash's context functions, as `Rind.Mcu.DigestDispatch` models them:
nothing, since `Hashing::start` builds the only one, of `C`'s own
`HashContext` functions, which the model calls directly. -/
@[reducible] def high.digest.Ops (_C : Type) : Type := Unit

/-- `RoundConstants`, a pointer into SHA-256's constants: the table it
started at and the index it points to. -/
@[reducible] def low.portable.sha.iram.RoundConstants : Type := Std.Array Std.U32 64#usize × Nat

/-- `Window`, the sixteen-word schedule window: each slot's word, or `none`
until it is written. -/
@[reducible] def low.portable.sha.iram.Window : Type := Std.Array (Option Std.U32) 16#usize

/-- `Blocks`, a pointer into a slice of whole blocks: the slice and the
offset it points to. -/
@[reducible] def low.portable.sha.iram.Blocks : Type := Slice Std.U8 × Nat

end rind.mcu
