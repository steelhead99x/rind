module
public import Aeneas
public import Rind.Mcu.Types
public import Rind.Mcu.Compare
public import Rind.Mcu.Sha256IramModel
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
The functions the translation for 32-bit microcontrollers leaves opaque,
beside the compares `Rind.Mcu.Compare` models and the IRAM SHA-256's helpers
`Rind.Mcu.Sha256IramModel` models. No proof assumes anything about them
beyond what each theorem takes as a hypothesis.
-/

namespace rind.mcu

/-! SHA-1's block function, whose contract `Rind.Mcu.ShaBlocks` states as
a hypothesis. -/

opaque low.generic.sha1.sha1_compress_blocks
  : Array Std.U32 5#usize → Slice Std.U8 → Result (Array Std.U32 5#usize)

/-! The entry guard, which reads no input. -/

opaque low.entry.Entry.new_secret : Result low.entry.Entry

/-- Whether an entry guard is held, which a debug build asserts. -/
opaque low.entry.Entry.assert_held : Result Unit

/-! AES, which no proof covers on this backend. -/

opaque mid.aes.Aes.new
  : cipher.Algorithm → Slice Std.U8 → Result (core.result.Result mid.aes.Aes error.Error)

opaque mid.aes.Aes.encrypt_block
  : mid.aes.Aes → Array Std.U8 16#usize → Result (Array Std.U8 16#usize)

opaque mid.aes.Aes.header_protection_mask
  : mid.aes.Aes → Array Std.U8 16#usize → Result (Array Std.U8 5#usize)

/-! MD5, which no proof covers. -/

opaque mid.md5.Md5State.new : Result mid.md5.Md5State

opaque mid.md5.Md5State.finish_with
  : mid.md5.Md5State → Slice Std.U8 → Result (Array Std.U8 16#usize)

opaque mid.md5.Md5Context.new : Result mid.md5.Md5Context

opaque mid.md5.Md5Context.update : mid.md5.Md5Context → Slice Std.U8 → Result mid.md5.Md5Context

opaque mid.md5.Md5Context.finish : mid.md5.Md5Context → Result (Array Std.U8 16#usize)

/-! SHA-3, whose sponge this translation leaves out. -/

opaque mid.sha3.Sha3Context.new
  (R : Std.Usize) (OUT : Std.Usize) : Result (mid.sha3.Sha3Context R OUT)

opaque mid.sha3.Sha3Context.update {R : Std.Usize} {OUT : Std.Usize}
  : mid.sha3.Sha3Context R OUT → Slice Std.U8 → Result (mid.sha3.Sha3Context R OUT)

opaque mid.sha3.Sha3Context.finish {R : Std.Usize} {OUT : Std.Usize}
  : mid.sha3.Sha3Context R OUT → Result (Array Std.U8 OUT)

end rind.mcu
