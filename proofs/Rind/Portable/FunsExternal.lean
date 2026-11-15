module
public import Aeneas
public import Rind.Portable.Types
public import Rind.Portable.Compare
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
The functions the portable translation leaves opaque, beside the compares
`Rind.Portable.Compare` models. No proof assumes anything about them beyond
what `Rind.Portable.Hacl` states for HACL*'s SHA-2 block functions and what
each theorem takes as a hypothesis.
-/

namespace rind.portable

/-! HACL*'s SHA-2 block functions, as libcrux-sha2 ships them, which Charon
cannot translate. -/

opaque libcrux_sha2.hacl.sha256_update_nblocks
  : Std.U32 → Slice Std.U8 → Slice Std.U32 → Result (Slice Std.U32)

opaque libcrux_sha2.hacl.sha512_update_nblocks
  : Std.U32 → Slice Std.U8 → Slice Std.U64 → Result (Slice Std.U64)

/-! SHA-1's block function, whose contract `Rind.Portable.ShaBlocks` states as
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

opaque mid.md5.Md5Context.Insts.CoreCloneClone.clone : mid.md5.Md5Context → Result mid.md5.Md5Context

/-! SHA-3, whose sponge this translation leaves out. -/

opaque mid.sha3.Sha3Context.new
  (R : Std.Usize) (OUT : Std.Usize) : Result (mid.sha3.Sha3Context R OUT)

opaque mid.sha3.Sha3Context.update {R : Std.Usize} {OUT : Std.Usize}
  : mid.sha3.Sha3Context R OUT → Slice Std.U8 → Result (mid.sha3.Sha3Context R OUT)

opaque mid.sha3.Sha3Context.finish {R : Std.Usize} {OUT : Std.Usize}
  : mid.sha3.Sha3Context R OUT → Result (Array Std.U8 OUT)

opaque mid.sha3.Sha3Context.Insts.CoreCloneClone.clone {R : Std.Usize} {OUT : Std.Usize}
  : mid.sha3.Sha3Context R OUT → Result (mid.sha3.Sha3Context R OUT)

end rind.portable
