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

/-! The entry guard, which reads no input. -/

opaque low.entry.Entry.new_secret : Result low.entry.Entry

/-- Whether an entry guard is held, which a debug build asserts. -/
opaque low.entry.Entry.assert_held : Result Unit

/-- Wiping a value, which no proof observes: the translation ignores drops. -/
opaque low.generic.zeroise.zeroise_value {T : Type} (ZeroableInst : low.generic.zeroise.Zeroable T) :
  T → Result T

/-! AES, whose header protection no proof covers. -/

opaque mid.aes.Aes.header_protection_mask
  : mid.aes.Aes → Array Std.U8 16#usize → Result (Array Std.U8 5#usize)

/-! The CPU feature checks. `Rind.Armv7.AesGcm`'s theorems take each one's
answer as a hypothesis: no feature, on the CPUs they are about. -/

opaque low.arm.cpu.HaveCryptoExt.check : Result (Option low.arm.cpu.HaveCryptoExt)

opaque low.arm.cpu.HaveNeon.check : Result (Option low.arm.cpu.HaveNeon)

/-! The constant-time compares behind `low::generic::ct_equal`, whose inline
assembly `Rind.Armv7.CtEqual` states HOL Light's theorems about. -/

opaque low.arm.cpu.ct_compare_16
  : Array Std.U8 16#usize → Array Std.U8 16#usize → Result Std.Usize

opaque low.arm.cpu.ct_compare_bytes : Slice Std.U8 → Slice Std.U8 → Result Std.U8

/-! aws-lc's AES and GHASH assembly for the crypto extension and for NEON,
which no proof covers. -/

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

opaque low.arm.ghash_armv4.NeonTable.new
  : Array Std.U8 16#usize → low.arm.cpu.HaveNeon → Result low.arm.ghash_armv4.NeonTable

opaque low.arm.ghash_armv4.NeonTable.ghash
  : low.arm.ghash_armv4.NeonTable → Array Std.U8 16#usize → Slice (Array Std.U8 16#usize) →
    Result (Array Std.U8 16#usize)

end rind.armv7
