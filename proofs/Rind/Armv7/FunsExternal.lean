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

/-! AES, whose header protection no proof covers. -/

opaque mid.aes.Aes.header_protection_mask
  : mid.aes.Aes → Array Std.U8 16#usize → Result (Array Std.U8 5#usize)

end rind.armv7
