module
public import Rind.Aarch64.Kdf.Types
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-! What the aarch64 HKDF and PBKDF2 translation alone leaves opaque, since
only it translates `mid::pbkdf2_vg`: the wipe of `Key::verify`'s derived key,
over this translation's own `Zeroable`. `admin/prove` imports it into
`Rind.Aarch64.Kdf.FunsExternal`. -/

namespace rind.aarch64.kdf

/-- `low::zeroise`, which writes zeros through a raw pointer. A theorem that
runs it takes that it returns as a hypothesis. -/
opaque low.generic.zeroise.zeroise {T : Type} (ZeroableInst : low.generic.zeroise.Zeroable T) :
    Slice T → Result (Slice T)

end rind.aarch64.kdf
