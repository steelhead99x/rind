module
public import Rind.X86_64.HmacDispatch
public import Rind.X86_64.QuicDispatch
public import Rind.X86_64.AeadDispatch
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-! The types the x86_64 HKDF and PBKDF2 translation, `Rind.X86_64.Kdf.Funs`,
leaves opaque: `NonZero<u32>`, and the HMAC and digest APIs' and the entry
guard, which it reaches as `Rind.X86_64.HmacDispatch` and the translation below
define them, in the namespace above its own. -/

namespace rind.x86_64.kdf

/-- `NonZeroU32Inner`: the `u32` a `NonZeroU32` holds. -/
@[reducible] def core.num.niche_types.NonZeroU32Inner : Type := Std.U32

/-- `NonZero<T>`: its `T`, which Rust keeps nonzero and no proof relies on. -/
@[reducible] def core.num.nonzero.NonZero (T : Type) (_Inner : Type) : Type := T

-- BEGIN vg (x86_64 and portable only: aarch64 translates `mid::pbkdf2_vg`)
/-- `mid::pbkdf2_vg::Algorithm` and `Key`: PBKDF2 on pyca/verified-garbage's
routine, which no CPU of this target runs. -/
opaque mid.pbkdf2_vg.Algorithm : Type
opaque mid.pbkdf2_vg.Key : Type
-- END vg

end rind.x86_64.kdf
