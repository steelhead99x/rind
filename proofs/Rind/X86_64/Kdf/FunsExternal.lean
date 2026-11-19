module
public import Rind.X86_64.HkdfExpand
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-! The functions the x86_64 HKDF and PBKDF2 translation leaves opaque, beside
the HMAC API's, which `Rind.X86_64.HmacDispatch` models, and HKDF-Expand's
loop, which `Rind.X86_64.HkdfExpand` does: each as the Rust standard library
or rind defines it. -/

namespace rind.x86_64.kdf

/-- `NonZeroU32Inner`'s `Clone`. -/
def core.num.niche_types.NonZeroU32Inner.Insts.CoreCloneClone.clone
    (x : core.num.niche_types.NonZeroU32Inner) : Result core.num.niche_types.NonZeroU32Inner :=
  ok x

/-- `NonZero::get`. -/
def core.num.nonzero.NonZero.get {T Inner : Type}
    (_ : core.num.nonzero.ZeroablePrimitive T Inner) (x : core.num.nonzero.NonZero T Inner) :
    Result T :=
  ok x

/-- `Digest`'s derived `Clone`, which copies its algorithm and bytes. -/
def high.digest.Digest.Insts.CoreCloneClone.clone (d : high.digest.Digest) :
    Result high.digest.Digest :=
  ok d

-- BEGIN vg (x86_64 and portable only: aarch64 translates `mid::pbkdf2_vg`)
/-! PBKDF2 on pyca/verified-garbage's routine (`mid::pbkdf2_vg`), which no CPU
of this target runs, left opaque. -/

/-- `pbkdf2_vg::Key::new`. -/
opaque mid.pbkdf2_vg.Key.new (algorithm : mid.pbkdf2_vg.Algorithm) (secret : Slice Std.U8) :
    Result (Option mid.pbkdf2_vg.Key)

/-- `pbkdf2_vg::Key::derive`. -/
opaque mid.pbkdf2_vg.Key.derive (self : mid.pbkdf2_vg.Key)
    (iterations : core.num.nonzero.NonZero Std.U32 core.num.niche_types.NonZeroU32Inner)
    (salt out : Slice Std.U8) :
    Result ((core.result.Result Unit error.Error) × (Slice Std.U8))

/-- `pbkdf2_vg::Key::verify`. -/
opaque mid.pbkdf2_vg.Key.verify (self : mid.pbkdf2_vg.Key)
    (iterations : core.num.nonzero.NonZero Std.U32 core.num.niche_types.NonZeroU32Inner)
    (salt previously_derived : Slice Std.U8) :
    Result (core.result.Result Unit error.Error)
-- END vg

/-! The header and AEAD models, lifted into what this translation calls them
in. Each lift is what the Rust does: `key_len` is pure, and the `new`s return
the error type this translation defines, not the models' own copy of it.
Refusing a key is `fail .panic`, which is what `expect` does when the From
impls call them, so each From impl panics exactly where it does. -/

/-- `quic::Algorithm::key_len`. -/
def aead.quic.Algorithm.key_len (self : aead.quic.Algorithm) : Result Usize :=
  ok (rind.x86_64.aead.quic.Algorithm.key_len self)

/-- `HeaderProtectionKey::new`, refusing as `expect` panics. -/
def aead.quic.HeaderProtectionKey.new (algorithm : aead.quic.Algorithm) (key : Slice Std.U8) :
    Result (core.result.Result aead.quic.HeaderProtectionKey error.Error) := do
  let r ← rind.x86_64.aead.quic.HeaderProtectionKey.new algorithm key
  match r with
  | .Ok k => ok (.Ok k)
  | .Err _ => fail .panic

-- BEGIN aead (x86_64 only: its AEAD model and proofs are x86_64's)
/-- `Algorithm::key_len`. -/
def aead.Algorithm.key_len (self : aead.Algorithm) : Result Usize :=
  ok (rind.x86_64.aead.Algorithm.key_len self)

/-- `Key::new`, refusing as `expect` panics. -/
def aead.Key.new (algorithm : aead.Algorithm) (key : Slice Std.U8) :
    Result (core.result.Result aead.Key error.Error) := do
  let r ← rind.x86_64.aead.Key.new algorithm key
  match r with
  | .Ok k => ok (.Ok k)
  | .Err _ => fail .panic
-- END aead

end rind.x86_64.kdf
