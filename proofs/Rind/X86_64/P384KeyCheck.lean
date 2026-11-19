import Rind.X86_64.P384Ecdsa
open Aeneas Aeneas.Std Result rind.spec

/-!
# x86_64's check that a P-384 signing key's public key is an encoding

What the shared `Rind.X86_64.P384Signature` takes of each target's
`SigningKey::is_public_key`: `is_public_key_of`, that it returns what SEC 1's
comparison with the key's own encoding does, or, for an X9.62 uncompressed
encoding, whether it encodes the key's scalar times G. P-384 has no
uncompressed fast path: its `public_key_is_uncompressed` is the trait's
default, `None`, so x86_64 always compares, as aarch64 does.
-/

namespace rind.x86_64

namespace P384

theorem is_public_key_of (_h : Runs) (_hc : Cached) (key : P384SigningKey) (enc : Slice U8)
    (_hk0 : 0 < scNat key.private_key.scalar) (_hk : scNat key.private_key.scalar < n384) (Post : Bool → Prop)
    (hsec1 : (do
      let ep ← high.ecdsa.SigningKey.public_key_uncompressed P384C key
      let s ← high.ecdsa.EncodedPoint.Insts.CoreConvertAsRefSliceU8.as_ref ep
      high.sec1.is_public_key s enc) ⦃ Post ⦄)
    (_hfast : ∀ m : Bool, enc.val.head? = some 4#u8 →
      (m = true ↔ enc.length = 97 ∧
        p384Pow p384G (scNat key.private_key.scalar) = some (p384Coords enc.val)) → Post m) :
    high.ecdsa.SigningKey.is_public_key P384C key enc ⦃ Post ⦄ := by
  unfold high.ecdsa.SigningKey.is_public_key
  step as ⟨e, he⟩
  split
  · exact hsec1
  step as ⟨i, hi⟩
  split
  · simp only [high.curve.PrivateKey.public_key_is_uncompressed.default, bind_ok]
    exact hsec1
  · exact hsec1

end P384

end rind.x86_64
