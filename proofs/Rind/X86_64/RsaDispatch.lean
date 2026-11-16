import Rind.X86_64.SignatureBuffer
import Rind.X86_64.RsaKey
open Aeneas Aeneas.Std Result rind.spec rind.spec.rsa

/-!
# The signature API's RSA public keys, modelled by hand

`rsa::PublicKey::verify` reaches each algorithm's verification through the
function pointer its `VerificationAlgorithm` holds, and every loader builds
the key's encoding with `Buffer::write`, both of which Aeneas cannot
translate, so the translation stops below them and this file models the Rust
above them for RSASSA-PKCS1-v1_5 and RSASSA-PSS with SHA-256,
`verify::PKCS1_SHA256` and `verify::PSS_SHA256`. `admin/prove` fails unless
this quote, and `SignatureBuffer`'s of `Buffer`, are still that Rust, so a
change to it is a change to this model:

```rust
enum HashId {
    Sha256,
    Sha384,
    Sha512,
}

impl HashId {
    /// The hash's output length, in bytes.
    const fn len(self) -> usize {
        match self {
            Self::Sha256 => 32,
            Self::Sha384 => 48,
            Self::Sha512 => 64,
        }
    }
}

const MAX_PUBLIC_MODULUS_BITS: usize = 8192;

pub(crate) const MAX_PUBLIC_MODULUS_BYTES: usize = MAX_PUBLIC_MODULUS_BITS / 8;

pub(crate) const MAX_PUBLIC_KEY_LEN: usize = rsa_pub::MAX_PUBLIC_MODULUS_BYTES + 64;

enum RsaPadding {
    /// RSASSA-PKCS1-v1_5.
    Pkcs1,
    /// RSASSA-PSS, with MGF1 on the same hash and a salt of this length.
    Pss(PssSalt),
}

struct RsaScheme {
    padding: RsaPadding,
    hash: HashId,
}

type RsaSign =
    for<'a> fn(&rsa::SigningKey, PssSalt, &'a mut [u8], &[u8]) -> Result<&'a [u8], Error>;

type RsaVerify = fn(&rsa::VerifyingKey, Option<PssSalt>, &[u8], &[u8]) -> Result<(), Error>;

impl RsaScheme {
    const fn pss(hash: HashId, salt: PssSalt) -> Self {
        Self {
            padding: RsaPadding::Pss(salt),
            hash,
        }
    }

    /// The PSS salt length, which PKCS#1 v1.5 ignores.
    const fn salt(self) -> PssSalt {
        match self.padding {
            RsaPadding::Pkcs1 => PssSalt::Hash,
            RsaPadding::Pss(salt) => salt,
        }
    }

    const fn signer(self) -> RsaSign {
        match (self.padding, self.hash) {
            (RsaPadding::Pkcs1, HashId::Sha256) => |key, _, out, m| key.sign_pkcs1_sha256(out, m),
            (RsaPadding::Pkcs1, HashId::Sha384) => |key, _, out, m| key.sign_pkcs1_sha384(out, m),
            (RsaPadding::Pkcs1, HashId::Sha512) => |key, _, out, m| key.sign_pkcs1_sha512(out, m),
            (RsaPadding::Pss(_), HashId::Sha256) => rsa::SigningKey::sign_pss_sha256,
            (RsaPadding::Pss(_), HashId::Sha384) => rsa::SigningKey::sign_pss_sha384,
            (RsaPadding::Pss(_), HashId::Sha512) => rsa::SigningKey::sign_pss_sha512,
        }
    }

    const fn verifier(self) -> RsaVerify {
        match (self.padding, self.hash) {
            (RsaPadding::Pkcs1, HashId::Sha256) => |key, _, s, m| key.verify_pkcs1_sha256(s, m),
            (RsaPadding::Pkcs1, HashId::Sha384) => |key, _, s, m| key.verify_pkcs1_sha384(s, m),
            (RsaPadding::Pkcs1, HashId::Sha512) => |key, _, s, m| key.verify_pkcs1_sha512(s, m),
            (RsaPadding::Pss(_), HashId::Sha256) => rsa::VerifyingKey::verify_pss_sha256,
            (RsaPadding::Pss(_), HashId::Sha384) => rsa::VerifyingKey::verify_pss_sha384,
            (RsaPadding::Pss(_), HashId::Sha512) => rsa::VerifyingKey::verify_pss_sha512,
        }
    }

    /// The smallest modulus whose PSS encoding fits the salt, if over
    /// `min_bits`: RFC 8017 section 9.1.1 needs `ceil((bits - 1) / 8)`
    /// bytes for the hash, the salt, and two more.
    const fn min_bits(self, min_bits: usize) -> usize {
        let salt = match self.padding {
            RsaPadding::Pkcs1 => return min_bits,
            RsaPadding::Pss(PssSalt::Hash) => self.hash.len(),
            RsaPadding::Pss(PssSalt::Max) => 0,
            RsaPadding::Pss(PssSalt::Len(len)) => len as usize,
        };
        let fits = 8 * (self.hash.len() + salt + 1) + 2;
        if fits > min_bits { fits } else { min_bits }
    }
}

enum RsaVerification {
    Scheme(RsaScheme),
    Pkcs1Sha1,
    PssAnySalt(HashId),
}

impl RsaVerification {
    const fn verifier(self) -> RsaVerify {
        match self {
            Self::Scheme(scheme) => scheme.verifier(),
            Self::Pkcs1Sha1 => |key, _, s, m| key.verify_pkcs1_sha1(s, m),
            Self::PssAnySalt(hash) => RsaScheme::pss(hash, PssSalt::Hash).verifier(),
        }
    }

    /// The PSS salt length to verify, `None` for any.
    fn salt(self) -> Option<PssSalt> {
        match self {
            Self::Scheme(scheme) => Some(scheme.salt()),
            Self::Pkcs1Sha1 | Self::PssAnySalt(_) => None,
        }
    }
}

pub struct VerificationAlgorithm {
    verification: RsaVerification,
    min_bits: usize,
    // The only path to the scheme's code, as ECDSA's algorithms hold theirs.
    verify: RsaVerify,
}

const fn verification(scheme: RsaScheme, min_bits: usize) -> VerificationAlgorithm {
    algorithm(RsaVerification::Scheme(scheme), scheme.min_bits(min_bits))
}

const fn algorithm(verification: RsaVerification, min_bits: usize) -> VerificationAlgorithm {
    VerificationAlgorithm {
        verification,
        min_bits,
        verify: verification.verifier(),
    }
}

const PKCS1_SHA256_SCHEME: RsaScheme = RsaScheme {
    padding: RsaPadding::Pkcs1,
    hash: HashId::Sha256,
};

const PSS_SHA256_SCHEME: RsaScheme = RsaScheme::pss(HashId::Sha256, PssSalt::Hash);

pub(crate) const MIN_BITS: usize = 2048;

pub struct PublicKey {
    key: rsa::VerifyingKey,
    encoding: RsaPublicKeyDer,
}

struct RsaPublicKeyDer(Buffer<{ rsa::MAX_PUBLIC_KEY_LEN }>, [u64; 0]);

impl PublicKey {
    /// Parses a PKCS#1 `RSAPublicKey`, refusing a malformed key before any
    /// signature arrives.
    pub fn new(der: &[u8]) -> Result<Self, Error> {
        Self::from_key(rsa::VerifyingKey::from_pkcs1_der(der)?)
    }

    /// Parses a public key from its `SubjectPublicKeyInfo` DER, naming
    /// `rsaEncryption`, `id-RSAES-OAEP`, or `id-ea-rsa` with `NULL`
    /// parameters or none.
    pub fn from_spki(der: &[u8]) -> Result<Self, Error> {
        Self::from_key(rsa::VerifyingKey::from_spki_der(der)?)
    }

    /// Loads a public key from its big-endian modulus and exponent, as a
    /// JWK carries them.
    pub fn from_components(
        components: &PublicKeyComponents<impl AsRef<[u8]>>,
    ) -> Result<Self, Error> {
        let key = rsa::VerifyingKey::from_components(components.n.as_ref(), components.e.as_ref())?;
        Self::from_key(key)
    }

    fn from_key(key: rsa::VerifyingKey) -> Result<Self, Error> {
        Ok(Self {
            encoding: RsaPublicKeyDer(Buffer::write(|output| key.to_pkcs1_der(output))?, []),
            key,
        })
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo` naming
    /// `rsaEncryption`.
    pub fn to_spki(&self) -> Spki {
        Spki(Buffer::encode(|output| self.key.to_spki_der(output)))
    }

    /// The modulus's length in bytes, which is also its signatures' length,
    /// so a caller can refuse a small key before it verifies anything.
    pub fn modulus_len(&self) -> usize {
        self.key.modulus_len_bits().div_ceil(8)
    }

    /// Verifies `signature` over `message` with `algorithm`, refusing a
    /// malformed signature, and refusing the key if its modulus is below
    /// the algorithm's floor.
    pub fn verify(
        &self,
        algorithm: &VerificationAlgorithm,
        message: &[u8],
        signature: &[u8],
    ) -> Result<(), Error> {
        if self.key.modulus_len_bits() < algorithm.min_bits {
            return Err(KeyFormatError::RsaModulus.into());
        }
        (algorithm.verify)(&self.key, algorithm.verification.salt(), signature, message)
    }
}

    pub static PKCS1_SHA256: VerificationAlgorithm = verification(PKCS1_SHA256_SCHEME, MIN_BITS);

    pub static PSS_SHA256: VerificationAlgorithm = verification(PSS_SHA256_SCHEME, MIN_BITS);

```

The model departs from the Rust in these ways, and adds no axiom:

- A `VerificationAlgorithm` is its `min_bits` and its `verify` with its
  `verification.salt()` passed, as `(key, signature, message)`:
  `algorithm` pairs the `verification` with that `verification`'s own
  `verifier()`, as the quote's only `VerificationAlgorithm` literal shows;
  `admin/prove` checks it is the only one.
- `verify::PKCS1_SHA256` is `verification(PKCS1_SHA256_SCHEME, 2048)`:
  `min_bits` 2048, as PKCS#1 v1.5 keeps the floor, `verify`
  `|key, _, s, m| key.verify_pkcs1_sha256(s, m)`, and salt
  `Some(PssSalt::Hash)`, which it ignores. `verify::PSS_SHA256` is
  `verification(PSS_SHA256_SCHEME, 2048)`: `min_bits` 2048, above PSS's
  8 · (32 + 32 + 1) + 2 = 522, `verify` `VerifyingKey::verify_pss_sha256`,
  and salt `Some(PssSalt::Hash)`.
- A `PublicKey`'s `encoding` is its `RsaPublicKeyDer`'s `Buffer`, as the
  empty array beside it holds nothing, of `MAX_PUBLIC_KEY_LEN`,
  8192 / 8 + 64 = 1088 bytes.
- `PublicKey::from_components` takes the components' `n` and `e` as
  slices, what their `as_ref` returns.
- `Buffer::write` is `SignatureBuffer`'s. The encoding it writes,
  `to_pkcs1_der`, is DER, which the ✓ leaves out, and opaque, as are
  `pkcs1_components` and `spki_components`, which `from_pkcs1_der` and
  `from_spki_der` read their components with.
- `?` is a `match`, since each error it passes on is already an `Error`.
- `to_spki`, `modulus_len`, and `PublicKey`'s `AsRef`, which no theorem here
  is about, are not modelled.

Drops are not modelled, as everywhere in the translation.
-/

namespace rind.x86_64

/-- `VerificationAlgorithm`: the smallest modulus it accepts, and its
`verify` with its `verification.salt()` passed, as `(key, signature,
message)`. -/
structure high.signature.rsa.VerificationAlgorithm where
  min_bits : Std.Usize
  verify : high.rsa.VerifyingKey → Slice Std.U8 → Slice Std.U8 →
    Result (core.result.Result Unit error.Error)

/-- `PublicKey`, whose `encoding` is its `RsaPublicKeyDer`'s `Buffer`. -/
structure high.signature.rsa.PublicKey where
  key : high.rsa.VerifyingKey
  encoding : high.signature.Buffer 1088#usize

/-- `PublicKey::from_key`. -/
def high.signature.rsa.PublicKey.from_key (key : high.rsa.VerifyingKey) :
    Result (core.result.Result high.signature.rsa.PublicKey error.Error) := do
  let b ← high.signature.Buffer.write 1088#usize (high.rsa.VerifyingKey.to_pkcs1_der key)
  match b with
  | .Ok encoding => ok (.Ok { key, encoding })
  | .Err e => ok (.Err e)

/-- `PublicKey::new`. -/
def high.signature.rsa.PublicKey.new (der : Slice Std.U8) :
    Result (core.result.Result high.signature.rsa.PublicKey error.Error) := do
  let r ← high.rsa.VerifyingKey.from_pkcs1_der der
  match r with
  | .Ok key => high.signature.rsa.PublicKey.from_key key
  | .Err e => ok (.Err e)

/-- `PublicKey::from_spki`. -/
def high.signature.rsa.PublicKey.from_spki (der : Slice Std.U8) :
    Result (core.result.Result high.signature.rsa.PublicKey error.Error) := do
  let r ← high.rsa.VerifyingKey.from_spki_der der
  match r with
  | .Ok key => high.signature.rsa.PublicKey.from_key key
  | .Err e => ok (.Err e)

/-- `PublicKey::from_components`, with the components' `n` and `e`. -/
def high.signature.rsa.PublicKey.from_components (n e : Slice Std.U8) :
    Result (core.result.Result high.signature.rsa.PublicKey error.Error) := do
  let r ← high.rsa.VerifyingKey.from_components n e
  match r with
  | .Ok key => high.signature.rsa.PublicKey.from_key key
  | .Err e => ok (.Err e)

/-- `PublicKey::verify`. -/
def high.signature.rsa.PublicKey.verify (self : high.signature.rsa.PublicKey)
    (algorithm : high.signature.rsa.VerificationAlgorithm) (message signature : Slice Std.U8) :
    Result (core.result.Result Unit error.Error) := do
  let bits ← high.rsa.VerifyingKey.modulus_len_bits self.key
  if bits < algorithm.min_bits then
    let e ← core.convert.IntoFrom.into error.Error.Insts.CoreConvertFromKeyFormatError
      error.KeyFormatError.RsaModulus
    ok (.Err e)
  else algorithm.verify self.key signature message

/-- The `verify::PKCS1_SHA256` static, `verification(PKCS1_SHA256_SCHEME, MIN_BITS)`. -/
def high.signature.rsa.verify.PKCS1_SHA256 : high.signature.rsa.VerificationAlgorithm where
  min_bits := 2048#usize
  verify key signature message := high.rsa.VerifyingKey.verify_pkcs1_sha256 key signature message

/-- The `verify::PSS_SHA256` static, `verification(PSS_SHA256_SCHEME, MIN_BITS)`. -/
def high.signature.rsa.verify.PSS_SHA256 : high.signature.rsa.VerificationAlgorithm where
  min_bits := 2048#usize
  verify key signature message :=
    high.rsa.VerifyingKey.verify_pss_sha256 key (some .Hash) signature message

/-- A computation that meets a post returns a value meeting it. -/
theorem spec_eq_ok {α : Type} {m : Result α} {P : α → Prop} (h : WP.spec m P) : ∃ x, m = ok x ∧ P x := by
  cases m with
  | ret x => exact ⟨x, rfl, (WP.spec_ok x).mp h⟩
  | vis e k => exact absurd h (by simp [WP.spec_vis])
  | div => exact absurd h (by simp [WP.spec_div])

/-- A bind that returns ran its first step to a value. -/
theorem bind_eq_ok {α β : Type} {m : Result α} {k : α → Result β} {y : β} (h : Std.bind m k = ok y) :
    ∃ x, m = ok x ∧ k x = ok y := by
  cases m with
  | ret x => exact ⟨x, rfl, by simpa using h⟩
  | vis e k' =>
    have : WP.spec (Std.bind (vis e k') k) (fun _ => True) := by rw [h]; simp [WP.spec_ok]
    rw [bind_vis, WP.spec_vis] at this; exact this.elim
  | div =>
    have : WP.spec (Std.bind div k) (fun _ => True) := by rw [h]; simp [WP.spec_ok]
    rw [bind_div, WP.spec_div] at this; exact this.elim

/-- A public key `PublicKey::from_key` returns holds the key it was given,
which for a loaded `(N, E)` key has a modulus of 1024 to 8192 bits. -/
theorem from_key_ok {key : high.rsa.VerifyingKey} {N E : Nat} (hk : KeyLoaded key N E)
    {pk : high.signature.rsa.PublicKey}
    (hpk : high.signature.rsa.PublicKey.from_key key = ok (.Ok pk)) :
    KeyLoaded pk.key N E ∧ 1024 ≤ N.size ∧ N.size ≤ 8192 := by
  unfold high.signature.rsa.PublicKey.from_key at hpk
  obtain ⟨b, -, hb⟩ := bind_eq_ok hpk
  split at hb
  · simp only [ok.injEq, core.result.Result.Ok.injEq] at hb
    subst hb
    have hmin := hk.1.2.2.2.2.2.2.2.1
    have hmax := hk.1.2.2.2.2.2.2.2.2
    rw [hk.2.1] at hmin hmax
    exact ⟨hk, hmin, hmax⟩
  · simp at hb

/-- `PublicKey::new`: a key it returns is an `(N, E)` key of 1024 to 8192
bits, which `der` encodes as PKCS#1 DER the ✓ leaves out. -/
theorem rsa_signature_new_spec (hheld : low.entry.Entry.assert_held = ok ()) (der : Slice U8)
    (pk : high.signature.rsa.PublicKey) (hpk : high.signature.rsa.PublicKey.new der = ok (.Ok pk)) :
    ∃ N E, KeyLoaded pk.key N E ∧ 1024 ≤ N.size ∧ N.size ≤ 8192 := by
  unfold high.signature.rsa.PublicKey.new high.rsa.VerifyingKey.from_pkcs1_der at hpk
  obtain ⟨r, hr, hk⟩ := bind_eq_ok hpk
  obtain ⟨_, -, hr⟩ := bind_eq_ok hr
  obtain ⟨x, -, hr⟩ := bind_eq_ok hr
  rcases x with ⟨n, e⟩ | err
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at hr
    change high.rsa.VerifyingKey.from_unsigned n e = ok r at hr
    have hs := from_unsigned_spec hheld n e
    rw [hr, WP.spec_ok] at hs
    cases r with
    | Ok key => exact ⟨_, _, from_key_ok hs hk⟩
    | Err _ => simp at hk
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hr
    simp only [bind_tc_ok, ok.injEq] at hr
    subst hr
    simp at hk

/-- `PublicKey::from_spki`: a key it returns is an `(N, E)` key of 1024 to
8192 bits, which `der` encodes as `SubjectPublicKeyInfo` DER the ✓ leaves
out. -/
theorem rsa_signature_from_spki_spec (hheld : low.entry.Entry.assert_held = ok ()) (der : Slice U8)
    (pk : high.signature.rsa.PublicKey) (hpk : high.signature.rsa.PublicKey.from_spki der = ok (.Ok pk)) :
    ∃ N E, KeyLoaded pk.key N E ∧ 1024 ≤ N.size ∧ N.size ≤ 8192 := by
  unfold high.signature.rsa.PublicKey.from_spki high.rsa.VerifyingKey.from_spki_der at hpk
  obtain ⟨r, hr, hk⟩ := bind_eq_ok hpk
  obtain ⟨_, -, hr⟩ := bind_eq_ok hr
  obtain ⟨x, -, hr⟩ := bind_eq_ok hr
  rcases x with ⟨n, e⟩ | err
  · change high.rsa.VerifyingKey.from_unsigned n e = ok r at hr
    have hs := from_unsigned_spec hheld n e
    rw [hr, WP.spec_ok] at hs
    cases r with
    | Ok key => exact ⟨_, _, from_key_ok hs hk⟩
    | Err _ => simp at hk
  · simp only [ok.injEq] at hr
    subst hr
    simp at hk

/-- `PublicKey::from_components(&PublicKeyComponents { n, e })`: a key it
returns has the modulus and exponent `n` and `e` encode, of 1024 to 8192
bits. -/
theorem rsa_signature_from_components_spec (h : Runs) (hheld : low.entry.Entry.assert_held = ok ())
    (n e : Slice U8) (pk : high.signature.rsa.PublicKey)
    (hpk : high.signature.rsa.PublicKey.from_components n e = ok (.Ok pk)) :
    KeyLoaded pk.key (beNat n.val) (beNat e.val) ∧ 1024 ≤ (beNat n.val).size ∧ (beNat n.val).size ≤ 8192 := by
  unfold high.signature.rsa.PublicKey.from_components at hpk
  obtain ⟨r, hr, hk⟩ := bind_eq_ok hpk
  have hs := from_components_spec h hheld n e
  rw [hr, WP.spec_ok] at hs
  cases r with
  | Ok key => exact from_key_ok hs hk
  | Err _ => simp at hk

/-- `PublicKey::verify` with a loaded `(N, E)` key refuses it if its modulus
is under the algorithm's floor, and otherwise runs the algorithm's
`verify`. -/
theorem public_key_verify_spec (pk : high.signature.rsa.PublicKey)
    (algorithm : high.signature.rsa.VerificationAlgorithm) (N E : Nat) (hk : KeyLoaded pk.key N E)
    (message signature : Slice U8) {P : core.result.Result Unit error.Error → Prop}
    (hv : algorithm.min_bits.val ≤ N.size → algorithm.verify pk.key signature message ⦃ P ⦄) :
    high.signature.rsa.PublicKey.verify pk algorithm message signature ⦃ r =>
      if N.size < algorithm.min_bits.val then r = .Err (.KeyRejected .RsaModulus) else P r ⦄ := by
  obtain ⟨hinv, hN, -, -⟩ := hk
  unfold high.signature.rsa.PublicKey.verify high.rsa.VerifyingKey.modulus_len_bits
    mid.rsa_pub.RsaPublicKey.modulus_len_bits
  step with len_bits_spec pk.key.n hinv.2.1 as ⟨bits, hbits⟩
  rw [hN] at hbits
  split
  · rename_i hlt
    have hlt' : N.size < algorithm.min_bits.val := by rw [← hbits]; exact hlt
    simp [error.Error.Insts.CoreConvertFromKeyFormatError.from, hlt']
  · rename_i hge
    have hge' : ¬ N.size < algorithm.min_bits.val := by rw [← hbits]; exact hge
    apply WP.spec_mono (hv (by omega))
    intro r hr
    simpa [hge'] using hr

/-- `PublicKey::verify(&verify::PKCS1_SHA256, ..)` with a loaded `(N, E)`
key: refused if the modulus is under 2048 bits, and otherwise
RSASSA-PKCS1-V1_5-VERIFY with SHA-256, over Montgomery products at its
width. -/
theorem rsa_pkcs1_sha256_verify_spec (h : Runs) (hb : Sha256Blocks) (pk : high.signature.rsa.PublicKey)
    (N E : Nat) (hk : KeyLoaded pk.key N E) (hP : MontProducts ((N.size + 63) / 64))
    (message signature : Slice U8) (hm : message.length ≤ maxInput) :
    high.signature.rsa.PublicKey.verify pk high.signature.rsa.verify.PKCS1_SHA256 message signature ⦃ r =>
      if N.size < 2048 then r = .Err (.KeyRejected .RsaModulus)
      else (r = .Ok () ↔ rsassaPkcs1v15Verify N E sha256.hash digestInfoSha256 (bv message.val)
        (bv signature.val)) ⦄ := by
  refine public_key_verify_spec pk _ N E hk message signature fun _ => ?_
  obtain ⟨hinv, hN, hE, hused⟩ := hk
  dsimp only [high.signature.rsa.verify.PKCS1_SHA256]
  rw [← hN, ← hE]
  exact verify_pkcs1_sha256_spec h hb pk.key hinv (by rw [hused, ← hN]; exact hN ▸ hP) signature message hm

/-- `PublicKey::verify(&verify::PSS_SHA256, ..)` with a loaded `(N, E)` key:
refused if the modulus is under 2048 bits, and otherwise RSASSA-PSS-VERIFY
with SHA-256, MGF1 with SHA-256, and a 32-byte salt, over Montgomery
products at its width. -/
theorem rsa_pss_sha256_verify_spec (h : Runs) (hb : Sha256Blocks) (pk : high.signature.rsa.PublicKey)
    (N E : Nat) (hk : KeyLoaded pk.key N E) (hP : MontProducts ((N.size + 63) / 64))
    (message signature : Slice U8) (hm : message.length ≤ maxInput) :
    high.signature.rsa.PublicKey.verify pk high.signature.rsa.verify.PSS_SHA256 message signature ⦃ r =>
      if N.size < 2048 then r = .Err (.KeyRejected .RsaModulus)
      else (r = .Ok () ↔ RsassaPss N E sha256.hash 32 (bv message.val) (bv signature.val) (some 32)) ⦄ := by
  refine public_key_verify_spec pk _ N E hk message signature fun _ => ?_
  obtain ⟨hinv, hN, hE, hused⟩ := hk
  dsimp only [high.signature.rsa.verify.PSS_SHA256]
  rw [← hN, ← hE]
  have := verify_pss_sha256_spec h hb pk.key hinv (by rw [hused, ← hN]; exact hN ▸ hP) (some .Hash)
    signature message hm
  simpa [pssSaltLen] using this

/-- A 2048-bit modulus fills 32 words, whose Montgomery products rind runs
on s2n-bignum's proven routines on a CPU with BMI2 and ADX. -/
theorem rsa2048_mont_products (o : Option low.x86_64.cpu.HaveBmi2Adx)
    (hcheck : low.x86_64.cpu.HaveBmi2Adx.check = ok o) (hsome : o.isSome) (N : Nat) (hN : N.size = 2048) :
    MontProducts ((N.size + 63) / 64) := by
  rw [hN]
  exact mont_products o hcheck (Or.inr ⟨hsome, Or.inr rfl⟩)

end rind.x86_64
