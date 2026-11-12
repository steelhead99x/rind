import Rind.X86_64.SignatureDispatch
import Rind.X86_64.RsaKey
open Aeneas Aeneas.Std Result rind.spec rind.spec.rsa

/-!
# The signature API's RSA verification dispatch, modelled by hand

`PublicKey` reaches each RSA algorithm's key parser and verification through
function pointers in its `Rsa`, which Aeneas cannot translate, so the
translation stops below them and this file models the Rust above them for
RSASSA-PKCS1-v1_5 and RSASSA-PSS with SHA-256, `verify::RSA_PKCS1_SHA256`
and `verify::RSA_PSS_SHA256`. `SignatureDispatch` quotes `PublicKey`'s
`impl`, whose `new`, `from_components`, `parse_rsa`, `rsa`, and `verify`
this models too. `admin/prove` fails unless these quotes are still that
Rust, so a change to it is a change to this model:

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

impl<const N: usize> Buffer<N> {
    fn new() -> Self {
        Self {
            bytes: [0; N],
            len: 0,
        }
    }

    // `let else` rather than `ok_or(..)?` on the `&mut` span, whose
    // translation `proofs/` cannot check. The compiled code is the same.
    fn copy_from(bytes: &[u8]) -> Result<Self, Error> {
        let mut buffer = Self::new();
        let Some(span) = buffer.bytes.get_mut(..bytes.len()) else {
            return Err(Error::WrongLength);
        };
        span.copy_from_slice(bytes);
        buffer.len = bytes.len();
        Ok(buffer)
    }

    /// Runs `write`, which writes to the start of its argument and returns
    /// the written span.
    pub(super) fn write(
        write: impl FnOnce(&mut [u8]) -> Result<&[u8], Error>,
    ) -> Result<Self, Error> {
        let mut buffer = Self::new();
        buffer.len = write(&mut buffer.bytes)?.len();
        Ok(buffer)
    }

    /// Copies into a buffer at least as large.
    fn widen<const M: usize>(&self) -> Buffer<M> {
        const { assert!(M >= N) };
        let mut wide = Buffer::new();
        wide.bytes[..N].copy_from_slice(&self.bytes);
        wide.len = self.len;
        wide
    }

    /// Runs `encode` as [`Self::write`] does, for an encoder `N` is sized
    /// for.
    ///
    /// Every `N` holds the encoding of the largest key a loader accepts, so
    /// an encoder that runs out of room is a bug in rind, not bad input.
    pub(super) fn encode(encode: impl FnOnce(&mut [u8]) -> Result<&[u8], Error>) -> Self {
        Self::write(encode).expect("sized for the largest key")
    }
}

pub struct RsaVerificationAlgorithm {
    rsa: Rsa,
    algorithm: VerificationAlgorithm,
}

impl AsRef<VerificationAlgorithm> for RsaVerificationAlgorithm {
    fn as_ref(&self) -> &VerificationAlgorithm {
        &self.algorithm
    }
}

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

type RsaVerify = fn(&rsa::VerifyingKey, Option<PssSalt>, &[u8], &[u8]) -> Result<(), Error>;

struct RsaVerifier {
    key: rsa::VerifyingKey,
    verify: RsaVerify,
}

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

struct Rsa {
    verification: RsaVerification,
    min_bits: usize,
    verify: RsaVerify,
    parse: fn(Self, &[u8]) -> Result<PublicKey, Error>,
}

impl fmt::Debug for Rsa {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Rsa")
            .field("verification", &self.verification)
            .field("min_bits", &self.min_bits)
            .finish()
    }
}

impl Rsa {
    /// Refuses `key` if its modulus is below this algorithm's floor.
    fn check(self, key: rsa::VerifyingKey) -> Result<rsa::VerifyingKey, Error> {
        match key.modulus_len_bits() >= self.min_bits {
            true => Ok(key),
            false => Err(KeyFormatError::RsaModulus.into()),
        }
    }
}

const fn rsa_verification(scheme: RsaScheme, min_bits: usize) -> RsaVerificationAlgorithm {
    rsa_algorithm(RsaVerification::Scheme(scheme), scheme.min_bits(min_bits))
}

const fn rsa_algorithm(verification: RsaVerification, min_bits: usize) -> RsaVerificationAlgorithm {
    let rsa = Rsa {
        verification,
        min_bits,
        verify: verification.verifier(),
        parse: PublicKey::parse_rsa,
    };
    RsaVerificationAlgorithm {
        rsa,
        algorithm: VerificationAlgorithm(Verification::Rsa(rsa)),
    }
}

const PKCS1_SHA256: RsaScheme = RsaScheme {
    padding: RsaPadding::Pkcs1,
    hash: HashId::Sha256,
};

const PSS_SHA256: RsaScheme = RsaScheme::pss(HashId::Sha256, PssSalt::Hash);

pub(super) const RSA_MIN_BITS: usize = 2048;

    pub static RSA_PKCS1_SHA256: RsaVerificationAlgorithm =
        rsa_verification(PKCS1_SHA256, RSA_MIN_BITS);

    pub static RSA_PSS_SHA256: RsaVerificationAlgorithm =
        rsa_verification(PSS_SHA256, RSA_MIN_BITS);

```

The model departs from the Rust in these ways, and adds no axiom:

- An `RsaVerificationAlgorithm` is its `Rsa`, and an `Rsa` its `min_bits`
  and its `verify` with its `verification.salt()` passed, as
  `(key, signature, message)`: its `algorithm` is `Verification::Rsa` of
  that `Rsa`, and `PublicKey::verify` passes the `verification` that
  `PublicKey::rsa` paired with the same `Rsa`'s `verify`. Its `parse` is
  `PublicKey::parse_rsa`, which `rsa_algorithm` alone sets, as the quotes'
  every `Rsa` literal shows; `admin/prove` checks they hold each one.
- `Verification::Rsa` is `Verification::Other`, holding what
  `PublicKey::new` does for it, `(rsa.parse)(rsa, bytes)`, which
  `RsaVerificationAlgorithm.as_ref` gives. `Parsed::Rsa` is
  `Parsed::Other`, holding what `PublicKey::verify` does for it, which
  `PublicKey::rsa` gives.
- `verify::RSA_PKCS1_SHA256` is `rsa_verification(PKCS1_SHA256, 2048)`:
  `min_bits` 2048, as PKCS#1 v1.5 keeps the floor, `verify`
  `|key, _, s, m| key.verify_pkcs1_sha256(s, m)`, and salt
  `Some(PssSalt::Hash)`, which it ignores. `verify::RSA_PSS_SHA256` is
  `rsa_verification(PSS_SHA256, 2048)`: `min_bits` 2048, above PSS's
  8 · (32 + 32 + 1) + 2 = 522, `verify` `VerifyingKey::verify_pss_sha256`,
  and salt `Some(PssSalt::Hash)`.
- `PublicKey::from_components` takes the components' `n` and `e` as
  slices, what their `as_ref` returns.
- `Buffer::write` takes `write` as a Lean function, as Aeneas cannot
  translate a closure that returns a borrow of its argument. The encoding
  it writes, `to_pkcs1_der`, is DER, which the ✓ leaves out, and opaque,
  as is `der_components`, which `from_der` reads its components with.
- `?` is a `match`, since each error it passes on is already an `Error`.

Drops are not modelled, as everywhere in the translation.
-/

namespace rind.x86_64

/-- `Buffer::write`, with `write` a Lean function. -/
def high.signature.Buffer.write (N : Std.Usize)
    (write : Slice Std.U8 → Result (core.result.Result (Slice Std.U8) error.Error × Slice Std.U8)) :
    Result (core.result.Result (high.signature.Buffer N) error.Error) := do
  let buffer ← high.signature.Buffer.new N
  let (s, to_slice_mut_back) ← lift (Array.to_slice_mut buffer.bytes)
  let r ← write s
  match r.1 with
  | .Ok span => ok (.Ok { bytes := to_slice_mut_back r.2, len := span.len })
  | .Err e => ok (.Err e)

/-- `Rsa`: the smallest modulus it accepts, and its `verify` with its
`verification.salt()` passed, as `(key, signature, message)`. -/
structure high.signature.Rsa where
  min_bits : Std.Usize
  verify : high.rsa.VerifyingKey → Slice Std.U8 → Slice Std.U8 →
    Result (core.result.Result Unit error.Error)

/-- `RsaVerificationAlgorithm`, which is its `Rsa`. -/
abbrev high.signature.RsaVerificationAlgorithm := high.signature.Rsa

/-- `Rsa::check`. -/
def high.signature.Rsa.check (self : high.signature.Rsa) (key : high.rsa.VerifyingKey) :
    Result (core.result.Result high.rsa.VerifyingKey error.Error) := do
  let bits ← high.rsa.VerifyingKey.modulus_len_bits key
  if bits >= self.min_bits then ok (.Ok key)
  else ok (.Err (.KeyRejected .RsaModulus))

/-- `PublicKey::rsa`, whose `Parsed::Rsa` verifies with `rsa.verify`. -/
def high.signature.PublicKey.rsa (rsa : high.signature.Rsa) (key : high.rsa.VerifyingKey) :
    Result (core.result.Result high.signature.PublicKey error.Error) := do
  let r ← rsa.check key
  match r with
  | .Ok key =>
    let b ← high.signature.Buffer.write 2592#usize (high.rsa.VerifyingKey.to_pkcs1_der key)
    match b with
    | .Ok encoding => ok (.Ok { encoding, key := .Other fun message signature => rsa.verify key signature message })
    | .Err e => ok (.Err e)
  | .Err e => ok (.Err e)

/-- `PublicKey::parse_rsa`. -/
def high.signature.PublicKey.parse_rsa (rsa : high.signature.Rsa) (bytes : Slice Std.U8) :
    Result (core.result.Result high.signature.PublicKey error.Error) := do
  let r ← high.rsa.VerifyingKey.from_der bytes
  match r with
  | .Ok key => high.signature.PublicKey.rsa rsa key
  | .Err e => ok (.Err e)

/-- `RsaVerificationAlgorithm`'s `AsRef<VerificationAlgorithm>`: its
`algorithm`, `Verification::Rsa` of its `Rsa`, with what `PublicKey::new`
does for it, `(rsa.parse)(rsa, bytes)`. -/
def high.signature.RsaVerificationAlgorithm.as_ref (self : high.signature.RsaVerificationAlgorithm) :
    high.signature.Verification :=
  .Other (high.signature.PublicKey.parse_rsa self)

/-- `PublicKey::from_components`, with the components' `n` and `e`. -/
def high.signature.PublicKey.from_components (algorithm : high.signature.RsaVerificationAlgorithm)
    (n e : Slice Std.U8) : Result (core.result.Result high.signature.PublicKey error.Error) := do
  let r ← high.rsa.VerifyingKey.from_components n e
  match r with
  | .Ok key => high.signature.PublicKey.rsa algorithm key
  | .Err e => ok (.Err e)

/-- The `verify::RSA_PKCS1_SHA256` static, `rsa_verification(PKCS1_SHA256, RSA_MIN_BITS)`. -/
def high.signature.verify.RSA_PKCS1_SHA256 : high.signature.RsaVerificationAlgorithm where
  min_bits := 2048#usize
  verify key signature message := high.rsa.VerifyingKey.verify_pkcs1_sha256 key signature message

/-- The `verify::RSA_PSS_SHA256` static, `rsa_verification(PSS_SHA256, RSA_MIN_BITS)`. -/
def high.signature.verify.RSA_PSS_SHA256 : high.signature.RsaVerificationAlgorithm where
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

/-- A key `PublicKey::rsa` returns has a modulus of at least the
algorithm's floor, and verifies with the algorithm's `verify`. -/
theorem public_key_rsa_ok (rsa : high.signature.Rsa) (key : high.rsa.VerifyingKey) (N E : Nat)
    (hk : KeyLoaded key N E) (pk : high.signature.PublicKey)
    (hpk : high.signature.PublicKey.rsa rsa key = ok (.Ok pk)) :
    rsa.min_bits.val ≤ N.size ∧
      pk.key = .Other fun message signature => rsa.verify key signature message := by
  obtain ⟨hinv, hN, -, -⟩ := hk
  have hlb := len_bits_spec key.n hinv.2.1
  unfold high.signature.PublicKey.rsa high.signature.Rsa.check high.rsa.VerifyingKey.modulus_len_bits
    mid.rsa_pub.RsaPublicKey.modulus_len_bits at hpk
  obtain ⟨bits, hm, hbits⟩ := spec_eq_ok hlb
  rw [hN] at hbits
  rw [hm] at hpk
  simp only [bind_ok] at hpk
  by_cases hge : bits ≥ rsa.min_bits
  · rw [ite_eq_left hge, bind_ok] at hpk
    simp only at hpk
    obtain ⟨w, -, hw⟩ := bind_eq_ok hpk
    split at hw
    · simp only [ok.injEq, core.result.Result.Ok.injEq] at hw
      subst hw
      refine ⟨?_, rfl⟩
      have : bits.val ≥ rsa.min_bits.val := hge
      omega
    · simp at hw
  · rw [ite_eq_right hge, bind_ok] at hpk
    simp at hpk

/-- A key `PublicKey::from_components` returns for an RSA algorithm is the
one its components encode, of at least the algorithm's floor, and verifies
with the algorithm's `verify`. -/
theorem from_components_rsa_ok (h : Runs) (hheld : low.entry.Entry.assert_held = ok ())
    (rsa : high.signature.Rsa) (n e : Slice U8) (pk : high.signature.PublicKey)
    (hpk : high.signature.PublicKey.from_components rsa n e = ok (.Ok pk)) :
    rsa.min_bits.val ≤ (beNat n.val).size ∧ ∃ key, KeyLoaded key (beNat n.val) (beNat e.val) ∧
      pk.key = .Other fun message signature => rsa.verify key signature message := by
  unfold high.signature.PublicKey.from_components at hpk
  obtain ⟨r, hr, hk⟩ := bind_eq_ok hpk
  have hs := from_components_spec h hheld n e
  rw [hr, WP.spec_ok] at hs
  split at hk
  · rename_i key
    obtain ⟨hmin, hpk'⟩ := public_key_rsa_ok rsa key _ _ hs pk hk
    exact ⟨hmin, key, hs, hpk'⟩
  · simp at hk

/-- A key `PublicKey::new` returns for an RSA algorithm, from DER, is some
`(N, E)` key of at least the algorithm's floor, and verifies with the
algorithm's `verify`. -/
theorem new_rsa_ok (hheld : low.entry.Entry.assert_held = ok ())
    (rsa : high.signature.Rsa) (bytes : Slice U8) (pk : high.signature.PublicKey)
    (hpk : high.signature.PublicKey.new (high.signature.RsaVerificationAlgorithm.as_ref rsa) bytes =
      ok (.Ok pk)) :
    ∃ N E key, KeyLoaded key N E ∧ rsa.min_bits.val ≤ N.size ∧
      pk.key = .Other fun message signature => rsa.verify key signature message := by
  unfold high.signature.PublicKey.new high.signature.RsaVerificationAlgorithm.as_ref
    high.signature.PublicKey.parse_rsa high.rsa.VerifyingKey.from_der at hpk
  dsimp only at hpk
  obtain ⟨r, hr, hk⟩ := bind_eq_ok hpk
  obtain ⟨_, -, hr⟩ := bind_eq_ok hr
  obtain ⟨x, -, hr⟩ := bind_eq_ok hr
  split at hr
  · rename_i ne
    obtain ⟨n', e'⟩ := ne
    have hr' : high.rsa.VerifyingKey.from_unsigned n' e' = ok r := hr
    have hs := from_unsigned_spec hheld n' e'
    rw [hr', WP.spec_ok] at hs
    cases r with
    | Ok key =>
      obtain ⟨hmin, hpk'⟩ := public_key_rsa_ok rsa key _ _ hs pk hk
      exact ⟨_, _, key, hs, hmin, hpk'⟩
    | Err _ => simp at hk
  · simp only [ok.injEq] at hr; subst hr; simp at hk

/-- A public key that verifies with `RSA_PKCS1_SHA256`'s `verify` over a
loaded `(N, E)` key computes RSASSA-PKCS1-V1_5-VERIFY with SHA-256. -/
theorem verify_rsa_pkcs1_sha256 (h : Runs) (hb : Sha256Blocks) (pk : high.signature.PublicKey)
    (key : high.rsa.VerifyingKey) (N E : Nat) (hk : KeyLoaded key N E)
    (hpk : pk.key = .Other fun message signature =>
      high.signature.verify.RSA_PKCS1_SHA256.verify key signature message)
    (hP : MontProducts ((N.size + 63) / 64)) (message signature : Slice U8)
    (hm : message.length ≤ maxInput) :
    high.signature.PublicKey.verify pk message signature ⦃ r =>
      r = .Ok () ↔ rsassaPkcs1v15Verify N E sha256.hash digestInfoSha256 (bv message.val)
        (bv signature.val) ⦄ := by
  obtain ⟨hinv, hN, hE, hused⟩ := hk
  unfold high.signature.PublicKey.verify
  rw [hpk]
  dsimp only [high.signature.verify.RSA_PKCS1_SHA256]
  rw [← hN, ← hE]
  exact verify_pkcs1_sha256_spec h hb key hinv (by rw [hused, ← hN]; exact hN ▸ hP) signature message hm

/-- A public key that verifies with `RSA_PSS_SHA256`'s `verify` over a
loaded `(N, E)` key computes RSASSA-PSS-VERIFY with SHA-256, MGF1 with
SHA-256, and a 32-byte salt. -/
theorem verify_rsa_pss_sha256 (h : Runs) (hb : Sha256Blocks) (pk : high.signature.PublicKey)
    (key : high.rsa.VerifyingKey) (N E : Nat) (hk : KeyLoaded key N E)
    (hpk : pk.key = .Other fun message signature =>
      high.signature.verify.RSA_PSS_SHA256.verify key signature message)
    (hP : MontProducts ((N.size + 63) / 64)) (message signature : Slice U8)
    (hm : message.length ≤ maxInput) :
    high.signature.PublicKey.verify pk message signature ⦃ r =>
      r = .Ok () ↔ RsassaPss N E sha256.hash 32 (bv message.val) (bv signature.val) (some 32) ⦄ := by
  obtain ⟨hinv, hN, hE, hused⟩ := hk
  unfold high.signature.PublicKey.verify
  rw [hpk]
  dsimp only [high.signature.verify.RSA_PSS_SHA256]
  rw [← hN, ← hE]
  have := verify_pss_sha256_spec h hb key hinv (by rw [hused, ← hN]; exact hN ▸ hP) (some .Hash) signature
    message hm
  simpa [pssSaltLen] using this

/-- `PublicKey::new(&verify::RSA_PKCS1_SHA256, der)`: a key it returns is an
`(N, E)` key of 2048 to 8192 bits, which `der` encodes as DER the ✓ leaves
out, and its `verify` computes RSASSA-PKCS1-V1_5-VERIFY with SHA-256 for that key, over
Montgomery products at its width. -/
theorem rsa_pkcs1_sha256_new_spec (h : Runs) (hb : Sha256Blocks) (bytes : Slice U8)
    (pk : high.signature.PublicKey)
    (hpk : high.signature.PublicKey.new
      (high.signature.RsaVerificationAlgorithm.as_ref high.signature.verify.RSA_PKCS1_SHA256) bytes = ok (.Ok pk)) :
    ∃ N E, 2048 ≤ N.size ∧ N.size ≤ 8192 ∧ ∀ message signature : Slice U8,
      MontProducts ((N.size + 63) / 64) → message.length ≤ maxInput →
      high.signature.PublicKey.verify pk message signature ⦃ r =>
        r = .Ok () ↔ rsassaPkcs1v15Verify N E sha256.hash digestInfoSha256 (bv message.val)
            (bv signature.val) ⦄ := by
  obtain ⟨N, E, key, hk, hmin, hpk'⟩ := new_rsa_ok hb.held _ bytes pk hpk
  have hmax := hk.1.2.2.2.2.2.2.2.2
  rw [hk.2.1] at hmax
  exact ⟨N, E, hmin, hmax, fun m s hP hm => verify_rsa_pkcs1_sha256 h hb pk key N E hk hpk' hP m s hm⟩

/-- `PublicKey::from_components(&verify::RSA_PKCS1_SHA256, &PublicKeyComponents { n, e })`:
a key it returns has the modulus and exponent `n` and `e` encode, of 2048
to 8192 bits, and its `verify` computes RSASSA-PKCS1-V1_5-VERIFY with SHA-256 for that key, over
Montgomery products at its width. -/
theorem rsa_pkcs1_sha256_from_components_spec (h : Runs) (hb : Sha256Blocks) (n e : Slice U8)
    (pk : high.signature.PublicKey)
    (hpk : high.signature.PublicKey.from_components high.signature.verify.RSA_PKCS1_SHA256 n e = ok (.Ok pk)) :
    2048 ≤ (beNat n.val).size ∧ (beNat n.val).size ≤ 8192 ∧ ∀ message signature : Slice U8,
      MontProducts (((beNat n.val).size + 63) / 64) → message.length ≤ maxInput →
      high.signature.PublicKey.verify pk message signature ⦃ r =>
        r = .Ok () ↔ rsassaPkcs1v15Verify (beNat n.val) (beNat e.val) sha256.hash digestInfoSha256 (bv message.val)
            (bv signature.val) ⦄ := by
  obtain ⟨hmin, key, hk, hpk'⟩ := from_components_rsa_ok h hb.held _ n e pk hpk
  have hmax := hk.1.2.2.2.2.2.2.2.2
  rw [hk.2.1] at hmax
  exact ⟨hmin, hmax, fun m s hP hm => verify_rsa_pkcs1_sha256 h hb pk key _ _ hk hpk' hP m s hm⟩

/-- `PublicKey::new(&verify::RSA_PSS_SHA256, der)`: a key it returns is an
`(N, E)` key of 2048 to 8192 bits, which `der` encodes as DER the ✓ leaves
out, and its `verify` computes RSASSA-PSS-VERIFY with SHA-256, MGF1 with SHA-256, and a 32-byte salt for that key, over
Montgomery products at its width. -/
theorem rsa_pss_sha256_new_spec (h : Runs) (hb : Sha256Blocks) (bytes : Slice U8)
    (pk : high.signature.PublicKey)
    (hpk : high.signature.PublicKey.new
      (high.signature.RsaVerificationAlgorithm.as_ref high.signature.verify.RSA_PSS_SHA256) bytes = ok (.Ok pk)) :
    ∃ N E, 2048 ≤ N.size ∧ N.size ≤ 8192 ∧ ∀ message signature : Slice U8,
      MontProducts ((N.size + 63) / 64) → message.length ≤ maxInput →
      high.signature.PublicKey.verify pk message signature ⦃ r =>
        r = .Ok () ↔ RsassaPss N E sha256.hash 32 (bv message.val) (bv signature.val) (some 32) ⦄ := by
  obtain ⟨N, E, key, hk, hmin, hpk'⟩ := new_rsa_ok hb.held _ bytes pk hpk
  have hmax := hk.1.2.2.2.2.2.2.2.2
  rw [hk.2.1] at hmax
  exact ⟨N, E, hmin, hmax, fun m s hP hm => verify_rsa_pss_sha256 h hb pk key N E hk hpk' hP m s hm⟩

/-- `PublicKey::from_components(&verify::RSA_PSS_SHA256, &PublicKeyComponents { n, e })`:
a key it returns has the modulus and exponent `n` and `e` encode, of 2048
to 8192 bits, and its `verify` computes RSASSA-PSS-VERIFY with SHA-256, MGF1 with SHA-256, and a 32-byte salt for that key, over
Montgomery products at its width. -/
theorem rsa_pss_sha256_from_components_spec (h : Runs) (hb : Sha256Blocks) (n e : Slice U8)
    (pk : high.signature.PublicKey)
    (hpk : high.signature.PublicKey.from_components high.signature.verify.RSA_PSS_SHA256 n e = ok (.Ok pk)) :
    2048 ≤ (beNat n.val).size ∧ (beNat n.val).size ≤ 8192 ∧ ∀ message signature : Slice U8,
      MontProducts (((beNat n.val).size + 63) / 64) → message.length ≤ maxInput →
      high.signature.PublicKey.verify pk message signature ⦃ r =>
        r = .Ok () ↔ RsassaPss (beNat n.val) (beNat e.val) sha256.hash 32 (bv message.val) (bv signature.val) (some 32) ⦄ := by
  obtain ⟨hmin, key, hk, hpk'⟩ := from_components_rsa_ok h hb.held _ n e pk hpk
  have hmax := hk.1.2.2.2.2.2.2.2.2
  rw [hk.2.1] at hmax
  exact ⟨hmin, hmax, fun m s hP hm => verify_rsa_pss_sha256 h hb pk key _ _ hk hpk' hP m s hm⟩

/-- A 2048-bit modulus fills 32 words, whose Montgomery products rind runs
on s2n-bignum's proven routines on a CPU with BMI2 and ADX. -/
theorem rsa2048_mont_products (o : Option low.x86_64.cpu.HaveBmi2Adx)
    (hcheck : low.x86_64.cpu.HaveBmi2Adx.check = ok o) (hsome : o.isSome) (N : Nat) (hN : N.size = 2048) :
    MontProducts ((N.size + 63) / 64) := by
  rw [hN]
  exact mont_products o hcheck (Or.inr ⟨hsome, Or.inr rfl⟩)


end rind.x86_64
