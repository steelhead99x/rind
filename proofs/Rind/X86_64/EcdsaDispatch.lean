import Rind.X86_64.SignatureDispatch
open Aeneas Aeneas.Std Result

/-!
# The signature API's P-256 ECDSA dispatch, modelled by hand

`EcdsaKeyPair` reaches each algorithm's code, and `PublicKey` each ECDSA
key's parser and verifier, through function pointers, and P-256's key
generation draws through a `dyn RandomSource`, none of which Aeneas can
translate, so the translation stops below them and this file models the Rust
above them for ECDSA on P-256 with SHA-256 and fixed-length signatures.
`admin/prove` fails unless these quotes are still that Rust, so a change to
it is a change to this model:

```rust
impl Curve for P256 {
    type PrivateKey = p256::StaticPrivateKey;
    type PublicKey = p256::VerifyingKey;
    type Scalar = p256::Scalar;

    fn oid() -> asn1::ObjectId {
        asn1::oid::id_prime256v1.clone()
    }

    fn generate_random_key(rng: &mut impl RandomSource) -> Result<p256::StaticPrivateKey, Error> {
        p256::StaticPrivateKey::generate(rng)
    }
}

    pub(crate) fn generate(rng: &mut dyn RandomSource) -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        for _ in 0..64 {
            let mut r = [0u8; Scalar::BYTES];
            rng.fill(&mut r)?;
            low::ct::secret_slice(&r);
            if let Ok(p) = Self::from_bytes(&r) {
                return Ok(p);
            }
        }

        Err(Error::RngFailed)
    }

    pub(crate) fn generate(rng: &mut dyn RandomSource) -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        PrivateKey::generate(rng).map(Self)
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

macro_rules! with_hash {
    ($hash:expr, |$H:ident| $body:expr) => {
        match $hash {
            HashId::Sha256 => {
                type $H = Sha256;
                $body
            }
            HashId::Sha384 => {
                type $H = Sha384;
                $body
            }
            HashId::Sha512 => {
                type $H = Sha512;
                $body
            }
        }
    };
}

struct Ecdsa {
    curve: CurveId,
    hash: HashId,
    encoding: EcdsaEncoding,
}

macro_rules! with_ecdsa {
    ($ecdsa:expr, |$C:ident, $H:ident, $E:ident| $body:expr) => {{
        let ecdsa: Ecdsa = $ecdsa;
        with_hash!(ecdsa.hash, |$H| match ecdsa.encoding {
            EcdsaEncoding::Asn1 => {
                type $E = Asn1;
                with_curve!(ecdsa.curve, |$C| $body)
            }
            EcdsaEncoding::Fixed => {
                type $E = Fixed;
                with_curve!(ecdsa.curve, |$C| $body)
            }
        })
    }};
}

macro_rules! with_curve {
    ($curve:expr, |$C:ident| $body:expr) => {
        match $curve {
            CurveId::P256 => {
                type $C = P256;
                $body
            }
            CurveId::P384 => {
                type $C = P384;
                $body
            }
            CurveId::P521 => {
                type $C = P521;
                $body
            }
        }
    };
}

trait Encoding {
    fn verify<C: Curve, H: SignatureHash>(
        key: &ecdsa::VerifyingKey<C>,
        signature: &[u8],
        message: &[u8],
    ) -> Result<(), Error>;

    fn sign<'a, C: Curve, H: SignatureHash>(
        key: &ecdsa::SigningKey<C>,
        output: &'a mut [u8],
        message: &[u8],
    ) -> Result<&'a [u8], Error>;

    fn verify_digest<C: Curve>(
        key: &ecdsa::VerifyingKey<C>,
        signature: &[u8],
        digest: &[u8],
    ) -> Result<(), Error>;

    /// Signs `digest`, drawing the nonce through `H`.
    fn sign_digest<'a, C: Curve, H: SignatureHash>(
        key: &ecdsa::SigningKey<C>,
        output: &'a mut [u8],
        digest: &[u8],
    ) -> Result<&'a [u8], Error>;
}

impl Encoding for Fixed {
    fn verify<C: Curve, H: SignatureHash>(
        key: &ecdsa::VerifyingKey<C>,
        signature: &[u8],
        message: &[u8],
    ) -> Result<(), Error> {
        key.verify::<H>(message, signature)
    }

    fn sign<'a, C: Curve, H: SignatureHash>(
        key: &ecdsa::SigningKey<C>,
        output: &'a mut [u8],
        message: &[u8],
    ) -> Result<&'a [u8], Error> {
        key.sign::<H>(message, output)
    }

    fn verify_digest<C: Curve>(
        key: &ecdsa::VerifyingKey<C>,
        signature: &[u8],
        digest: &[u8],
    ) -> Result<(), Error> {
        key.verify_digest(digest, signature)
    }

    fn sign_digest<'a, C: Curve, H: SignatureHash>(
        key: &ecdsa::SigningKey<C>,
        output: &'a mut [u8],
        digest: &[u8],
    ) -> Result<&'a [u8], Error> {
        key.sign_digest::<H>(digest, output)
    }
}

trait EcdsaCurve: Curve<PublicKey: Clone> + Sized + 'static {
    fn parsed(key: EcdsaVerifier<Self>, ecdsa: Ecdsa) -> Parsed;

    fn key(pair: EcdsaPair<Self>) -> EcdsaKey;
}

macro_rules! ecdsa_curve {
    ($curve:ident, $parsed:ident) => {
        impl EcdsaCurve for $curve {
            fn parsed(key: EcdsaVerifier<Self>, ecdsa: Ecdsa) -> Parsed {
                Parsed::$parsed(key, ecdsa)
            }

            fn key(pair: EcdsaPair<Self>) -> EcdsaKey {
                EcdsaKey::$curve(pair)
            }
        }
    };
}

ecdsa_curve!(P256, EcdsaP256);

struct EcdsaVerifier<C: Curve> {
    key: ecdsa::VerifyingKey<C>,
    verify: Verify<ecdsa::VerifyingKey<C>>,
    verify_digest: Verify<ecdsa::VerifyingKey<C>>,
}

impl<C: Curve> EcdsaVerifier<C> {
    fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        (self.verify)(&self.key, signature, message)
    }

    fn verify_digest(&self, digest: &[u8], signature: &[u8]) -> Result<(), Error> {
        (self.verify_digest)(&self.key, signature, digest)
    }
}

fn parse_ecdsa<C: EcdsaCurve, H: SignatureHash, E: Encoding>(
    ecdsa: Ecdsa,
    bytes: &[u8],
) -> Result<Parsed, Error> {
    let key = EcdsaVerifier {
        key: ecdsa::VerifyingKey::from_x962_uncompressed(bytes)?,
        verify: E::verify::<C, H>,
        verify_digest: E::verify_digest::<C>,
    };
    Ok(C::parsed(key, ecdsa))
}

const fn ecdsa_verification(
    curve: CurveId,
    hash: HashId,
    encoding: EcdsaEncoding,
) -> VerificationAlgorithm {
    let ecdsa = Ecdsa {
        curve,
        hash,
        encoding,
    };
    let parse = with_ecdsa!(ecdsa, |C, H, E| parse_ecdsa::<C, H, E> as _);
    let decompress: sec1::Decompress = match curve {
        CurveId::P256 => p256::PublicKey::decompress,
        CurveId::P384 => p384::PublicKey::decompress,
        CurveId::P521 => p521::PublicKey::decompress,
    };
    VerificationAlgorithm(Verification::Ecdsa(ecdsa, parse, decompress))
}

const fn ecdsa_signing(verification: &VerificationAlgorithm) -> EcdsaSigningAlgorithm {
    match verification.0 {
        Verification::Ecdsa(ecdsa, ..) => EcdsaSigningAlgorithm {
            ecdsa,
            load: with_ecdsa!(ecdsa, |C, H, E| EcdsaKeyPair::load::<C, H, E> as _),
        },
        _ => panic!("not an ECDSA algorithm"),
    }
}

pub struct EcdsaSigningAlgorithm {
    ecdsa: Ecdsa,
    // The only path to the algorithm's code, as `Verification`'s.
    load: fn(Ecdsa, EcdsaSource<'_>) -> Result<EcdsaKeyPair, Error>,
}

enum EcdsaSource<'a> {
    Generate,
    Pkcs8(&'a [u8]),
    Sec1(&'a [u8]),
    Scalar {
        scalar: &'a [u8],
        public_key: &'a [u8],
    },
}

pub struct EcdsaKeyPair {
    key: EcdsaKey,
    algorithm: Ecdsa,
}

enum EcdsaKey {
    P256(EcdsaPair<P256>),
    P384(EcdsaPair<P384>),
    P521(EcdsaPair<P521>),
}

struct EcdsaPair<C: EcdsaCurve> {
    signing: ecdsa::SigningKey<C>,
    ops: low::ZeroableRef<EcdsaOps<C>>,
}

type Write<K> = for<'a> fn(&K, &'a mut [u8]) -> Result<&'a [u8], Error>;

struct EcdsaOps<C: EcdsaCurve> {
    public_key: fn(&ecdsa::SigningKey<C>) -> ecdsa::EncodedPoint,
    parse: fn(&[u8]) -> Result<ecdsa::VerifyingKey<C>, Error>,
    sign: Sign<ecdsa::SigningKey<C>>,
    sign_digest: Sign<ecdsa::SigningKey<C>>,
    verify: Verify<ecdsa::VerifyingKey<C>>,
    verify_digest: Verify<ecdsa::VerifyingKey<C>>,
    to_pkcs8: Write<ecdsa::SigningKey<C>>,
    to_scalar: Write<ecdsa::SigningKey<C>>,
    to_spki: Write<ecdsa::SigningKey<C>>,
}

impl<C: EcdsaCurve> EcdsaPair<C> {
    fn point(&self) -> ecdsa::EncodedPoint {
        (self.ops.get().public_key)(&self.signing)
    }

    fn public_key(&self, ecdsa: Ecdsa) -> PublicKey {
        let point = self.point();
        let key = EcdsaVerifier {
            key: (self.ops.get().parse)(point.as_ref()).expect("a key pair's own point"),
            verify: self.ops.get().verify,
            verify_digest: self.ops.get().verify_digest,
        };
        PublicKey {
            key: C::parsed(key, ecdsa),
            encoding: Buffer::copy_from(point.as_ref()).expect("sized for the largest key"),
        }
    }
}

macro_rules! on_ecdsa {
    ($key_pair:expr, |$pair:ident| $body:expr) => {
        match &$key_pair.key {
            EcdsaKey::P256($pair) => $body,
            EcdsaKey::P384($pair) => $body,
            EcdsaKey::P521($pair) => $body,
        }
    };
}

impl EcdsaKeyPair {
    /// Generates a key pair for `algorithm` from the system random source.
    pub fn generate(algorithm: &'static EcdsaSigningAlgorithm) -> Result<Self, Error> {
        (algorithm.load)(algorithm.ecdsa, EcdsaSource::Generate)
    }

    /// Loads a PKCS#8 v1 `ECPrivateKey` on `algorithm`'s curve.
    pub fn from_pkcs8(
        algorithm: &'static EcdsaSigningAlgorithm,
        der: &[u8],
    ) -> Result<Self, Error> {
        (algorithm.load)(algorithm.ecdsa, EcdsaSource::Pkcs8(der))
    }

    /// Loads a SEC1 (RFC 5915) `ECPrivateKey` on `algorithm`'s curve.
    ///
    /// This refuses PKCS#8, which [`Self::from_pkcs8`] takes: a caller always
    /// knows which of the two it holds.
    pub fn from_sec1(algorithm: &'static EcdsaSigningAlgorithm, der: &[u8]) -> Result<Self, Error> {
        (algorithm.load)(algorithm.ecdsa, EcdsaSource::Sec1(der))
    }

    /// Loads a fixed-length big-endian private scalar, refused unless
    /// `public_key`, an X9.62 uncompressed or compressed point, is its public
    /// key.
    ///
    /// This suits a JWK's `d` and `x`/`y`; prefer [`Self::from_pkcs8`] for
    /// stored keys.
    pub fn from_scalar_and_public_key(
        algorithm: &'static EcdsaSigningAlgorithm,
        scalar: &[u8],
        public_key: &[u8],
    ) -> Result<Self, Error> {
        let source = EcdsaSource::Scalar { scalar, public_key };
        (algorithm.load)(algorithm.ecdsa, source)
    }

    /// Loads a key pair for `ecdsa`, whose curve, hash, and encoding are `C`,
    /// `H`, and `E`.
    fn load<C: EcdsaCurve, H: SignatureHash, E: Encoding>(
        ecdsa: Ecdsa,
        source: EcdsaSource<'_>,
    ) -> Result<Self, Error> {
        let signing = match source {
            EcdsaSource::Generate => ecdsa::SigningKey::<C>::generate(),
            EcdsaSource::Pkcs8(der) => ecdsa::SigningKey::from_pkcs8_der(der),
            EcdsaSource::Sec1(der) => ecdsa::SigningKey::from_sec1_der(der),
            EcdsaSource::Scalar { scalar, public_key } => {
                ecdsa::SigningKey::from_private_key_and_public_key(scalar, public_key)
            }
        }?;
        let ops = const {
            &EcdsaOps {
                public_key: ecdsa::SigningKey::public_key_uncompressed,
                parse: ecdsa::VerifyingKey::from_x962_uncompressed,
                sign: E::sign::<C, H>,
                sign_digest: E::sign_digest::<C, H>,
                verify: E::verify::<C, H>,
                verify_digest: E::verify_digest::<C>,
                to_pkcs8: ecdsa::SigningKey::to_pkcs8_der,
                to_scalar: ecdsa::SigningKey::to_scalar,
                to_spki: ecdsa::SigningKey::to_spki_der,
            }
        };
        Ok(Self {
            key: C::key(EcdsaPair {
                signing,
                ops: low::ZeroableRef::new(ops),
            }),
            algorithm: ecdsa,
        })
    }

    /// Returns the public key, which verifies what this key pair signs.
    pub fn public_key(&self) -> PublicKey {
        on_ecdsa!(self, |pair| pair.public_key(self.algorithm))
    }

    /// Signs `message` with a fresh nonce.
    pub fn sign(&self, message: &[u8]) -> Result<Signature, Error> {
        Buffer::write(|output| {
            on_ecdsa!(self, |pair| (pair.ops.get().sign)(
                &pair.signing,
                output,
                message
            ))
        })
        .map(Signature)
    }

    /// Signs the message `digest` hashes, with a fresh nonce.
    ///
    /// The digest's hash, SHA-256, SHA-384, or SHA-512, replaces the
    /// algorithm's, which still fixes the signature's encoding, so
    /// [`Self::public_key`] verifies the signature over the message only if
    /// the hashes match; [`PublicKey::verify_digest`] verifies it in any
    /// case. Another hash is refused as [`Error::Unsupported`].
    pub fn sign_digest(&self, digest: &Digest) -> Result<Signature, Error> {
        let digest = signed_digest(digest)?;
        Buffer::write(|output| {
            on_ecdsa!(self, |pair| (pair.ops.get().sign_digest)(
                &pair.signing,
                output,
                digest
            ))
        })
        .map(Signature)
    }

    /// Encodes the private key as PKCS#8.
    pub fn to_pkcs8(&self) -> Pkcs8 {
        Pkcs8(Buffer::encode(|output| {
            on_ecdsa!(self, |pair| (pair.ops.get().to_pkcs8)(
                &pair.signing,
                output
            ))
        }))
    }

    /// Encodes the private key as a big-endian scalar exactly the curve's
    /// length, as a JWK's `d` and SEC1's `privateKey` hold it.
    ///
    /// This is what [`Self::from_scalar_and_public_key`] loads; prefer
    /// [`Self::to_pkcs8`] for stored keys.
    pub fn to_scalar(&self) -> EcdsaScalar {
        EcdsaScalar(Buffer::encode(|output| {
            on_ecdsa!(self, |pair| (pair.ops.get().to_scalar)(
                &pair.signing,
                output
            ))
        }))
    }

    /// Encodes the private key as a SEC1 (RFC 5915) `ECPrivateKey` naming
    /// its curve and holding its public key, as OpenSSL writes it.
    ///
    /// This is what [`Self::from_sec1`] loads; [`Self::to_pkcs8`] holds the
    /// same `ECPrivateKey` without its curve, which PKCS#8 names instead.
    pub fn to_sec1(&self) -> Sec1 {
        let _entry = low::Entry::new_secret();
        let scalar = self.to_scalar();
        let point = on_ecdsa!(self, |pair| pair.point());
        let curve = curve_oid(self.algorithm.curve);
        Sec1(Buffer::encode(|output| {
            sec1::encode(scalar.as_ref(), point.as_ref(), Some(curve), output)
        }))
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`.
    pub fn to_spki(&self) -> Spki {
        Spki(Buffer::encode(|output| {
            on_ecdsa!(self, |pair| (pair.ops.get().to_spki)(&pair.signing, output))
        }))
    }
}

    pub static ECDSA_P256_SHA256_FIXED: EcdsaSigningAlgorithm =
        ecdsa_signing(&verify::ECDSA_P256_SHA256_FIXED);

    pub static ECDSA_P256_SHA256_FIXED: VerificationAlgorithm =
        ecdsa_verification(CurveId::P256, HashId::Sha256, EcdsaEncoding::Fixed);

```

The model departs from the Rust in these ways, and adds no axiom:

- P-256's `generate_random_key` is `StaticPrivateKey::generate`, which is
  `PrivateKey::generate` over the source it is given, whose `dyn` is the
  source's `RandomSource` impl. `low::ct::secret_slice`, a ctgrind marker
  that computes nothing, is left out. `P256C` is the translated `Curve` impl
  for `P256` with `generate_random_key` replaced by this model, so the
  translated ECDSA code over it runs the model.
- `verify::ECDSA_P256_SHA256_FIXED` is `Verification::Other`, holding what
  `PublicKey::new` does for it: `with_ecdsa!` gives it
  `parse_ecdsa::<P256, Sha256, Fixed>`, then the key's bytes are copied.
- That parser's `Parsed::EcdsaP256` is `Parsed::Other`, holding what
  `PublicKey::verify` does for it: its `EcdsaVerifier`'s `verify`,
  `Fixed::verify::<P256, Sha256>`, which is `VerifyingKey::verify::<Sha256>`.
  Its `verify_digest`, read only by `PublicKey::verify_digest`, which no
  theorem here is about, and its `Ecdsa`, read only by `Debug`, are left
  out.
- An `EcdsaSigningAlgorithm` is the `load` it holds, applied to its `Ecdsa`;
  `with_ecdsa!` gives `sign::ECDSA_P256_SHA256_FIXED`
  `EcdsaKeyPair::load::<P256, Sha256, Fixed>`.
- An `EcdsaKey::P256` whose ops that `load` built is `P256Sha256Fixed`,
  holding its signing key, and `EcdsaKeyPair::sign` and `public_key` call
  those ops' `Fixed::sign::<P256, Sha256>`, which is
  `SigningKey::sign::<Sha256>`, `public_key`, which is
  `SigningKey::public_key_uncompressed`, `parse`, which is
  `VerifyingKey::from_x962_uncompressed`, and
  `Fixed::verify::<P256, Sha256>` directly: `load` builds every `EcdsaOps` and `EcdsaPair`, and its `ops` are
  reached only through `pair.ops.get()`. `admin/prove` checks that the quotes
  hold every mention of these. Every other key is `Other`, holding what
  `sign` and `public_key` do for it, and `ZeroableRef`, which holds the ops,
  is left out.
- `EcdsaKeyPair`'s `algorithm`, read only by `Debug` and the `Parsed` it
  passes to, is left out, as are `sign_digest`, `Debug`, and the `to_*`
  encoders, which no theorem here is about, and the ops' `sign_digest` and
  `verify_digest`, which only `sign_digest` and `verify_digest` read.
- `Buffer::write` takes `write` as a Lean function, as Aeneas cannot
  translate a closure that returns a borrow of its argument.
- PKCS#8 and SEC1 loading, DER the ✓ leaves out, is opaque.
- `?` is a `match`, since each error it passes on is already an `Error`.

Drops are not modelled, as everywhere in the translation.
`MAX_UNCOMPRESSED_PUBLIC_KEY_LEN` is P-521's 1 + 2 · 66 = 133, and
`SIGNATURE_MAX_LEN` is RSA's largest modulus, 8192 / 8 = 1024.
-/

namespace rind.x86_64

/-- The loop of `p256::PrivateKey::generate(rng)`, with `n` draws left. -/
def mid.p256.PrivateKey.generate_from_loop {T : Type} (inst : mid.rng.RandomSource T) :
    Nat → T → Result (core.result.Result mid.p256.PrivateKey error.Error × T)
  | 0, rng => ok (.Err .RngFailed, rng)
  | n + 1, rng => do
    let r := Array.repeat 32#usize 0#u8
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut r)
    let (r1, rng1, s1) ← inst.fill rng s
    match r1 with
    | .Err e => ok (.Err e, rng1)
    | .Ok () =>
      let p ← mid.p256.PrivateKey.from_bytes (to_slice_mut_back s1).to_slice
      match p with
      | .Ok p => ok (.Ok p, rng1)
      | .Err _ => mid.p256.PrivateKey.generate_from_loop inst n rng1

/-- `p256::StaticPrivateKey::generate(rng)`, which P-256's
`generate_random_key` is. -/
def mid.p256.StaticPrivateKey.generate {T : Type} (inst : mid.rng.RandomSource T) (rng : T) :
    Result (core.result.Result mid.p256.StaticPrivateKey error.Error × T) := do
  let _ ← low.entry.Entry.new_secret
  let _ ← low.entry.Entry.new_secret
  mid.p256.PrivateKey.generate_from_loop inst 64 rng

/-- P-256's `Curve` impl, whose `generate_random_key` is
`StaticPrivateKey::generate`. -/
abbrev P256C : high.curve.Curve high.curve.P256 mid.p256.StaticPrivateKey mid.p256.VerifyingKey
    mid.p256.Scalar :=
  { high.curve.P256.Insts.RindHighCurveCurveStaticPrivateKeyVerifyingKeyScalar with
    generate_random_key := fun inst rng => mid.p256.StaticPrivateKey.generate inst rng }

/-- SHA-256's `SignatureHash` impl. -/
abbrev Sha256Sig := high.hash.Sha256.Insts.RindHighHashSignatureHashSha256ContextSha256State

/-- An ECDSA signing key on P-256. -/
abbrev P256SigningKey :=
  high.ecdsa.SigningKey high.curve.P256 mid.p256.StaticPrivateKey mid.p256.VerifyingKey mid.p256.Scalar

/-- An ECDSA verifying key on P-256. -/
abbrev P256VerifyingKey :=
  high.ecdsa.VerifyingKey high.curve.P256 mid.p256.StaticPrivateKey mid.p256.VerifyingKey mid.p256.Scalar

/-- `parse_ecdsa::<P256, Sha256, Fixed>`, whose `Verifier`'s `verify` is
`VerifyingKey::verify::<Sha256>`. -/
def high.signature.parse_ecdsa_p256_sha256_fixed (bytes : Slice Std.U8) :
    Result (core.result.Result high.signature.Parsed error.Error) := do
  let r ← high.ecdsa.VerifyingKey.from_x962_uncompressed P256C bytes
  match r with
  | .Ok key => ok (.Ok (.Other fun message signature =>
      high.ecdsa.VerifyingKey.verify P256C Sha256Sig key message signature))
  | .Err e => ok (.Err e)

/-- The `verify::ECDSA_P256_SHA256_FIXED` static, whose parser is
`parse_ecdsa::<P256, Sha256, Fixed>`, with what `PublicKey::new` does for it. -/
def high.signature.verify.ECDSA_P256_SHA256_FIXED : high.signature.Verification :=
  .Other fun bytes => do
    let r ← high.signature.parse_ecdsa_p256_sha256_fixed bytes
    match r with
    | .Ok key =>
      let b ← high.signature.Buffer.copy_from 2592#usize bytes
      match b with
      | .Ok encoding => ok (.Ok { key, encoding })
      | .Err e => ok (.Err e)
    | .Err e => ok (.Err e)

/-- `EcdsaKey`, whose P-256 pair `load::<P256, Sha256, Fixed>` built is
`P256Sha256Fixed`. -/
inductive high.signature.EcdsaKey where
  | P256Sha256Fixed (signing : P256SigningKey)
  | Other (sign : Slice Std.U8 → Result (core.result.Result high.signature.Signature error.Error))
      (public_key : Result high.signature.PublicKey)

/-- `EcdsaKeyPair`. -/
structure high.signature.EcdsaKeyPair where
  key : high.signature.EcdsaKey

/-- `EcdsaSource`. -/
inductive high.signature.EcdsaSource where
  | Generate
  | Pkcs8 (der : Slice Std.U8)
  | Sec1 (der : Slice Std.U8)
  | Scalar (scalar public_key : Slice Std.U8)

/-- `EcdsaSigningAlgorithm`: its `load`, applied to its `Ecdsa`. -/
structure high.signature.EcdsaSigningAlgorithm where
  load : high.signature.EcdsaSource →
    Result (core.result.Result high.signature.EcdsaKeyPair error.Error)

/-- `ecdsa::SigningKey::<P256>::from_pkcs8_der`, DER the ✓ leaves out. -/
opaque high.ecdsa.SigningKey.from_pkcs8_der_p256 :
    Slice Std.U8 → Result (core.result.Result P256SigningKey error.Error)

/-- `ecdsa::SigningKey::<P256>::from_sec1_der`, DER the ✓ leaves out. -/
opaque high.ecdsa.SigningKey.from_sec1_der_p256 :
    Slice Std.U8 → Result (core.result.Result P256SigningKey error.Error)

/-- `EcdsaKeyPair::load::<P256, Sha256, Fixed>`. -/
def high.signature.EcdsaKeyPair.load_p256_sha256_fixed (source : high.signature.EcdsaSource) :
    Result (core.result.Result high.signature.EcdsaKeyPair error.Error) := do
  let signing ← match source with
    | .Generate => high.ecdsa.SigningKey.generate P256C
    | .Pkcs8 der => high.ecdsa.SigningKey.from_pkcs8_der_p256 der
    | .Sec1 der => high.ecdsa.SigningKey.from_sec1_der_p256 der
    | .Scalar scalar public_key =>
      high.ecdsa.SigningKey.from_private_key_and_public_key P256C scalar public_key
  match signing with
  | .Err e => ok (.Err e)
  | .Ok signing => ok (.Ok { key := .P256Sha256Fixed signing })

/-- The `sign::ECDSA_P256_SHA256_FIXED` static, whose `load` is
`EcdsaKeyPair::load::<P256, Sha256, Fixed>`. -/
def high.signature.sign.ECDSA_P256_SHA256_FIXED : high.signature.EcdsaSigningAlgorithm :=
  ⟨high.signature.EcdsaKeyPair.load_p256_sha256_fixed⟩

/-- `EcdsaKeyPair::generate`. -/
def high.signature.EcdsaKeyPair.generate (algorithm : high.signature.EcdsaSigningAlgorithm) :
    Result (core.result.Result high.signature.EcdsaKeyPair error.Error) :=
  algorithm.load .Generate

/-- `EcdsaKeyPair::from_scalar_and_public_key`. -/
def high.signature.EcdsaKeyPair.from_scalar_and_public_key
    (algorithm : high.signature.EcdsaSigningAlgorithm) (scalar public_key : Slice Std.U8) :
    Result (core.result.Result high.signature.EcdsaKeyPair error.Error) :=
  algorithm.load (.Scalar scalar public_key)

/-- `EcdsaKeyPair::public_key`, as the translation names a method, whose
P-256 `Verifier`'s `verify` is `VerifyingKey::verify::<Sha256>`. -/
def high.signature.EcdsaKeyPair.impl.public_key (self : high.signature.EcdsaKeyPair) :
    Result high.signature.PublicKey :=
  match self.key with
  | .P256Sha256Fixed signing => do
    let point ← high.ecdsa.SigningKey.public_key_uncompressed P256C signing
    let s ← high.ecdsa.EncodedPoint.Insts.CoreConvertAsRefSliceU8.as_ref point
    let r ← high.ecdsa.VerifyingKey.from_x962_uncompressed P256C s
    let key ← core.result.Result.expect error.Error.Insts.CoreFmtDebug r
      (toStr "a key pair's own point")
    let s1 ← high.ecdsa.EncodedPoint.Insts.CoreConvertAsRefSliceU8.as_ref point
    let b ← high.signature.Buffer.copy_from 2592#usize s1
    let encoding ← core.result.Result.expect error.Error.Insts.CoreFmtDebug b
      (toStr "sized for the largest key")
    ok { key := .Other fun message signature =>
        high.ecdsa.VerifyingKey.verify P256C Sha256Sig key message signature, encoding }
  | .Other _ public_key => public_key

/-- `EcdsaKeyPair::sign`, whose P-256 ops' `sign` is
`SigningKey::sign::<Sha256>`. -/
def high.signature.EcdsaKeyPair.sign (self : high.signature.EcdsaKeyPair) (message : Slice Std.U8) :
    Result (core.result.Result high.signature.Signature error.Error) :=
  match self.key with
  | .P256Sha256Fixed signing =>
    high.signature.Buffer.write 1024#usize fun output =>
      high.ecdsa.SigningKey.sign P256C Sha256Sig signing message output
  | .Other sign _ => sign message

end rind.x86_64
