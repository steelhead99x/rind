import Rind.X86_64.SignatureBuffer
open Aeneas Aeneas.Std Result

/-!
# The signature API's P-256 ECDSA dispatch, modelled by hand

`ecdsa::KeyPair` reaches each algorithm's code, and `ecdsa::PublicKey` each
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

macro_rules! with_hash {
    ($hash:expr, |$H:ident| $body:expr) => {
        match $hash {
            HashId::Sha256 => {
                type $H = crate::high::hash::Sha256;
                $body
            }
            HashId::Sha384 => {
                type $H = crate::high::hash::Sha384;
                $body
            }
            HashId::Sha512 => {
                type $H = crate::high::hash::Sha512;
                $body
            }
        }
    };
}

type Verify<K> = fn(&K, &[u8], &[u8]) -> Result<(), Error>;

type Sign<K> = for<'a> fn(&K, &'a mut [u8], &[u8]) -> Result<&'a [u8], Error>;

type Write<K> = for<'a> fn(&K, &'a mut [u8]) -> Result<&'a [u8], Error>;

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
    fn key(key: EcdsaVerifier<Self>) -> Key;

    fn pair(pair: EcdsaPair<Self>) -> EcdsaKey;
}

macro_rules! ecdsa_curve {
    ($curve:ident) => {
        impl EcdsaCurve for $curve {
            fn key(key: EcdsaVerifier<Self>) -> Key {
                Key::$curve(key)
            }

            fn pair(pair: EcdsaPair<Self>) -> EcdsaKey {
                EcdsaKey::$curve(pair)
            }
        }
    };
}

ecdsa_curve!(P256);

enum Key {
    P256(EcdsaVerifier<P256>),
    P384(EcdsaVerifier<P384>),
    P521(EcdsaVerifier<P521>),
}

impl Clone for Key {
    fn clone(&self) -> Self {
        match self {
            Self::P256(key) => Self::P256(key.clone()),
            Self::P384(key) => Self::P384(key.clone()),
            Self::P521(key) => Self::P521(key.clone()),
        }
    }
}

struct EcdsaVerifier<C: EcdsaCurve> {
    key: ecdsa::VerifyingKey<C>,
    ops: low::ZeroableRef<VerifyOps<C>>,
}

impl<C: EcdsaCurve> Clone for EcdsaVerifier<C> {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            ops: self.ops,
        }
    }
}

struct VerifyOps<C: EcdsaCurve> {
    verify: Verify<ecdsa::VerifyingKey<C>>,
    verify_digest: Verify<ecdsa::VerifyingKey<C>>,
}

impl<C: EcdsaCurve> EcdsaVerifier<C> {
    /// Parses `point` for the encoding and hash `E` and `H`.
    fn parse<H: SignatureHash, E: Encoding>(point: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            key: ecdsa::VerifyingKey::from_x962_uncompressed(point)?,
            ops: low::ZeroableRef::new(
                const {
                    &VerifyOps {
                        verify: E::verify::<C, H>,
                        verify_digest: E::verify_digest::<C>,
                    }
                },
            ),
        })
    }

    fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        (self.ops.get().verify)(&self.key, signature, message)
    }

    fn verify_digest(&self, digest: &[u8], signature: &[u8]) -> Result<(), Error> {
        (self.ops.get().verify_digest)(&self.key, signature, digest)
    }
}

macro_rules! on_key {
    ($key_enum:expr, |$key:ident| $body:expr) => {
        match $key_enum {
            Key::P256($key) => $body,
            Key::P384($key) => $body,
            Key::P521($key) => $body,
        }
    };
}

fn parse_ecdsa<C: EcdsaCurve, H: SignatureHash, E: Encoding>(point: &[u8]) -> Result<Key, Error> {
    EcdsaVerifier::<C>::parse::<H, E>(point).map(C::key)
}

pub struct VerificationAlgorithm {
    ecdsa: Ecdsa,
    // The only path to the algorithm's code: a binary links only the
    // algorithms it names.
    parse: fn(&[u8]) -> Result<Key, Error>,
    decompress: sec1::Decompress,
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
    VerificationAlgorithm {
        ecdsa,
        parse,
        decompress,
    }
}

pub struct PublicKey {
    key: Key,
    algorithm: Ecdsa,
    point: EncodedPoint,
}

impl PublicKey {
    /// Parses an X9.62 uncompressed point for `algorithm`, refusing a
    /// malformed key before any signature arrives.
    ///
    /// A compressed point is refused, which
    /// [`agreement::PublicKey::new`](crate::agreement::PublicKey::new)
    /// decompresses, and [`Self::from_spki`] takes inside a
    /// `SubjectPublicKeyInfo`.
    pub fn new(algorithm: &VerificationAlgorithm, point: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            key: (algorithm.parse)(point)?,
            algorithm: algorithm.ecdsa,
            point: EncodedPoint::copy_from(point)?,
        })
    }

    /// Parses a public key for `algorithm` from its `SubjectPublicKeyInfo`
    /// DER, refusing one that names another algorithm or curve.
    ///
    /// It names `id-ecPublicKey` and the algorithm's curve, and its point
    /// may be compressed (RFC 5480), which this decompresses.
    pub fn from_spki(algorithm: &VerificationAlgorithm, der: &[u8]) -> Result<Self, Error> {
        let curve = Some(asn1::Any::ObjectId(curve_oid(algorithm.ecdsa.curve)));
        let point = spki::decode(der, &[&asn1::oid::id_ecPublicKey], curve)?;
        let mut decompressed = [0; MAX_UNCOMPRESSED_PUBLIC_KEY_LEN];
        Self::new(
            algorithm,
            sec1::uncompressed(point, algorithm.decompress, &mut decompressed)?,
        )
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`: `id-ecPublicKey`
    /// on its curve, with its uncompressed point.
    pub fn to_spki(&self) -> Spki {
        let curve = Some(asn1::Any::ObjectId(curve_oid(self.algorithm.curve)));
        Spki(Buffer::encode(|output| {
            spki::encode(self.as_ref(), &asn1::oid::id_ecPublicKey, curve, output)
        }))
    }

    /// Verifies `signature` over `message`, refusing a malformed signature.
    ///
    /// ECDSA signatures are malleable: `(r, s)` and `(r, n - s)` both verify,
    /// so don't identify a message by its signature's bytes.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        on_key!(&self.key, |key| key.verify(message, signature))
    }

    /// Verifies `signature` over the message `digest` hashes.
    ///
    /// The digest's hash, SHA-256, SHA-384, or SHA-512, replaces the
    /// algorithm's, which still fixes the curve and the signature's encoding.
    /// Another hash is refused as [`Error::Unsupported`].
    ///
    /// So unlike [`Self::verify`], this does not pin the hash: hash with the
    /// one your protocol names, never one the signed data or its sender
    /// picks. A signature over one SHA-2 hash verifies over another only
    /// for a message whose digest collides with it, which no one can find.
    pub fn verify_digest(&self, digest: &Digest, signature: &[u8]) -> Result<(), Error> {
        let digest = signed_digest(digest)?;
        on_key!(&self.key, |key| key.verify_digest(digest, signature))
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        self.point.as_ref()
    }
}

pub struct Signature(Buffer<SIGNATURE_MAX_LEN>);

const SIGNATURE_MAX_LEN: usize = 3 + 2 * (2 + MAX_SCALAR_LEN + 1);

const fn ecdsa_signing(verification: &VerificationAlgorithm) -> SigningAlgorithm {
    let ecdsa = verification.ecdsa;
    SigningAlgorithm {
        ecdsa,
        load: with_ecdsa!(ecdsa, |C, H, E| KeyPair::load::<C, H, E> as _),
    }
}

pub struct SigningAlgorithm {
    ecdsa: Ecdsa,
    // The only path to the algorithm's code, as `VerificationAlgorithm`'s.
    load: fn(Ecdsa, EcdsaSource<'_>) -> Result<KeyPair, Error>,
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

pub struct KeyPair {
    key: EcdsaKey,
    public: PublicKey,
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

struct EcdsaOps<C: EcdsaCurve> {
    sign: Sign<ecdsa::SigningKey<C>>,
    sign_digest: Sign<ecdsa::SigningKey<C>>,
    to_pkcs8: Write<ecdsa::SigningKey<C>>,
    to_scalar: Write<ecdsa::SigningKey<C>>,
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

impl KeyPair {
    /// Generates a key pair for `algorithm` from the system random source.
    pub fn generate(algorithm: &'static SigningAlgorithm) -> Result<Self, Error> {
        (algorithm.load)(algorithm.ecdsa, EcdsaSource::Generate)
    }

    /// Loads a PKCS#8 v1 `ECPrivateKey` on `algorithm`'s curve.
    pub fn from_pkcs8(algorithm: &'static SigningAlgorithm, der: &[u8]) -> Result<Self, Error> {
        (algorithm.load)(algorithm.ecdsa, EcdsaSource::Pkcs8(der))
    }

    /// Loads a SEC1 (RFC 5915) `ECPrivateKey` on `algorithm`'s curve.
    ///
    /// This refuses PKCS#8, which [`Self::from_pkcs8`] takes: a caller always
    /// knows which of the two it holds.
    pub fn from_sec1(algorithm: &'static SigningAlgorithm, der: &[u8]) -> Result<Self, Error> {
        (algorithm.load)(algorithm.ecdsa, EcdsaSource::Sec1(der))
    }

    /// Loads a fixed-length big-endian private scalar, refused unless
    /// `public_key`, an X9.62 uncompressed or compressed point, is its public
    /// key.
    ///
    /// This suits a JWK's `d` and `x`/`y`; prefer [`Self::from_pkcs8`] for
    /// stored keys.
    pub fn from_scalar_and_public_key(
        algorithm: &'static SigningAlgorithm,
        scalar: &[u8],
        public_key: &[u8],
    ) -> Result<Self, Error> {
        let source = EcdsaSource::Scalar { scalar, public_key };
        (algorithm.load)(algorithm.ecdsa, source)
    }

    /// Loads a key pair for `ecdsa`, whose curve, hash, and encoding are `C`,
    /// `H`, and `E`, and derives its public key.
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
        // A loader that checked a given public key kept it, so only a key
        // without one costs a scalar multiplication here.
        let point = signing.public_key_uncompressed();
        let public = PublicKey {
            key: C::key(EcdsaVerifier::parse::<H, E>(point.as_ref()).expect("its own point")),
            algorithm: ecdsa,
            point,
        };
        let ops = const {
            &EcdsaOps {
                sign: E::sign::<C, H>,
                sign_digest: E::sign_digest::<C, H>,
                to_pkcs8: ecdsa::SigningKey::to_pkcs8_der,
                to_scalar: ecdsa::SigningKey::to_scalar,
            }
        };
        Ok(Self {
            key: C::pair(EcdsaPair {
                signing,
                ops: low::ZeroableRef::new(ops),
            }),
            public,
        })
    }

    /// Returns the public key, which verifies what this key pair signs.
    pub fn public_key(&self) -> &PublicKey {
        &self.public
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
    /// [`PublicKey::verify`] verifies the signature over the message only if
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
    pub fn to_scalar(&self) -> Scalar {
        Scalar(Buffer::encode(|output| {
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
        // A copy inside the call, so unwiped, unlike `to_scalar`'s.
        let scalar = Buffer::<MAX_SCALAR_LEN>::encode(|output| {
            on_ecdsa!(self, |pair| (pair.ops.get().to_scalar)(
                &pair.signing,
                output
            ))
        });
        let curve = curve_oid(self.public.algorithm.curve);
        Sec1(Buffer::encode(|output| {
            sec1::encode(scalar.as_ref(), self.public.as_ref(), Some(curve), output)
        }))
    }
}

    pub static P256_SHA256_FIXED: SigningAlgorithm = ecdsa_signing(&verify::P256_SHA256_FIXED);

    pub static P256_SHA256_FIXED: VerificationAlgorithm =
        ecdsa_verification(CurveId::P256, HashId::Sha256, EcdsaEncoding::Fixed);

```

The model departs from the Rust in these ways, and adds no axiom:

- P-256's `generate_random_key` is `StaticPrivateKey::generate`, which is
  `PrivateKey::generate` over the source it is given, whose `dyn` is the
  source's `RandomSource` impl. `low::ct::secret_slice`, a ctgrind marker
  that computes nothing, is left out. `P256C` is the translated `Curve` impl
  for `P256` with `generate_random_key` replaced by this model, so the
  translated ECDSA code over it runs the model.
- A `VerificationAlgorithm` is its `parse`; `with_ecdsa!` gives
  `verify::P256_SHA256_FIXED` `parse_ecdsa::<P256, Sha256, Fixed>`. Its
  `ecdsa`, which `PublicKey::new` copies into the key's `algorithm`, and its
  `decompress`, read only by `PublicKey::from_spki`, are left out.
- A `Key::P256` whose `EcdsaVerifier`'s ops `parse::<Sha256, Fixed>` built is
  `Key.P256Sha256Fixed`, holding its `VerifyingKey`, and `PublicKey::verify`
  calls those ops' `verify`, `Fixed::verify::<P256, Sha256>`, which is
  `VerifyingKey::verify::<Sha256>`, directly: `parse` builds every
  `VerifyOps`, a clone keeps its ops, and they are read only through
  `ops.get()`. Every other key is `Other`, holding what `verify` does for it,
  and `ZeroableRef`, which holds the ops, is left out.
- A `PublicKey`'s `algorithm`, read only by `Debug`, `to_spki`, and
  `KeyPair::to_sec1`, is left out.
- A `SigningAlgorithm` is the `load` it holds, applied to its `Ecdsa`;
  `with_ecdsa!` gives `sign::P256_SHA256_FIXED`
  `KeyPair::load::<P256, Sha256, Fixed>`.
- An `EcdsaKey::P256` whose ops that `load` built is
  `EcdsaKey.P256Sha256Fixed`, holding its signing key, and `KeyPair::sign`
  calls those ops' `sign`, `Fixed::sign::<P256, Sha256>`, which is
  `SigningKey::sign::<Sha256>`, directly: `load` builds every `EcdsaOps` and
  `EcdsaPair`. Every other key is `Other`, holding what `sign` does for it.
- `admin/prove` checks that the quotes hold every mention of `Key::` and
  `EcdsaKey::`, every `VerifyOps`, `EcdsaOps`, and `EcdsaPair` built, every
  `Key` a clone builds, and every read of an `ops`.
- `verify_digest`, `sign_digest`, `from_spki`, `to_spki`, and the `to_*`
  encoders, which no theorem here is about, are quoted only because they
  share their `impl`, and are not modelled, nor are the ops they read.
  Neither are the clones, which compute no result here.
- `.map(Signature)` is the identity: the translation's `Signature` is its
  `Buffer`. `Buffer::write` is `Rind.X86_64.SignatureBuffer`'s.
- PKCS#8 and SEC1 loading, DER the ✓ leaves out, is opaque.
- `?` is a `match`, since each error it passes on is already an `Error`.

Drops are not modelled, as everywhere in the translation.
`SIGNATURE_MAX_LEN` is 3 + 2 · (2 + 66 + 1) = 141, from P-521's 66-byte
`MAX_SCALAR_LEN`.
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

/-- `Key`, whose P-256 verifier `parse::<Sha256, Fixed>` built is
`P256Sha256Fixed`. -/
inductive high.signature.ecdsa.Key where
  | P256Sha256Fixed (key : P256VerifyingKey)
  | Other (verify : Slice Std.U8 → Slice Std.U8 → Result (core.result.Result Unit error.Error))

/-- `PublicKey`. -/
structure high.signature.ecdsa.PublicKey where
  key : high.signature.ecdsa.Key
  point : high.ecdsa.EncodedPoint

/-- `VerificationAlgorithm`: its `parse`. -/
structure high.signature.ecdsa.VerificationAlgorithm where
  parse : Slice Std.U8 → Result (core.result.Result high.signature.ecdsa.Key error.Error)

/-- `EcdsaVerifier::<P256>::parse::<Sha256, Fixed>`, whose ops' `verify` is
`VerifyingKey::verify::<Sha256>`, as the `VerifyingKey` it holds. -/
def high.signature.ecdsa.EcdsaVerifier.parse_p256_sha256_fixed (point : Slice Std.U8) :
    Result (core.result.Result P256VerifyingKey error.Error) := do
  let r ← high.ecdsa.VerifyingKey.from_x962_uncompressed P256C point
  match r with
  | .Ok key => ok (.Ok key)
  | .Err e => ok (.Err e)

/-- `parse_ecdsa::<P256, Sha256, Fixed>`. -/
def high.signature.ecdsa.parse_ecdsa_p256_sha256_fixed (point : Slice Std.U8) :
    Result (core.result.Result high.signature.ecdsa.Key error.Error) := do
  let r ← high.signature.ecdsa.EcdsaVerifier.parse_p256_sha256_fixed point
  match r with
  | .Ok key => ok (.Ok (.P256Sha256Fixed key))
  | .Err e => ok (.Err e)

/-- The `verify::P256_SHA256_FIXED` static, whose parser is
`parse_ecdsa::<P256, Sha256, Fixed>`. -/
def high.signature.ecdsa.verify.P256_SHA256_FIXED : high.signature.ecdsa.VerificationAlgorithm :=
  ⟨high.signature.ecdsa.parse_ecdsa_p256_sha256_fixed⟩

/-- `PublicKey::new`. -/
def high.signature.ecdsa.PublicKey.new (algorithm : high.signature.ecdsa.VerificationAlgorithm)
    (point : Slice Std.U8) :
    Result (core.result.Result high.signature.ecdsa.PublicKey error.Error) := do
  let r ← algorithm.parse point
  match r with
  | .Err e => ok (.Err e)
  | .Ok key =>
    let p ← high.ecdsa.EncodedPoint.copy_from point
    match p with
    | .Ok point => ok (.Ok { key, point })
    | .Err e => ok (.Err e)

/-- `PublicKey::verify`, whose P-256 verifier's `verify` is
`VerifyingKey::verify::<Sha256>`. -/
def high.signature.ecdsa.PublicKey.verify (self : high.signature.ecdsa.PublicKey)
    (message signature : Slice Std.U8) : Result (core.result.Result Unit error.Error) :=
  match self.key with
  | .P256Sha256Fixed key => high.ecdsa.VerifyingKey.verify P256C Sha256Sig key message signature
  | .Other verify => verify message signature

/-- `PublicKey`'s `AsRef<[u8]>`. -/
def high.signature.ecdsa.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref
    (self : high.signature.ecdsa.PublicKey) : Result (Slice Std.U8) :=
  high.ecdsa.EncodedPoint.Insts.CoreConvertAsRefSliceU8.as_ref self.point

/-- `EcdsaKey`, whose P-256 pair `load::<P256, Sha256, Fixed>` built is
`P256Sha256Fixed`. -/
inductive high.signature.ecdsa.EcdsaKey where
  | P256Sha256Fixed (signing : P256SigningKey)
  | Other (sign : Slice Std.U8 →
      Result (core.result.Result high.signature.ecdsa.Signature error.Error))

/-- `KeyPair`. -/
structure high.signature.ecdsa.KeyPair where
  key : high.signature.ecdsa.EcdsaKey
  «public» : high.signature.ecdsa.PublicKey

/-- `EcdsaSource`. -/
inductive high.signature.ecdsa.EcdsaSource where
  | Generate
  | Pkcs8 (der : Slice Std.U8)
  | Sec1 (der : Slice Std.U8)
  | Scalar (scalar public_key : Slice Std.U8)

/-- `SigningAlgorithm`: its `load`, applied to its `Ecdsa`. -/
structure high.signature.ecdsa.SigningAlgorithm where
  load : high.signature.ecdsa.EcdsaSource →
    Result (core.result.Result high.signature.ecdsa.KeyPair error.Error)

/-- `ecdsa::SigningKey::<P256>::from_pkcs8_der`, DER the ✓ leaves out. -/
opaque high.ecdsa.SigningKey.from_pkcs8_der_p256 :
    Slice Std.U8 → Result (core.result.Result P256SigningKey error.Error)

/-- `ecdsa::SigningKey::<P256>::from_sec1_der`, DER the ✓ leaves out. -/
opaque high.ecdsa.SigningKey.from_sec1_der_p256 :
    Slice Std.U8 → Result (core.result.Result P256SigningKey error.Error)

/-- `KeyPair::load::<P256, Sha256, Fixed>`. -/
def high.signature.ecdsa.KeyPair.load_p256_sha256_fixed (source : high.signature.ecdsa.EcdsaSource) :
    Result (core.result.Result high.signature.ecdsa.KeyPair error.Error) := do
  let signing ← match source with
    | .Generate => high.ecdsa.SigningKey.generate P256C
    | .Pkcs8 der => high.ecdsa.SigningKey.from_pkcs8_der_p256 der
    | .Sec1 der => high.ecdsa.SigningKey.from_sec1_der_p256 der
    | .Scalar scalar public_key =>
      high.ecdsa.SigningKey.from_private_key_and_public_key P256C scalar public_key
  match signing with
  | .Err e => ok (.Err e)
  | .Ok signing =>
    let point ← high.ecdsa.SigningKey.public_key_uncompressed P256C signing
    let s ← high.ecdsa.EncodedPoint.Insts.CoreConvertAsRefSliceU8.as_ref point
    let r ← high.signature.ecdsa.EcdsaVerifier.parse_p256_sha256_fixed s
    let key ← core.result.Result.expect error.Error.Insts.CoreFmtDebug r (toStr "its own point")
    ok (.Ok { key := .P256Sha256Fixed signing, «public» := { key := .P256Sha256Fixed key, point } })

/-- The `sign::P256_SHA256_FIXED` static, whose `load` is
`KeyPair::load::<P256, Sha256, Fixed>`. -/
def high.signature.ecdsa.sign.P256_SHA256_FIXED : high.signature.ecdsa.SigningAlgorithm :=
  ⟨high.signature.ecdsa.KeyPair.load_p256_sha256_fixed⟩

/-- `KeyPair::generate`. -/
def high.signature.ecdsa.KeyPair.generate (algorithm : high.signature.ecdsa.SigningAlgorithm) :
    Result (core.result.Result high.signature.ecdsa.KeyPair error.Error) :=
  algorithm.load .Generate

/-- `KeyPair::from_scalar_and_public_key`. -/
def high.signature.ecdsa.KeyPair.from_scalar_and_public_key
    (algorithm : high.signature.ecdsa.SigningAlgorithm) (scalar public_key : Slice Std.U8) :
    Result (core.result.Result high.signature.ecdsa.KeyPair error.Error) :=
  algorithm.load (.Scalar scalar public_key)

/-- `KeyPair::public_key`. -/
def high.signature.ecdsa.KeyPair.public_key (self : high.signature.ecdsa.KeyPair) :
    Result high.signature.ecdsa.PublicKey :=
  ok self.«public»

/-- `KeyPair::sign`, whose P-256 ops' `sign` is `SigningKey::sign::<Sha256>`. -/
def high.signature.ecdsa.KeyPair.sign (self : high.signature.ecdsa.KeyPair) (message : Slice Std.U8) :
    Result (core.result.Result high.signature.ecdsa.Signature error.Error) :=
  match self.key with
  | .P256Sha256Fixed signing =>
    high.signature.Buffer.write 141#usize fun output =>
      high.ecdsa.SigningKey.sign P256C Sha256Sig signing message output
  | .Other sign => sign message

end rind.x86_64
