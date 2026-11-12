import Rind.X86_64.Funs
open Aeneas Aeneas.Std Result

/-!
# The signature API's Ed25519 dispatch, modelled by hand

`PublicKey` reaches each algorithm's key parser, and each parsed key its
verification, through function pointers, which Aeneas cannot translate, so
the translation stops below them and this file models the Rust above them.
`admin/prove` fails unless these quotes are still that Rust, so a change to it
is a change to this model:

```rust
pub struct VerificationAlgorithm(Verification);

enum Verification {
    Ecdsa(
        Ecdsa,
        fn(Ecdsa, &[u8]) -> Result<Parsed, Error>,
        sec1::Decompress,
    ),
    Rsa(Rsa),
    Ed25519(fn(&[u8]) -> Result<Parsed, Error>),
    MlDsa(MlDsaAlgorithm),
    SlhDsa(SlhDsaAlgorithm),
}

type Verify<K> = fn(&K, &[u8], &[u8]) -> Result<(), Error>;

struct Verifier<K> {
    key: K,
    verify: Verify<K>,
}

impl<K> Verifier<K> {
    fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        (self.verify)(&self.key, signature, message)
    }
}

pub struct PublicKey {
    key: Parsed,
    encoding: Buffer<MAX_PUBLIC_KEY_LEN>,
}

enum Parsed {
    EcdsaP256(EcdsaVerifier<P256>, Ecdsa),
    EcdsaP384(EcdsaVerifier<P384>, Ecdsa),
    EcdsaP521(EcdsaVerifier<P521>, Ecdsa),
    Rsa(RsaVerifier, RsaVerification),
    Ed25519(Verifier<Ed25519VerifyingKey>),
    MlDsa(MlDsaVerifier),
    SlhDsa(SlhDsaAlgorithm),
}

impl PublicKey {
    /// Parses a public key for `algorithm`, any `verify` constant,
    /// refusing a malformed key before any signature arrives.
    ///
    /// ECDSA keys are X9.62 uncompressed points, RSA keys are PKCS#1
    /// `RSAPublicKey` or `SubjectPublicKeyInfo` DER, Ed25519 keys are their
    /// 32 bytes, and ML-DSA keys are FIPS 204's encoding. A compressed ECDSA
    /// point is refused, which
    /// [`agreement::PublicKey::new`](crate::agreement::PublicKey::new)
    /// decompresses. So is an Ed25519 point of small order, which verifies
    /// signatures nobody made.
    pub fn new(algorithm: &impl AsRef<VerificationAlgorithm>, bytes: &[u8]) -> Result<Self, Error> {
        let key = match algorithm.as_ref().0 {
            Verification::Ecdsa(ecdsa, parse, _) => parse(ecdsa, bytes)?,
            Verification::Rsa(rsa) => return (rsa.parse)(rsa, bytes),
            Verification::Ed25519(parse) => parse(bytes)?,
            Verification::MlDsa(algorithm) => algorithm.parse(bytes)?,
            Verification::SlhDsa(algorithm) => algorithm.parse(bytes)?,
        };
        Ok(Self {
            key,
            encoding: Buffer::copy_from(bytes)?,
        })
    }

    /// Loads an RSA key for `algorithm` from its big-endian modulus and
    /// exponent, as a JWK carries them.
    pub fn from_components(
        algorithm: &RsaVerificationAlgorithm,
        components: &PublicKeyComponents<impl AsRef<[u8]>>,
    ) -> Result<Self, Error> {
        let key = rsa::VerifyingKey::from_components(components.n.as_ref(), components.e.as_ref())?;
        Self::rsa(algorithm.rsa, key)
    }

    /// Parses a public key for `algorithm` from its `SubjectPublicKeyInfo`
    /// DER, refusing one that names another algorithm or curve.
    ///
    /// An ECDSA key names `id-ecPublicKey` and the algorithm's curve, and
    /// its point may be compressed (RFC 5480), which this decompresses. An
    /// RSA key names `rsaEncryption`, `id-RSAES-OAEP`, or `id-ea-rsa`, an
    /// Ed25519 key `id-Ed25519`, and an ML-DSA key its parameter set's OID
    /// (RFC 9881).
    pub fn from_spki(
        algorithm: &impl AsRef<VerificationAlgorithm>,
        der: &[u8],
    ) -> Result<Self, Error> {
        match algorithm.as_ref().0 {
            Verification::Ecdsa(ecdsa, _, decompress) => {
                let curve = Some(asn1::Any::ObjectId(curve_oid(ecdsa.curve)));
                let point = spki::decode(der, &[&asn1::oid::id_ecPublicKey], curve)?;
                let mut decompressed = [0; MAX_UNCOMPRESSED_PUBLIC_KEY_LEN];
                Self::new(
                    algorithm,
                    sec1::uncompressed(point, decompress, &mut decompressed)?,
                )
            }
            // RSA's parser takes PKCS#1 too, which this refuses.
            Verification::Rsa(rsa) => {
                pkix::SubjectPublicKeyInfo::from_bytes(der).map_err(KeyFormatError::Asn1)?;
                (rsa.parse)(rsa, der)
            }
            Verification::Ed25519(_) => Self::new(
                algorithm,
                spki::decode(der, &[&asn1::oid::id_ed25519], None)?,
            ),
            Verification::MlDsa(ml_dsa) => {
                Self::new(algorithm, spki::decode(der, &[ml_dsa.oid], None)?)
            }
            Verification::SlhDsa(slh_dsa) => {
                Self::new(algorithm, spki::decode(der, &[slh_dsa.oid], None)?)
            }
        }
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`: ECDSA's
    /// `id-ecPublicKey` on its curve, with its uncompressed point, RSA's
    /// `rsaEncryption`, Ed25519's `id-Ed25519`, or ML-DSA's parameter set.
    pub fn to_spki(&self) -> Spki {
        let ec = |curve| (&asn1::oid::id_ecPublicKey, Some(asn1::Any::ObjectId(curve)));
        let (algorithm, parameters) = match &self.key {
            Parsed::EcdsaP256(..) => ec(P256::oid()),
            Parsed::EcdsaP384(..) => ec(P384::oid()),
            Parsed::EcdsaP521(..) => ec(P521::oid()),
            Parsed::Rsa(..) => (&asn1::oid::rsaEncryption, Some(asn1::Any::Null(asn1::Null))),
            Parsed::Ed25519(_) => (&asn1::oid::id_ed25519, None),
            Parsed::MlDsa(key) => (key.algorithm.oid, None),
            Parsed::SlhDsa(algorithm) => (algorithm.oid, None),
        };
        Spki(Buffer::encode(|output| {
            spki::encode(self.as_ref(), algorithm, parameters, output)
        }))
    }

    /// Parses an RSA key's PKCS#1 or SPKI DER for `rsa`.
    fn parse_rsa(rsa: Rsa, bytes: &[u8]) -> Result<Self, Error> {
        Self::rsa(rsa, rsa::VerifyingKey::from_der(bytes)?)
    }

    /// Binds an RSA key to `rsa`, refusing it below the algorithm's floor.
    ///
    /// The encoding is the key's PKCS#1 DER, whether it came as PKCS#1,
    /// SPKI, or components.
    fn rsa(rsa: Rsa, key: rsa::VerifyingKey) -> Result<Self, Error> {
        let key = rsa.check(key)?;
        Ok(Self {
            encoding: Buffer::write(|output| key.to_pkcs1_der(output))?,
            key: Parsed::Rsa(
                RsaVerifier {
                    key,
                    verify: rsa.verify,
                },
                rsa.verification,
            ),
        })
    }

    /// Verifies `signature` over `message`, refusing a malformed signature.
    ///
    /// ECDSA signatures are malleable: `(r, s)` and `(r, n - s)` both verify,
    /// unlike Ed25519, PKCS#1, and PSS signatures, so don't identify a message
    /// by its ECDSA signature's bytes.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        match &self.key {
            Parsed::EcdsaP256(key, _) => key.verify(message, signature),
            Parsed::EcdsaP384(key, _) => key.verify(message, signature),
            Parsed::EcdsaP521(key, _) => key.verify(message, signature),
            Parsed::Rsa(key, verification) => {
                (key.verify)(&key.key, verification.salt(), signature, message)
            }
            Parsed::Ed25519(key) => key.verify(message, signature),
            Parsed::MlDsa(key) => key.verify(self.as_ref(), message, signature),
            Parsed::SlhDsa(algorithm) => (algorithm.verify)(self.as_ref(), message, signature),
        }
    }

    /// Verifies an ECDSA `signature` over the message `digest` hashes.
    ///
    /// The digest's hash, SHA-256, SHA-384, or SHA-512, replaces the
    /// algorithm's, which still fixes the curve and the signature's encoding.
    /// Another hash, or a key other than ECDSA, is refused as
    /// [`Error::Unsupported`].
    ///
    /// So unlike [`Self::verify`], this does not pin the hash: hash with the
    /// one your protocol names, never one the signed data or its sender
    /// picks. A signature over one SHA-2 hash verifies over another only
    /// for a message whose digest collides with it, which no one can find.
    pub fn verify_digest(&self, digest: &Digest, signature: &[u8]) -> Result<(), Error> {
        let digest = signed_digest(digest)?;
        match &self.key {
            Parsed::EcdsaP256(key, _) => key.verify_digest(digest, signature),
            Parsed::EcdsaP384(key, _) => key.verify_digest(digest, signature),
            Parsed::EcdsaP521(key, _) => key.verify_digest(digest, signature),
            Parsed::Rsa(..) | Parsed::Ed25519(_) | Parsed::MlDsa(_) | Parsed::SlhDsa(_) => {
                Err(Error::Unsupported)
            }
        }
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        self.encoding.as_ref()
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut f = f.debug_struct("PublicKey");
        match &self.key {
            Parsed::EcdsaP256(_, algorithm)
            | Parsed::EcdsaP384(_, algorithm)
            | Parsed::EcdsaP521(_, algorithm) => f.field("algorithm", algorithm),
            Parsed::Rsa(_, verification) => f.field("algorithm", verification),
            Parsed::Ed25519(_) => f.field("algorithm", &format_args!("Ed25519")),
            Parsed::MlDsa(key) => f.field("algorithm", &format_args!("{}", key.algorithm.name)),
            Parsed::SlhDsa(algorithm) => f.field("algorithm", &format_args!("{}", algorithm.name)),
        };
        f.field("bytes", &self.as_ref()).finish()
    }
}

impl Ed25519KeyPair {
    /// Generates a key pair from the system random source.
    pub fn generate() -> Result<Self, Error> {
        Ok(Self::new(Ed25519SigningKey::generate()?))
    }

    /// Loads a PKCS#8 Ed25519 key, refused if it carries a public key
    /// (v2, RFC 5958) that does not match.
    ///
    /// This also takes PKCS#8 v1, which carries no public key: common tools
    /// write v1, and such a key is no less valid.
    pub fn from_pkcs8(der: &[u8]) -> Result<Self, Error> {
        Ok(Self::new(Ed25519SigningKey::from_pkcs8_der(der)?))
    }

    /// Loads a 32-byte seed, as a JWK's `d` holds it, deriving its public
    /// key.
    ///
    /// Prefer [`Self::from_seed_and_public_key`] when the public key is at
    /// hand, which checks it.
    pub fn from_seed(seed: &[u8]) -> Result<Self, Error> {
        Ok(Self::new(Ed25519SigningKey::from_bytes(seed)?))
    }

    /// Loads a 32-byte seed, refused unless `public_key` is its public key.
    ///
    /// This suits a JWK's `d` and `x`.
    pub fn from_seed_and_public_key(seed: &[u8], public_key: &[u8]) -> Result<Self, Error> {
        let pair = Self::new(Ed25519SigningKey::from_bytes(seed)?);
        match pair.public_key.as_slice() == public_key {
            true => Ok(pair),
            false => Err(KeyFormatError::MismatchedPublicKey.into()),
        }
    }

    fn new(key: Ed25519SigningKey) -> Self {
        let public_key = key.public_key().as_bytes();
        Self { key, public_key }
    }

    /// Returns the public key, which verifies what this key pair signs.
    pub fn public_key(&self) -> PublicKey {
        PublicKey {
            key: Parsed::Ed25519(Verifier {
                key: self.key.public_key(),
                verify: Ed25519VerifyingKey::verify,
            }),
            encoding: Buffer::from(self.public_key).widen(),
        }
    }

    /// Signs `message`.
    pub fn sign(&self, message: &[u8]) -> Signature {
        Signature(Buffer::from(self.key.sign(message)).widen())
    }

    /// Encodes the key pair as PKCS#8 v2 (RFC 5958).
    pub fn to_pkcs8(&self) -> Pkcs8 {
        Pkcs8(Buffer::encode(|output| self.key.to_pkcs8_der(true, output)))
    }

    /// Encodes the private key as PKCS#8 v1 (RFC 8410), its seed without its
    /// public key, as OpenSSL and BoringSSL write it.
    pub fn to_pkcs8v1(&self) -> Pkcs8 {
        Pkcs8(Buffer::encode(|output| {
            self.key.to_pkcs8_der(false, output)
        }))
    }

    /// Returns the private key's 32-byte seed, as a JWK's `d` holds it.
    ///
    /// This is what [`Self::from_seed_and_public_key`] loads; prefer
    /// [`Self::to_pkcs8`] for stored keys.
    pub fn to_seed(&self) -> Ed25519Seed {
        Ed25519Seed(*self.key.seed())
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`.
    pub fn to_spki(&self) -> Spki {
        Spki(Buffer::encode(|output| {
            self.key.public_key().to_spki_der(output)
        }))
    }
}

fn parse_ed25519(bytes: &[u8]) -> Result<Parsed, Error> {
    Ok(Parsed::Ed25519(Verifier {
        key: Ed25519VerifyingKey::from_bytes(bytes)?,
        verify: Ed25519VerifyingKey::verify,
    }))
}

    pub static ED25519: VerificationAlgorithm =
        VerificationAlgorithm(Verification::Ed25519(parse_ed25519));

```

The model departs from the Rust in five ways, and adds no axiom:

- `VerificationAlgorithm` is its `Verification`, and `PublicKey::new` takes
  the one its argument's `as_ref` returns, as both `AsRef` impls return the
  `VerificationAlgorithm` they hold.
- `Verification::Ed25519` holds nothing, and `PublicKey::new` calls
  `parse_ed25519` directly: the `ED25519` static builds the only one.
  `admin/prove` checks that the quotes hold every mention of
  `Verification::Ed25519(` in `signature.rs`.
- `Parsed::Ed25519` holds the key, and `PublicKey::verify` calls
  `Ed25519VerifyingKey::verify` directly: `Verifier`'s fields are private to
  `signature.rs`, where only `parse_ed25519` and `Ed25519KeyPair::public_key`
  build a `Parsed::Ed25519`, each with that function. `admin/prove` checks
  that the quotes hold every mention of `Parsed::Ed25519(` there.
- ECDSA's, RSA's, and ML-DSA's variants, which no theorem here is about,
  are one `Other` variant of each type, holding what `PublicKey::new` and
  `PublicKey::verify` do for them. `Verification::Ecdsa`'s decompressor,
  which only `PublicKey::from_spki` reads, is left out.
- `?` is a `match`, since each error it passes on is already an `Error`.

`PublicKey`'s `Debug` is quoted only so that check sees its mention, and not
modelled: it computes no result. Nor are `PublicKey::verify_digest`,
`from_spki`, and `to_spki`, or `Ed25519KeyPair`'s `from_seed` and
`to_pkcs8v1`, which no theorem here is about: `from_spki` builds its key with
`PublicKey::new`, and the others build no `Parsed`. Drops are not modelled, as everywhere in the
translation. `MAX_PUBLIC_KEY_LEN` is the larger of `rsa::MAX_PUBLIC_KEY_LEN`,
8192 / 8 + 64 = 1088, and ML-DSA-87's public key length, 32 + 8 * 320 =
2592.
-/

namespace rind.x86_64

/-- `Parsed`. -/
inductive high.signature.Parsed where
  | Ed25519 (key : high.ed25519.Ed25519VerifyingKey)
  | Other (verify : Slice Std.U8 → Slice Std.U8 → Result (core.result.Result Unit error.Error))

/-- `PublicKey`. -/
structure high.signature.PublicKey where
  key : high.signature.Parsed
  encoding : high.signature.Buffer 2592#usize

/-- `Verification`, and `VerificationAlgorithm`, which holds one. -/
inductive high.signature.Verification where
  | Ed25519
  | Other (new : Slice Std.U8 → Result (core.result.Result high.signature.PublicKey error.Error))

/-- `parse_ed25519`, whose `Verifier`'s `verify` is `Ed25519VerifyingKey::verify`. -/
def high.signature.parse_ed25519 (bytes : Slice Std.U8) :
    Result (core.result.Result high.signature.Parsed error.Error) := do
  let r ← high.ed25519.Ed25519VerifyingKey.from_bytes bytes
  match r with
  | .Ok key => ok (.Ok (.Ed25519 key))
  | .Err e => ok (.Err e)

/-- The `ED25519` static, whose parser is `parse_ed25519`. -/
def high.signature.verify.ED25519 : high.signature.Verification := .Ed25519

/-- `PublicKey::new`. -/
def high.signature.PublicKey.new (algorithm : high.signature.Verification) (bytes : Slice Std.U8) :
    Result (core.result.Result high.signature.PublicKey error.Error) :=
  match algorithm with
  | .Ed25519 => do
    let r ← high.signature.parse_ed25519 bytes
    match r with
    | .Ok key =>
      let b ← high.signature.Buffer.copy_from 2592#usize bytes
      match b with
      | .Ok encoding => ok (.Ok { key, encoding })
      | .Err e => ok (.Err e)
    | .Err e => ok (.Err e)
  | .Other new => new bytes

/-- `PublicKey::verify`, whose Ed25519 `Verifier`'s `verify` is
`Ed25519VerifyingKey::verify`. -/
def high.signature.PublicKey.verify (self : high.signature.PublicKey) (message signature : Slice Std.U8) :
    Result (core.result.Result Unit error.Error) :=
  match self.key with
  | .Ed25519 key => high.ed25519.Ed25519VerifyingKey.verify key signature message
  | .Other verify => verify message signature

/-- `PublicKey`'s `AsRef<[u8]>`. -/
def high.signature.PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref (self : high.signature.PublicKey) :
    Result (Slice Std.U8) :=
  high.signature.Buffer.Insts.CoreConvertAsRefSliceU8.as_ref self.encoding

/-- `Ed25519KeyPair::public_key`, as the translation names a method that shares
a field's name, whose `Verifier`'s `verify` is
`Ed25519VerifyingKey::verify`. -/
def high.signature.Ed25519KeyPair.impl.public_key (self : high.signature.Ed25519KeyPair) :
    Result high.signature.PublicKey := do
  let key ← high.ed25519.Ed25519SigningKey.public_key self.key
  let b ← high.signature.Buffer.Insts.CoreConvertFromArrayU8N.from self.public_key
  let encoding ← high.signature.Buffer.widen 2592#usize b
  ok { key := .Ed25519 key, encoding }

end rind.x86_64
