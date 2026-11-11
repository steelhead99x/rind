// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use crate::Error;
use crate::error::KeyFormatError;
use crate::high::asn1::{self, Type, pkix};
use crate::high::hash::{self, Hash};
use crate::high::{pkcs1, pkcs8};
use crate::low::{Entry, PosInt, ct};
use crate::mid::rng::SystemRandom;
use crate::mid::rsa_key_size::RsaKeySize;
use crate::mid::{rsa_priv, rsa_pub};

/// The longest PKCS#1 `RSAPublicKey`: the modulus and its DER framing, with
/// room for the exponent.
pub(crate) const MAX_PUBLIC_KEY_LEN: usize = rsa_pub::MAX_PUBLIC_MODULUS_BYTES + 64;

/// The longest PKCS#8 private key: an `RSAPrivateKey` in an octet string,
/// after its version and algorithm identifier.
pub(crate) const MAX_PKCS8_LEN: usize = SigningKey::MAX_PKCS1_BUFFER_LEN + 64;

/// The algorithms an RSA key's `SubjectPublicKeyInfo` or PKCS#8 may name,
/// all for the same key, as aws-lc takes them: `rsaEncryption`, RFC 4055's
/// `id-RSAES-OAEP`, and X.509's `id-ea-rsa`.
static KEY_ALGORITHMS: [&asn1::ObjectId; 3] = [
    &asn1::oid::rsaEncryption,
    &asn1::oid::id_RSAES_OAEP,
    &asn1::oid::id_ea_rsa,
];

/// Reads a big-endian public exponent for `RsaPublicKey::new` to bound; one
/// too wide for a `u64` is far past that bound.
fn public_exponent(e: &[u8]) -> Result<u64, Error> {
    if e.len() > size_of::<u64>() {
        return Err(KeyFormatError::RsaExponent.into());
    }
    Ok(e.iter().fold(0, |e, byte| e << 8 | u64::from(*byte)))
}

/// How long an RSASSA-PSS salt is.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum PssSalt {
    /// The hash's length.
    Hash,
    /// The longest the modulus allows.
    Max,
    /// This many bytes.
    Len(u16),
}

impl PssSalt {
    /// The salt length for an `em_len`-byte encoded message and an
    /// `h_len`-byte hash, which may not fit it.
    fn len(self, em_len: usize, h_len: usize) -> usize {
        match self {
            Self::Hash => h_len,
            Self::Max => em_len.saturating_sub(h_len + 2),
            Self::Len(len) => len.into(),
        }
    }
}

/// An RSA verification public key.
///
/// Keys supported by this library have public moduli between
/// 1024- and 8192-bits; each verification algorithm may set a higher floor.
#[derive(Clone, Debug)]
pub(crate) struct VerifyingKey(rsa_pub::RsaPublicKey);

impl VerifyingKey {
    /// Loads an RSA public key from its big-endian modulus and exponent.
    ///
    /// A leading zero byte in either is refused, as ring and aws-lc-rs do.
    pub(crate) fn from_components(n: &[u8], e: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        if n.first() == Some(&0) || e.first() == Some(&0) {
            return Err(KeyFormatError::LeadingZero.into());
        }

        let n = PosInt::from_bytes(n).map_err(|_| KeyFormatError::RsaModulus)?;
        Ok(Self(rsa_pub::RsaPublicKey::new(n, public_exponent(e)?)?))
    }

    /// Decodes an RSA public key from PKCS#1 `RSAPublicKey` or
    /// `SubjectPublicKeyInfo` DER, as aws-lc-rs takes either.
    pub(crate) fn from_der(bytes: &[u8]) -> Result<Self, Error> {
        match asn1::opens_nested_sequence(bytes) {
            true => Self::from_spki_der(bytes),
            false => Self::from_pkcs1_der(bytes),
        }
    }

    /// Decodes an RSA public key from `SubjectPublicKeyInfo` DER, whose
    /// algorithm must be one of [`KEY_ALGORITHMS`] with `NULL` parameters, as
    /// RFC 3279 section 2.3.1 requires for `rsaEncryption`, or none, which
    /// aws-lc also takes.
    fn from_spki_der(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        let spki = pkix::SubjectPublicKeyInfo::from_bytes(bytes).map_err(KeyFormatError::Asn1)?;
        if !KEY_ALGORITHMS.contains(&&spki.algorithm.algorithm)
            || !matches!(
                spki.algorithm.parameters,
                None | Some(asn1::Any::Null(asn1::Null))
            )
        {
            return Err(KeyFormatError::MismatchedSpkiAlgorithm.into());
        }
        Self::from_pkcs1_der(spki.subjectPublicKey.as_octets())
    }

    /// Decodes an RSA public verification key from PKCS#1 DER format.
    ///
    /// This format is defined in
    /// [RFC8017](https://datatracker.ietf.org/doc/html/rfc8017#appendix-A.1.1)
    /// (and earlier standards, including the original PKCS#1 standard).
    fn from_pkcs1_der(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        let decoded = pkix::RSAPublicKey::from_bytes(bytes).map_err(KeyFormatError::Asn1)?;

        if decoded.modulus.is_negative() {
            return Err(KeyFormatError::RsaModulus.into());
        }
        if decoded.publicExponent.is_negative() {
            return Err(KeyFormatError::RsaExponent.into());
        }

        let n =
            PosInt::from_bytes(decoded.modulus.as_ref()).map_err(|_| KeyFormatError::RsaModulus)?;
        let e = public_exponent(decoded.publicExponent.as_ref())?;
        let pub_key = rsa_pub::RsaPublicKey::new(n, e)?;

        Ok(Self(pub_key))
    }

    /// Encodes this RSA verification key in SubjectPublicKeyInfo DER format.
    ///
    /// The `SubjectPublicKeyInfo.algorithm` identifier is `rsaEncryption`.
    ///
    /// `output` is the output buffer, and the encoding is written to the start
    /// of this buffer.  An error is returned if the encoding is larger than
    /// the supplied buffer.  Otherwise, on success, the range containing the
    /// encoding is returned.
    pub(crate) fn to_spki_der<'a>(&self, output: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_public();

        let mut pub_key_buffer = [0u8; MAX_PUBLIC_KEY_LEN];
        let pub_key_buffer = self.to_pkcs1_der(&mut pub_key_buffer)?;

        let spki = pkix::SubjectPublicKeyInfo {
            algorithm: pkix::AlgorithmIdentifier {
                algorithm: asn1::oid::rsaEncryption.clone(),
                parameters: Some(asn1::Any::Null(asn1::Null)),
            },
            subjectPublicKey: asn1::BitString::new(pub_key_buffer),
        };

        let len = spki
            .encode(&mut asn1::Encoder::new(output))
            .map_err(|_| Error::WrongLength)?;
        Ok(&output[..len])
    }

    /// Encodes this RSA verification key to PKCS#1 DER format.
    ///
    /// `output` is the output buffer, and the encoding is written to the start
    /// of this buffer.  An error is returned if the encoding is larger than
    /// the supplied buffer.  Otherwise, on success, the range containing the
    /// encoding is returned.
    pub(crate) fn to_pkcs1_der<'a>(&self, output: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_public();

        let mut buffer = [0u8; rsa_pub::MAX_PUBLIC_MODULUS_BYTES + 1];
        let public_modulus = self.0.n.to_bytes_asn1(&mut buffer)?;
        let public_exponent = self.0.e.to_be_bytes();

        let pub_key = pkix::RSAPublicKey {
            modulus: asn1::Integer::new(public_modulus),
            publicExponent: asn1::Integer::new(&public_exponent),
        };
        let used = pub_key
            .encode(&mut asn1::Encoder::new(output))
            .map_err(|_| Error::WrongLength)?;
        Ok(&output[..used])
    }

    /// Returns the public modulus length, in bits.
    pub(crate) fn modulus_len_bits(&self) -> usize {
        self.0.modulus_len_bits()
    }

    /// Verifies `signature`, using RSASSA-PKCS1-v1_5 with SHA-1.
    ///
    /// `message` is the (unhashed) signed message.  It is hashed
    /// using SHA-1 by this function.
    ///
    /// [`Error::BadSignature`] is returned if the signature is invalid.
    pub(crate) fn verify_pkcs1_sha1(&self, signature: &[u8], message: &[u8]) -> Result<(), Error> {
        let _entry = Entry::new_public();
        let hash = hash::LegacySha1::hash(message);
        self._verify_pkcs1(signature, pkcs1::DIGESTINFO_SHA1, hash.as_ref())
    }

    /// Verifies `signature`, using RSASSA-PKCS1-v1_5 with SHA-256.
    ///
    /// `message` is the (unhashed) signed message.  It is hashed
    /// using SHA-256 by this function.
    ///
    /// [`Error::BadSignature`] is returned if the signature is invalid.
    pub(crate) fn verify_pkcs1_sha256(
        &self,
        signature: &[u8],
        message: &[u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_public();
        let hash = hash::Sha256::hash(message);
        self._verify_pkcs1(signature, pkcs1::DIGESTINFO_SHA256, hash.as_ref())
    }

    /// Verifies `signature`, using RSASSA-PKCS1-v1_5 with SHA-384.
    ///
    /// `message` is the (unhashed) signed message.  It is hashed
    /// using SHA-384 by this function.
    ///
    /// [`Error::BadSignature`] is returned if the signature is invalid.
    pub(crate) fn verify_pkcs1_sha384(
        &self,
        signature: &[u8],
        message: &[u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_public();
        let hash = hash::Sha384::hash(message);
        self._verify_pkcs1(signature, pkcs1::DIGESTINFO_SHA384, hash.as_ref())
    }

    /// Verifies `signature`, using RSASSA-PKCS1-v1_5 with SHA-512.
    ///
    /// `message` is the (unhashed) signed message.  It is hashed
    /// using SHA-512 by this function.
    ///
    /// [`Error::BadSignature`] is returned if the signature is invalid.
    pub(crate) fn verify_pkcs1_sha512(
        &self,
        signature: &[u8],
        message: &[u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_public();
        let hash = hash::Sha512::hash(message);
        self._verify_pkcs1(signature, pkcs1::DIGESTINFO_SHA512, hash.as_ref())
    }

    fn _verify_pkcs1(
        &self,
        signature: &[u8],
        digest_info: &[u8],
        hash: &[u8],
    ) -> Result<(), Error> {
        if signature.len() != self.0.modulus_len_bytes() {
            return Err(Error::BadSignature);
        }
        let c = PosInt::from_bytes(signature).map_err(|_| Error::BadSignature)?;
        let m = self.0.public_op(c).map_err(|_| Error::BadSignature)?;

        let mut m_bytes = [0u8; rsa_pub::MAX_PUBLIC_MODULUS_BYTES];
        let m_bytes = i2osp(&m, &mut m_bytes[..self.0.modulus_len_bytes()])?;

        let mut actual_m = [0u8; rsa_pub::MAX_PUBLIC_MODULUS_BYTES];
        let actual_m = &mut actual_m[..self.0.modulus_len_bytes()];
        pkcs1::encode_pkcs1_sig(actual_m, digest_info, hash);

        match actual_m == m_bytes {
            true => Ok(()),
            false => Err(Error::BadSignature),
        }
    }

    /// Verifies `signature`, using RSASSA-PSS with SHA-256 and a salt of
    /// `salt`'s length, or any length for `None`.
    ///
    /// `message` is the (unhashed) signed message.  It is hashed
    /// using SHA-256 by this function.
    ///
    /// [`Error::BadSignature`] is returned if the signature is invalid.
    ///
    /// RSASSA-PSS is described in
    /// [RFC8017](https://datatracker.ietf.org/doc/html/rfc8017#section-8.1)
    /// (and earlier standards, including the original PKCS#1 standard).
    pub(crate) fn verify_pss_sha256(
        &self,
        salt: Option<PssSalt>,
        signature: &[u8],
        message: &[u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_public();
        self._verify_pss::<hash::Sha256>(salt, signature, message)
    }

    /// Verifies `signature`, using RSASSA-PSS with SHA-384 and a salt of
    /// `salt`'s length, or any length for `None`.
    ///
    /// `message` is the (unhashed) signed message.  It is hashed
    /// using SHA-384 by this function.
    ///
    /// [`Error::BadSignature`] is returned if the signature is invalid.
    ///
    /// RSASSA-PSS is described in
    /// [RFC8017](https://datatracker.ietf.org/doc/html/rfc8017#section-8.1)
    /// (and earlier standards, including the original PKCS#1 standard).
    pub(crate) fn verify_pss_sha384(
        &self,
        salt: Option<PssSalt>,
        signature: &[u8],
        message: &[u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_public();
        self._verify_pss::<hash::Sha384>(salt, signature, message)
    }

    /// Verifies `signature`, using RSASSA-PSS with SHA-512 and a salt of
    /// `salt`'s length, or any length for `None`.
    ///
    /// `message` is the (unhashed) signed message.  It is hashed
    /// using SHA-512 by this function.
    ///
    /// [`Error::BadSignature`] is returned if the signature is invalid.
    ///
    /// RSASSA-PSS is described in
    /// [RFC8017](https://datatracker.ietf.org/doc/html/rfc8017#section-8.1)
    /// (and earlier standards, including the original PKCS#1 standard).
    pub(crate) fn verify_pss_sha512(
        &self,
        salt: Option<PssSalt>,
        signature: &[u8],
        message: &[u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_public();
        self._verify_pss::<hash::Sha512>(salt, signature, message)
    }

    fn _verify_pss<H: Hash>(
        &self,
        salt: Option<PssSalt>,
        signature: &[u8],
        message: &[u8],
    ) -> Result<(), Error> {
        let hash = H::hash(message);

        if signature.len() != self.0.modulus_len_bytes() {
            return Err(Error::BadSignature);
        }
        let c = PosInt::from_bytes(signature).map_err(|_| Error::BadSignature)?;
        let m = self.0.public_op(c).map_err(|_| Error::BadSignature)?;

        // RFC 8017 section 8.1.2: EM is only `ceil(emBits / 8)` octets, one
        // fewer than the modulus when its bit length is one more than a
        // multiple of eight, and `m` must fit them.
        let em_bits = self.0.modulus_len_bits() - 1;
        let mut em = [0u8; rsa_pub::MAX_PUBLIC_MODULUS_BYTES];
        let em = i2osp(&m, &mut em[..em_bits.div_ceil(8)]).map_err(|_| Error::BadSignature)?;

        let s_len = salt.map(|salt| salt.len(em.len(), hash.as_ref().len()));
        pkcs1::verify_pss_sig::<H>(em, em_bits, hash.as_ref(), s_len)
    }

    /// Encrypts `message` with RSAES-OAEP, using `H` and MGF1 with `H`,
    /// into the front of `ciphertext`, as long as the modulus.
    ///
    /// A message longer than [`pkcs1::oaep_max_message_len`] is refused
    /// with [`Error::WrongLength`].
    ///
    /// RSAES-OAEP is described in
    /// [RFC8017](https://datatracker.ietf.org/doc/html/rfc8017#section-7.1.1).
    pub(crate) fn encrypt_oaep<'a, H: Hash>(
        &self,
        ciphertext: &'a mut [u8],
        message: &[u8],
        label: &[u8],
    ) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        let k = self.0.modulus_len_bytes();
        let ciphertext = ciphertext.get_mut(..k).ok_or(Error::WrongLength)?;

        let mut em = [0u8; rsa_pub::MAX_PUBLIC_MODULUS_BYTES];
        let em = &mut em[..k];
        pkcs1::encode_oaep::<H>(em, &mut SystemRandom, message, label)?;

        // The encoded message is secret, so it is read at the modulus's
        // width rather than by `PosInt::from_bytes`, which skips its
        // leading zeros.
        let mut words = [0u64; rsa_pub::MAX_PUBLIC_MODULUS_BYTES / 8];
        let words = &mut words[..k.div_ceil(8)];
        for (word, bytes) in words.iter_mut().zip(em.rchunks(8)) {
            *word = bytes.iter().fold(0, |w, b| w << 8 | u64::from(*b));
        }
        let m = PosInt::from_words(words)?;

        // `m` is below the modulus, as EM's first octet is zero.
        let c = ct::into_public(self.0.public_op(m)?);
        i2osp(&c, ciphertext).map(|c| &*c)
    }

    /// The public modulus length, in bytes.
    pub(crate) fn modulus_len_bytes(&self) -> usize {
        self.0.modulus_len_bytes()
    }

    /// `base^e mod n`, written at the modulus length.
    ///
    /// `base` is big-endian and at most that long. It must be below `n`.
    pub(crate) fn public_op_be<'a>(
        &self,
        base: &[u8],
        out: &'a mut [u8],
    ) -> Result<&'a [u8], Error> {
        let c = self.0.int_from_be(base)?;
        let m = self.0.public_op(c)?;
        let out = out
            .get_mut(..self.modulus_len_bytes())
            .ok_or(Error::WrongLength)?;
        i2osp(&m, out).map(|m| &*m)
    }

    /// `a * b mod n`, both big-endian and below `n`, at the modulus length.
    pub(crate) fn mul_mod_be<'a>(
        &self,
        a: &[u8],
        b: &[u8],
        out: &'a mut [u8],
    ) -> Result<&'a [u8], Error> {
        let a = self.0.int_from_be(a)?;
        let b = self.0.int_from_be(b)?;
        let m = self.0.mul_mod(&a, &b)?;
        let out = out
            .get_mut(..self.modulus_len_bytes())
            .ok_or(Error::WrongLength)?;
        i2osp(&m, out).map(|m| &*m)
    }

    /// Whether `a` and the modulus are coprime. The verdict is declassified.
    pub(crate) fn is_coprime_be(&self, a: &[u8]) -> Result<bool, Error> {
        let a = self.0.int_from_be(a)?;
        Ok(ct::into_public(a.is_coprime(&self.0.n)))
    }

    /// `a^{-1} mod n` at the modulus length.
    ///
    /// Fails with [`Error::Unsupported`] when `a` shares a factor with `n`.
    pub(crate) fn invert_be<'a>(&self, a: &[u8], out: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let a = self.0.int_from_be(a)?;
        let mut zero = PosInt::zero();
        zero.expand(&self.0.n);
        if !ct::into_public(a.less_than(&self.0.n) & !a.equals(&zero) & a.is_coprime(&self.0.n)) {
            return Err(Error::Unsupported);
        }
        let inv = a.mod_inverse(&self.0.n);
        let out = out
            .get_mut(..self.modulus_len_bytes())
            .ok_or(Error::WrongLength)?;
        i2osp(&inv, out).map(|inv| &*inv)
    }

    /// A random residue in `1..n` coprime to `n`, at the modulus length.
    pub(crate) fn random_factor_be<'a>(
        &self,
        rng: &mut dyn crate::mid::rng::RandomSource,
        out: &'a mut [u8],
    ) -> Result<&'a [u8], Error> {
        let r = self.0.random_factor(rng)?;
        let out = out
            .get_mut(..self.modulus_len_bytes())
            .ok_or(Error::WrongLength)?;
        i2osp(&r, out).map(|r| &*r)
    }
}

/// An RSA signing private key.
///
/// Keys supported by this library have public moduli between
/// 2048- and 8192-bits.  Only two-prime RSA keys are supported.
pub(crate) struct SigningKey(rsa_priv::RsaPrivateKey);

impl SigningKey {
    /// Generates a new RSA signing key.
    ///
    /// `size` is the desired key size.  This library supports a selection of common key sizes.
    ///
    /// Key generation is a slow process, especially for larger key sizes.  As an indication,
    /// an 2048-bit key takes about 30 milliseconds, while an 8192-bit key may take 15 seconds or more.
    /// The time required is non-deterministic, and does not have an upper bound.
    /// It is constant in the primes, revealing only which candidates are discarded.
    pub(crate) fn generate(size: RsaKeySize) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        rsa_priv::RsaPrivateKey::generate(size, &mut SystemRandom, &mut SystemRandom)
            .map(SigningKey)
    }

    /// Decodes an RSA signing key from PKCS#1 DER format.
    ///
    /// This format is defined in
    /// [RFC8017](https://datatracker.ietf.org/doc/html/rfc8017#appendix-A.1.2)
    /// (and earlier standards, including the original PKCS#1 standard).
    pub(crate) fn from_pkcs1_der(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        let decoded = pkix::RSAPrivateKey::from_bytes(bytes).map_err(KeyFormatError::Asn1)?;

        if !matches!(decoded.version, pkix::Version::two_prime) {
            return Err(KeyFormatError::MultiPrimeRsa.into());
        }

        if decoded.modulus.is_negative() {
            return Err(KeyFormatError::RsaModulus.into());
        }
        if decoded.publicExponent.is_negative() {
            return Err(KeyFormatError::RsaExponent.into());
        }

        let n =
            PosInt::from_bytes(decoded.modulus.as_ref()).map_err(|_| KeyFormatError::RsaModulus)?;
        let e = public_exponent(decoded.publicExponent.as_ref())?;

        let prime = |x: &asn1::Integer<'_>| {
            PosInt::from_bytes(x.as_ref()).map_err(|_| KeyFormatError::RsaPrimes)
        };
        let p = prime(&decoded.prime1)?;
        let q = prime(&decoded.prime2)?;
        // A component too wide for its slot cannot agree with the others.
        let mismatched = |_| KeyFormatError::MismatchedRsaComponents;
        let d = PosInt::from_bytes(decoded.privateExponent.as_ref()).map_err(mismatched)?;
        let dp = PosInt::from_bytes(decoded.exponent1.as_ref()).map_err(mismatched)?;
        let dq = PosInt::from_bytes(decoded.exponent2.as_ref()).map_err(mismatched)?;
        let iqmp = PosInt::from_bytes(decoded.coefficient.as_ref()).map_err(mismatched)?;

        let priv_key = rsa_priv::RsaPrivateKey::new(p, q, d, dp, dq, iqmp, n, e)?;
        Ok(Self(priv_key))
    }

    /// Encodes an RSA signing key to PKCS#1 DER format.
    ///
    /// `output` is the output buffer, and the encoding is written to the start
    /// of this buffer.  An error is returned if the encoding is larger than
    /// the supplied buffer.  Otherwise, on success, the range containing the
    /// encoding is returned.
    pub(crate) fn to_pkcs1_der<'a>(&self, output: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();

        let mut buf = rsa_priv::RsaComponentsBuffer::default();
        let components = self.0.encode_components(&mut buf)?;

        let used = pkix::RSAPrivateKey {
            version: pkix::Version::two_prime,
            modulus: asn1::Integer::new(components.public_modulus),
            publicExponent: asn1::Integer::new(components.public_exponent),
            prime1: asn1::Integer::new(components.p),
            prime2: asn1::Integer::new(components.q),
            privateExponent: asn1::Integer::new(components.d),
            exponent1: asn1::Integer::new(components.dp),
            exponent2: asn1::Integer::new(components.dq),
            coefficient: asn1::Integer::new(components.iqmp),
        }
        .encode(&mut asn1::Encoder::new(output))
        .map_err(|_| Error::WrongLength)?;

        output.get(..used).ok_or(Error::WrongLength)
    }

    // this is an over-estimate
    const MAX_PKCS1_BUFFER_LEN: usize = rsa_priv::RsaComponentsBuffer::LEN + 128;

    /// Encodes an RSA signing key to PKCS#8 DER format.
    ///
    /// `output` is the output buffer, and the encoding is written to the start
    /// of this buffer.  An error is returned if the encoding is larger than
    /// the supplied buffer.  Otherwise, on success, the range containing the
    /// encoding is returned.
    pub(crate) fn to_pkcs8_der<'a>(&self, output: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();

        let mut pkcs1_buffer = [0u8; Self::MAX_PKCS1_BUFFER_LEN];

        pkcs8::Key::construct(
            self.to_pkcs1_der(&mut pkcs1_buffer)?,
            None,
            asn1::oid::rsaEncryption.clone(),
            Some(asn1::Any::Null(asn1::Null)),
        )
        .encode(output)
    }

    /// Decodes an RSA signing key from PKCS#8 DER format.
    ///
    /// This format is defined in
    /// [RFC5208](https://datatracker.ietf.org/doc/html/rfc5208#section-5)
    /// (and earlier standards, including the original PKCS#8 standard).
    ///
    /// `privateKeyAlgorithm` inside this encoding must be one of
    /// [`KEY_ALGORITHMS`] with `NULL` parameters, as aws-lc requires.
    pub(crate) fn from_pkcs8_der(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        pkcs8::Key::decode(bytes, &KEY_ALGORITHMS, Some(asn1::Any::Null(asn1::Null)))
            .and_then(|k| Self::from_pkcs1_der(k.v1_private_key()?))
    }

    /// A two-prime key from its prime factors, private exponent, modulus,
    /// and public exponent.
    #[cfg(test)]
    pub(crate) fn from_components(
        p: &[u8],
        q: &[u8],
        d: &[u8],
        n: &[u8],
        e: u64,
    ) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        Ok(Self(rsa_priv::RsaPrivateKey::from_components(
            p, q, d, n, e,
        )?))
    }

    /// RSASP1 on a modulus-length integer, checked against the public key.
    ///
    /// The result is declassified: a blind signature is what the signer sends.
    pub(crate) fn blind_sign<'a>(
        &self,
        blinded: &[u8],
        out: &'a mut [u8],
    ) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        if blinded.len() != self.0.modulus_len_bytes() {
            return Err(Error::WrongLength);
        }
        let m = PosInt::from_bytes(blinded).map_err(|_| Error::WrongLength)?;
        let c = ct::into_public(self.0.private_op(&m)?);
        self.to_signature(&c, out)
    }

    /// Returns the matching public key.
    pub(crate) fn public_key(&self) -> VerifyingKey {
        let _entry = Entry::new_public();
        VerifyingKey(self.0.public_key())
    }

    /// Returns the public modulus length, in bytes.
    pub(crate) fn modulus_len_bytes(&self) -> usize {
        let _entry = Entry::new_public();
        self.0.public_key().modulus_len_bytes()
    }

    /// Signs `message`, using RSASSA-PKCS1-v1_5 with SHA-256.
    ///
    /// The signature is written to the front of `signature`, is
    /// precisely [`Self::modulus_len_bytes()`] in length, and
    /// then the written-to slice is returned.
    ///
    /// RSASSA-PKCS1-v1_5 is described in
    /// [RFC8017](https://datatracker.ietf.org/doc/html/rfc8017#section-8.2)
    /// (and earlier standards, including the original PKCS#1 standard).
    pub(crate) fn sign_pkcs1_sha256<'a>(
        &self,
        signature: &'a mut [u8],
        message: &[u8],
    ) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        let hash = hash::Sha256::hash(message);
        self._sign_pkcs1(signature, pkcs1::DIGESTINFO_SHA256, hash.as_ref())
    }

    /// Signs `message`, using RSASSA-PKCS1-v1_5 with SHA-384.
    ///
    /// The signature is written to the front of `signature`, is
    /// precisely [`Self::modulus_len_bytes()`] in length, and
    /// then the written-to slice is returned.
    ///
    /// RSASSA-PKCS1-v1_5 is described in
    /// [RFC8017](https://datatracker.ietf.org/doc/html/rfc8017#section-8.2)
    /// (and earlier standards, including the original PKCS#1 standard).
    pub(crate) fn sign_pkcs1_sha384<'a>(
        &self,
        signature: &'a mut [u8],
        message: &[u8],
    ) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        let hash = hash::Sha384::hash(message);
        self._sign_pkcs1(signature, pkcs1::DIGESTINFO_SHA384, hash.as_ref())
    }

    /// Signs `message`, using RSASSA-PKCS1-v1_5 with SHA-512.
    ///
    /// The signature is written to the front of `signature`, is
    /// precisely [`Self::modulus_len_bytes()`] in length, and
    /// then the written-to slice is returned.
    ///
    /// RSASSA-PKCS1-v1_5 is described in
    /// [RFC8017](https://datatracker.ietf.org/doc/html/rfc8017#section-8.2)
    /// (and earlier standards, including the original PKCS#1 standard).
    pub(crate) fn sign_pkcs1_sha512<'a>(
        &self,
        signature: &'a mut [u8],
        message: &[u8],
    ) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        let hash = hash::Sha512::hash(message);
        self._sign_pkcs1(signature, pkcs1::DIGESTINFO_SHA512, hash.as_ref())
    }

    /// Signs `message`, using RSASSA-PSS with SHA-256 and a salt of `salt`'s
    /// length, refusing the key if its modulus is too short for it.
    ///
    /// The signature is written to the front of `signature`, is
    /// precisely [`Self::modulus_len_bytes()`] in length, and
    /// then the written-to slice is returned.
    ///
    /// RSASSA-PSS is described in
    /// [RFC8017](https://datatracker.ietf.org/doc/html/rfc8017#section-8.1)
    /// (and earlier standards, including the original PKCS#1 standard).
    pub(crate) fn sign_pss_sha256<'a>(
        &self,
        salt: PssSalt,
        signature: &'a mut [u8],
        message: &[u8],
    ) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        self._sign_pss::<hash::Sha256>(salt, signature, message)
    }

    /// Signs `message`, using RSASSA-PSS with SHA-384 and a salt of `salt`'s
    /// length, refusing the key if its modulus is too short for it.
    ///
    /// The signature is written to the front of `signature`, is
    /// precisely [`Self::modulus_len_bytes()`] in length, and
    /// then the written-to slice is returned.
    ///
    /// RSASSA-PSS is described in
    /// [RFC8017](https://datatracker.ietf.org/doc/html/rfc8017#section-8.1)
    /// (and earlier standards, including the original PKCS#1 standard).
    pub(crate) fn sign_pss_sha384<'a>(
        &self,
        salt: PssSalt,
        signature: &'a mut [u8],
        message: &[u8],
    ) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        self._sign_pss::<hash::Sha384>(salt, signature, message)
    }

    /// Signs `message`, using RSASSA-PSS with SHA-512 and a salt of `salt`'s
    /// length, refusing the key if its modulus is too short for it.
    ///
    /// The signature is written to the front of `signature`, is
    /// precisely [`Self::modulus_len_bytes()`] in length, and
    /// then the written-to slice is returned.
    ///
    /// RSASSA-PSS is described in
    /// [RFC8017](https://datatracker.ietf.org/doc/html/rfc8017#section-8.1)
    /// (and earlier standards, including the original PKCS#1 standard).
    pub(crate) fn sign_pss_sha512<'a>(
        &self,
        salt: PssSalt,
        signature: &'a mut [u8],
        message: &[u8],
    ) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        self._sign_pss::<hash::Sha512>(salt, signature, message)
    }

    fn _sign_pkcs1<'a>(
        &self,
        signature: &'a mut [u8],
        digest_info: &[u8],
        hash: &[u8],
    ) -> Result<&'a [u8], Error> {
        if signature.len() < self.0.modulus_len_bytes() {
            return Err(Error::WrongLength);
        }

        let mut m = [0u8; rsa_pub::MAX_PUBLIC_MODULUS_BYTES];
        let m = &mut m[..self.0.modulus_len_bytes()];
        pkcs1::encode_pkcs1_sig(m, digest_info, hash);

        let m = PosInt::from_bytes(m)?;
        let c = ct::into_public(self.0.private_op(&m)?);
        self.to_signature(&c, signature)
    }

    fn _sign_pss<'a, H: Hash>(
        &self,
        salt: PssSalt,
        signature: &'a mut [u8],
        message: &[u8],
    ) -> Result<&'a [u8], Error> {
        if signature.len() < self.0.modulus_len_bytes() {
            return Err(Error::WrongLength);
        }

        let hash = H::hash(message);

        // RFC 8017 section 8.1.1: EM is only `ceil(emBits / 8)` octets, one
        // fewer than the modulus when its bit length is one more than a
        // multiple of eight.
        let em_bits = self.0.modulus_len_bits() - 1;
        let mut em = [0u8; rsa_pub::MAX_PUBLIC_MODULUS_BYTES];
        let em = &mut em[..em_bits.div_ceil(8)];

        let s_len = salt.len(em.len(), hash.as_ref().len());
        pkcs1::encode_pss_sig::<H>(em, em_bits, &mut SystemRandom, hash.as_ref(), s_len)?;
        let m = PosInt::from_bytes(em)?;
        let c = ct::into_public(self.0.private_op(&m)?);
        self.to_signature(&c, signature)
    }

    /// Decrypts `ciphertext` with RSAES-OAEP, using `H` and MGF1 with `H`,
    /// into the front of `plaintext`, which must hold
    /// [`pkcs1::oaep_max_message_len`] bytes.
    ///
    /// Every failure but [`Error::Fault`] is [`Error::DecryptFailed`],
    /// which reveals nothing of the decrypted value.
    ///
    /// RSAES-OAEP is described in
    /// [RFC8017](https://datatracker.ietf.org/doc/html/rfc8017#section-7.1.2).
    pub(crate) fn decrypt_oaep<'a, H: Hash>(
        &self,
        plaintext: &'a mut [u8],
        ciphertext: &[u8],
        label: &[u8],
    ) -> Result<&'a [u8], Error> {
        let _entry = Entry::new_secret();
        // 1b.  If the length of the ciphertext C is not k octets, output
        //      "decryption error" and stop.
        let k = self.0.modulus_len_bytes();
        if ciphertext.len() != k {
            return Err(Error::DecryptFailed);
        }

        // 2a.  Convert the ciphertext C to an integer ciphertext
        //      representative c.
        // 2b.  Apply the RSADP decryption primitive, which refuses a c not
        //      below the modulus.
        let c = PosInt::from_bytes(ciphertext).map_err(|_| Error::DecryptFailed)?;
        let m = self.0.private_op(&c).map_err(|e| match e {
            Error::Fault => Error::Fault,
            _ => Error::DecryptFailed,
        })?;

        // 2c.  Convert the message representative m to an encoded message
        //      EM of length k octets, which `m` below the modulus fits.
        let mut em = [0u8; rsa_pub::MAX_PUBLIC_MODULUS_BYTES];
        let em = i2osp(&m, &mut em[..k])?;

        pkcs1::decode_oaep::<H>(em, label, plaintext)
    }

    /// Writes `c` to the front of `signature` in exactly the modulus length.
    fn to_signature<'a, const N: usize>(
        &self,
        c: &PosInt<N>,
        signature: &'a mut [u8],
    ) -> Result<&'a [u8], Error> {
        let signature = signature
            .get_mut(..self.0.modulus_len_bytes())
            .ok_or(Error::WrongLength)?;
        Ok(i2osp(c, signature)?)
    }
}

/// This is I2OSP: writes `x` to all of `out`, big-endian, however many of its
/// leading bytes are zero, and refuses an `x` that does not fit.
///
/// Constant time in `x`, apart from whether it fits.
fn i2osp<'a, const N: usize>(x: &PosInt<N>, out: &'a mut [u8]) -> Result<&'a mut [u8], Error> {
    let mut bytes = [0u8; rsa_pub::MAX_PUBLIC_MODULUS_BYTES];
    let bytes = x.to_bytes(&mut bytes)?;
    let (excess, bytes) = bytes.split_at(bytes.len().saturating_sub(out.len()));
    if ct::into_public(excess.iter().fold(0, |acc, b| acc | b)) != 0 {
        return Err(Error::WrongLength);
    }

    let (zeroes, value) = out.split_at_mut(out.len() - bytes.len());
    zeroes.fill(0);
    value.copy_from_slice(bytes);
    Ok(out)
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::high::hmac_drbg::HmacDrbg;
    use crate::mid::rng::SliceRandomSource;
    use crate::test::{Acvp, acvp};

    /// Verifies each test's signature under its group's key, returning
    /// `None` for a group whose public exponent rind refuses: above 33 bits,
    /// as aws-lc refuses.
    fn acvp_verify(group: &serde_json::Value, test: &serde_json::Value) -> Option<bool> {
        let e = group.hex("e");
        let key = VerifyingKey::from_components(&group.hex("n"), &e);
        if e.len() * 8 - e[0].leading_zeros() as usize > 33 {
            assert_eq!(key.err(), Some(KeyFormatError::RsaExponent.into()));
            return None;
        }
        let key = key.unwrap();
        let (signature, message) = (test.hex("signature"), test.hex("message"));
        let salt = Some(PssSalt::Len(u16::try_from(group.int("saltLen")).unwrap()));
        let result = match (group.str("sigType"), group.str("hashAlg")) {
            ("pkcs1v1.5", "SHA2-256") => key.verify_pkcs1_sha256(&signature, &message),
            ("pkcs1v1.5", "SHA2-384") => key.verify_pkcs1_sha384(&signature, &message),
            ("pkcs1v1.5", "SHA2-512") => key.verify_pkcs1_sha512(&signature, &message),
            ("pss", "SHA2-256") => key.verify_pss_sha256(salt, &signature, &message),
            ("pss", "SHA2-384") => key.verify_pss_sha384(salt, &signature, &message),
            ("pss", "SHA2-512") => key.verify_pss_sha512(salt, &signature, &message),
            other => panic!("unexpected signature type {other:?}"),
        };
        if group.str("sigType") == "pss" {
            assert_eq!(group.str("maskFunction"), "mgf1");
        }
        Some(result.is_ok())
    }

    #[test]
    fn acvp_sig_ver() {
        for group in acvp("RSA-SigVer-FIPS186-5") {
            for test in group.tests() {
                if let Some(valid) = acvp_verify(&group, test) {
                    assert_eq!(valid, test.flag("testPassed"), "{}", test.str("reason"));
                }
            }
        }
    }

    /// ACVP's signing answers come from keys it does not publish, so they
    /// are checked as a validator checks a signer's: they must verify.
    #[test]
    fn acvp_sig_gen() {
        for group in acvp("RSA-SigGen-FIPS186-5") {
            for test in group.tests() {
                assert_ne!(acvp_verify(&group, test), Some(false));
            }
        }
    }

    fn check_all_algs(buf: &mut [u8], private: &SigningKey, public: &VerifyingKey) {
        let sig = private.sign_pkcs1_sha256(buf, b"hello").unwrap();
        public.verify_pkcs1_sha256(sig, b"hello").unwrap();

        let sig = private.sign_pkcs1_sha384(buf, b"hello").unwrap();
        public.verify_pkcs1_sha384(sig, b"hello").unwrap();

        let sig = private.sign_pkcs1_sha512(buf, b"hello").unwrap();
        public.verify_pkcs1_sha512(sig, b"hello").unwrap();

        for salt in [
            PssSalt::Hash,
            PssSalt::Max,
            PssSalt::Len(0),
            PssSalt::Len(1),
        ] {
            let sig = private.sign_pss_sha256(salt, buf, b"hello").unwrap();
            public.verify_pss_sha256(Some(salt), sig, b"hello").unwrap();
            public.verify_pss_sha256(None, sig, b"hello").unwrap();

            let sig = private.sign_pss_sha384(salt, buf, b"hello").unwrap();
            public.verify_pss_sha384(Some(salt), sig, b"hello").unwrap();
            public.verify_pss_sha384(None, sig, b"hello").unwrap();

            let sig = private.sign_pss_sha512(salt, buf, b"hello").unwrap();
            public.verify_pss_sha512(Some(salt), sig, b"hello").unwrap();
            public.verify_pss_sha512(None, sig, b"hello").unwrap();
        }
    }

    #[test]
    fn pss_salt_must_fit_modulus() {
        let private_key = SigningKey::from_pkcs1_der(include_bytes!("rsa/rsa2048.der")).unwrap();
        let public_key = private_key.public_key();
        let mut buf = [0u8; 256];

        // A 2048-bit modulus leaves 256 - 32 - 2 bytes for a SHA-256 salt.
        let max = PssSalt::Len(222);
        let sig = private_key
            .sign_pss_sha256(max, &mut buf, b"hello")
            .unwrap();
        public_key
            .verify_pss_sha256(Some(PssSalt::Max), sig, b"hello")
            .unwrap();
        public_key.verify_pss_sha256(None, sig, b"hello").unwrap();
        assert_eq!(
            public_key.verify_pss_sha256(Some(PssSalt::Len(221)), sig, b"hello"),
            Err(Error::BadSignature)
        );
        assert_eq!(
            public_key.verify_pss_sha256(Some(PssSalt::Hash), sig, b"hello"),
            Err(Error::BadSignature)
        );

        let too_long = PssSalt::Len(223);
        assert_eq!(
            public_key.verify_pss_sha256(Some(too_long), sig, b"hello"),
            Err(Error::BadSignature)
        );
        assert_eq!(
            private_key
                .sign_pss_sha256(too_long, &mut buf, b"hello")
                .map(|_| ()),
            Err(KeyFormatError::RsaModulus.into())
        );
    }

    #[test]
    fn pairwise_rsa2048_sign_verify() {
        let private_key = SigningKey::from_pkcs1_der(include_bytes!("rsa/rsa2048.der")).unwrap();

        check_all_algs(&mut [0u8; 256], &private_key, &private_key.public_key());
    }

    #[test]
    fn verify_rejects_signature_not_modulus_length() {
        // RFC 8017 requires a signature of exactly k octets.  A zero byte
        // added to or removed from the front keeps its integer value, so
        // only the length check rejects these.
        type Sign = fn(&SigningKey, &mut [u8], &[u8]) -> Result<(), Error>;
        type Verify = fn(&VerifyingKey, &[u8], &[u8]) -> Result<(), Error>;
        let schemes: [(Sign, Verify); 2] = [
            (
                |k, s, m| k.sign_pkcs1_sha256(s, m).map(|_| ()),
                VerifyingKey::verify_pkcs1_sha256,
            ),
            (
                |k, s, m| k.sign_pss_sha256(PssSalt::Hash, s, m).map(|_| ()),
                |k, s, m| k.verify_pss_sha256(Some(PssSalt::Hash), s, m),
            ),
        ];

        let private_key = SigningKey::from_pkcs1_der(include_bytes!("rsa/rsa2048.der")).unwrap();
        let public_key = private_key.public_key();

        for (sign, verify) in schemes {
            let mut signature = [0u8; 257];
            for i in 0u32.. {
                let message = i.to_be_bytes();
                sign(&private_key, &mut signature[1..], &message).unwrap();
                assert_eq!(
                    verify(&public_key, &signature, &message),
                    Err(Error::BadSignature)
                );

                // About one signature in 256 starts with a zero byte.
                if signature[1] == 0 {
                    verify(&public_key, &signature[1..], &message).unwrap();
                    assert_eq!(
                        verify(&public_key, &signature[2..], &message),
                        Err(Error::BadSignature)
                    );
                    break;
                }
            }
        }
    }

    #[test]
    fn pairwise_rsa2048_sign_verify_pkcs8() {
        let private_key =
            SigningKey::from_pkcs8_der(include_bytes!("rsa/rsa2048.pkcs8.der")).unwrap();

        // Longer than the modulus: the signature takes the front.
        check_all_algs(&mut [0u8; 300], &private_key, &private_key.public_key());
    }

    #[test]
    fn i2osp_refuses_what_does_not_fit() {
        let x = PosInt::<1>::from_bytes(&[1, 1, 0, 0]).unwrap();
        assert_eq!(i2osp(&x, &mut [0; 2]).map(|_| ()), Err(Error::WrongLength));
        assert_eq!(i2osp(&x, &mut [0xff; 5]).unwrap(), [0, 1, 1, 0, 0]);
    }

    /// Primes of 20 words, a multiple of four but not of eight.
    #[test]
    fn pairwise_rsa2560_sign_verify() {
        let private_key =
            SigningKey::from_pkcs8_der(include_bytes!("rsa/rsa2560.pkcs8.der")).unwrap();

        check_all_algs(&mut [0u8; 320], &private_key, &private_key.public_key());
    }

    #[test]
    fn pairwise_rsa3072_sign_verify() {
        let private_key = SigningKey::from_pkcs1_der(include_bytes!("rsa/rsa3072.der")).unwrap();

        check_all_algs(&mut [0u8; 384], &private_key, &private_key.public_key());
    }

    #[test]
    fn pairwise_rsa4096_sign_verify() {
        let private_key = SigningKey::from_pkcs1_der(include_bytes!("rsa/rsa4096.der")).unwrap();

        check_all_algs(&mut [0u8; 512], &private_key, &private_key.public_key());
    }

    #[test]
    fn pairwise_rsa6144_sign_verify() {
        let private_key = SigningKey::from_pkcs1_der(include_bytes!("rsa/rsa6144.der")).unwrap();

        check_all_algs(&mut [0u8; 768], &private_key, &private_key.public_key());
    }

    #[test]
    fn pairwise_rsa8192_sign_verify() {
        let private_key = SigningKey::from_pkcs1_der(include_bytes!("rsa/rsa8192.der")).unwrap();

        check_all_algs(&mut [0u8; 1024], &private_key, &private_key.public_key());
    }

    /// Moduli that are not a whole number of words: 2049 bits makes PSS's
    /// encoded message a byte shorter than the modulus, 2050 bits masks seven
    /// of its top bits, and 2056 bits is a whole number of bytes.
    const ODD_SIZE_KEYS: [&[u8]; 3] = [
        include_bytes!("rsa/rsa2049.pkcs8.der"),
        include_bytes!("rsa/rsa2050.pkcs8.der"),
        include_bytes!("rsa/rsa2056.pkcs8.der"),
    ];

    #[test]
    fn pairwise_odd_size_sign_verify() {
        for der in ODD_SIZE_KEYS {
            let private_key = SigningKey::from_pkcs8_der(der).unwrap();

            check_all_algs(&mut [0u8; 257], &private_key, &private_key.public_key());
        }
    }

    #[test]
    fn pairwise_key_formatting() {
        check_pkcs1(include_bytes!("rsa/rsa2048.der"));
        check_pkcs1(include_bytes!("rsa/rsa3072.der"));
        check_pkcs1(include_bytes!("rsa/rsa4096.der"));
        check_pkcs1(include_bytes!("rsa/rsa6144.der"));
        check_pkcs1(include_bytes!("rsa/rsa8192.der"));

        check_pkcs8(include_bytes!("rsa/rsa2048.pkcs8.der"));
        check_pkcs8(include_bytes!("rsa/rsa2560.pkcs8.der"));
        check_pkcs8(include_bytes!("rsa/rsa3072.pkcs8.der"));
        check_pkcs8(include_bytes!("rsa/rsa4096.pkcs8.der"));
        check_pkcs8(include_bytes!("rsa/rsa6144.pkcs8.der"));
        check_pkcs8(include_bytes!("rsa/rsa8192.pkcs8.der"));
        for der in ODD_SIZE_KEYS {
            check_pkcs8(der);
        }
    }

    fn check_pkcs1(pkcs1_der: &[u8]) {
        let decoded = SigningKey::from_pkcs1_der(pkcs1_der).unwrap();
        let mut buffer = [0u8; SigningKey::MAX_PKCS1_BUFFER_LEN];
        let encoded = decoded.to_pkcs1_der(&mut buffer).unwrap();
        assert_eq!(encoded, pkcs1_der);
        assert_eq!(
            decoded.to_pkcs1_der(&mut buffer[..pkcs1_der.len() - 1]),
            Err(Error::WrongLength)
        );
        let public_key = decoded.public_key();
        assert_eq!(
            public_key.to_pkcs1_der(&mut [0u8; 8]),
            Err(Error::WrongLength)
        );
        assert_eq!(
            public_key.to_spki_der(&mut [0u8; 8]),
            Err(Error::WrongLength)
        );
    }

    fn check_pkcs8(pkcs8_der: &[u8]) {
        let decoded = SigningKey::from_pkcs8_der(pkcs8_der).unwrap();
        let mut buffer = [0u8; SigningKey::MAX_PKCS1_BUFFER_LEN];
        let encoded = decoded.to_pkcs8_der(&mut buffer).unwrap();
        assert_eq!(encoded, pkcs8_der);
        assert_eq!(
            decoded.to_pkcs8_der(&mut buffer[..pkcs8_der.len() - 1]),
            Err(Error::WrongLength)
        );
    }

    /// Every backend makes the same decisions from the same random input,
    /// so generates the same key.
    #[test]
    fn key_generation_known_answer() {
        let candidates = include_str!("../testdata/rsa.bench.2048.txt")
            .split_whitespace()
            .flat_map(|line| hex::decode(line).unwrap())
            .collect::<Vec<_>>();
        let key = SigningKey(
            rsa_priv::RsaPrivateKey::generate(
                RsaKeySize::Rsa2048,
                &mut SliceRandomSource(&candidates),
                &mut HmacDrbg::<hash::Sha256>::new(b"", b"", b""),
            )
            .unwrap(),
        );
        let mut buffer = [0u8; SigningKey::MAX_PKCS1_BUFFER_LEN];
        let der = key.to_pkcs1_der(&mut buffer).unwrap();
        assert_eq!(
            hex::encode(hash::Sha256::hash(der)),
            "5f6fd81f730c06fe0d50c356ec15df941cc89e4ad2289de9b9f2fc27a65148ca"
        );
    }

    /// Given aws-lc-rs's primes, rind derives the same key as aws-lc-rs, with
    /// `d` reduced mod lcm(p - 1, q - 1). The primes are secret, so under
    /// `admin/ctgrind` this also checks Miller-Rabin on them and the
    /// derivation are constant time.
    #[test]
    #[cfg(not(any(miri, target_family = "wasm")))]
    fn key_generation_matches_aws_lc() {
        use aws_lc_rs::encoding::AsDer;
        use aws_lc_rs::rsa::{KeyPair, KeySize};

        // rind sets each candidate's top two bits, so only primes with both
        // set come out unchanged.
        let theirs = core::iter::repeat_with(|| {
            let pkcs8 = KeyPair::generate(KeySize::Rsa2048)
                .unwrap()
                .as_der()
                .unwrap();
            let key = SigningKey::from_pkcs8_der(pkcs8.as_ref()).unwrap();
            let mut buffer = [0u8; SigningKey::MAX_PKCS1_BUFFER_LEN];
            key.to_pkcs1_der(&mut buffer).unwrap().to_vec()
        })
        .find(|der| {
            let key = Pkcs1::decode(der);
            key.p[0] >= 0xc0 && key.q[0] >= 0xc0
        })
        .unwrap();

        let key = Pkcs1::decode(&theirs);
        let ours = SigningKey(
            rsa_priv::RsaPrivateKey::generate(
                RsaKeySize::Rsa2048,
                &mut SliceRandomSource(&[key.p, key.q].concat()),
                &mut HmacDrbg::<hash::Sha256>::new(b"", b"", b""),
            )
            .unwrap(),
        );
        let mut buffer = [0u8; SigningKey::MAX_PKCS1_BUFFER_LEN];
        assert_eq!(ours.to_pkcs1_der(&mut buffer).unwrap(), &theirs[..]);
    }

    /// A PKCS#1 private key's integers, as big-endian magnitudes.
    #[derive(Clone)]
    struct Pkcs1 {
        n: Vec<u8>,
        e: Vec<u8>,
        d: Vec<u8>,
        p: Vec<u8>,
        q: Vec<u8>,
        dp: Vec<u8>,
        dq: Vec<u8>,
        iqmp: Vec<u8>,
    }

    impl Pkcs1 {
        fn decode(der: &[u8]) -> Self {
            let k = pkix::RSAPrivateKey::from_bytes(der).unwrap();
            let int = |i: asn1::Integer<'_>| trim(i.as_ref()).to_vec();
            Self {
                n: int(k.modulus),
                e: int(k.publicExponent),
                d: int(k.privateExponent),
                p: int(k.prime1),
                q: int(k.prime2),
                dp: int(k.exponent1),
                dq: int(k.exponent2),
                iqmp: int(k.coefficient),
            }
        }

        fn encode(&self) -> Vec<u8> {
            let signed = |x: &[u8]| [&[0][..], x].concat();
            let ints = [
                &self.n, &self.e, &self.d, &self.p, &self.q, &self.dp, &self.dq, &self.iqmp,
            ]
            .map(|x| signed(x));
            let [n, e, d, p, q, dp, dq, iqmp] = ints.each_ref().map(|x| asn1::Integer::new(x));
            let mut out = vec![0u8; 8192];
            let len = pkix::RSAPrivateKey {
                version: pkix::Version::two_prime,
                modulus: n,
                publicExponent: e,
                privateExponent: d,
                prime1: p,
                prime2: q,
                exponent1: dp,
                exponent2: dq,
                coefficient: iqmp,
            }
            .encode(&mut asn1::Encoder::new(&mut out))
            .unwrap();
            out.truncate(len);
            out
        }
    }

    fn trim(x: &[u8]) -> &[u8] {
        let start = x.iter().position(|b| *b != 0).unwrap_or(x.len());
        &x[start..]
    }

    /// `a + b`, or `a - b` if `negate`, big-endian.
    fn add_sub(a: &[u8], b: &[u8], negate: bool) -> Vec<u8> {
        let len = a.len().max(b.len()) + 1;
        let at = |x: &[u8], i: usize| x.len().checked_sub(i + 1).map_or(0, |j| i32::from(x[j]));
        let mut out = vec![0u8; len];
        let mut carry = 0;
        for i in 0..len {
            let b = if negate { -at(b, i) } else { at(b, i) };
            let sum = at(a, i) + b + carry;
            out[len - 1 - i] = sum.rem_euclid(256) as u8;
            carry = sum.div_euclid(256);
        }
        assert_eq!(carry, 0);
        trim(&out).to_vec()
    }

    fn add(a: &[u8], b: &[u8]) -> Vec<u8> {
        add_sub(a, b, false)
    }

    fn sub(a: &[u8], b: &[u8]) -> Vec<u8> {
        add_sub(a, b, true)
    }

    /// `a * b`, big-endian.
    fn mul(a: &[u8], b: &[u8]) -> Vec<u8> {
        let mut out = vec![0u8; a.len() + b.len()];
        for (i, x) in a.iter().rev().enumerate() {
            let mut carry = 0;
            for (j, y) in b.iter().rev().enumerate() {
                let at = out.len() - 1 - i - j;
                let sum = u32::from(out[at]) + u32::from(*x) * u32::from(*y) + carry;
                out[at] = sum as u8;
                carry = sum >> 8;
            }
            out[a.len() - 1 - i] = carry as u8;
        }
        trim(&out).to_vec()
    }

    /// Each key breaks one relation between its components, which rind and
    /// aws-lc-rs both refuse. Those that stay congruent but are unreduced
    /// are caught only by a range check.
    #[test]
    fn refuses_mismatched_private_key() {
        let key = Pkcs1::decode(include_bytes!("rsa/rsa2048.der"));
        let p_1 = sub(&key.p, &[1]);
        let q_1 = sub(&key.q, &[1]);
        let mutants = [
            (
                "n + 2",
                Pkcs1 {
                    n: add(&key.n, &[2]),
                    ..key.clone()
                },
            ),
            (
                "e = 3",
                Pkcs1 {
                    e: vec![3],
                    ..key.clone()
                },
            ),
            (
                "d + 2",
                Pkcs1 {
                    d: add(&key.d, &[2]),
                    ..key.clone()
                },
            ),
            // Still right mod p - 1, so only the check mod q - 1 refuses it.
            (
                "d + p - 1",
                Pkcs1 {
                    d: add(&key.d, &p_1),
                    ..key.clone()
                },
            ),
            (
                "d + q - 1",
                Pkcs1 {
                    d: add(&key.d, &q_1),
                    ..key.clone()
                },
            ),
            (
                "dp + 2",
                Pkcs1 {
                    dp: add(&key.dp, &[2]),
                    ..key.clone()
                },
            ),
            (
                "dp - 2",
                Pkcs1 {
                    dp: sub(&key.dp, &[2]),
                    ..key.clone()
                },
            ),
            (
                "dp + p - 1",
                Pkcs1 {
                    dp: add(&key.dp, &p_1),
                    ..key.clone()
                },
            ),
            (
                "dq + q - 1",
                Pkcs1 {
                    dq: add(&key.dq, &q_1),
                    ..key.clone()
                },
            ),
            (
                "dp = 0",
                Pkcs1 {
                    dp: vec![],
                    ..key.clone()
                },
            ),
            (
                "iqmp + 1",
                Pkcs1 {
                    iqmp: add(&key.iqmp, &[1]),
                    ..key.clone()
                },
            ),
            (
                "iqmp + p",
                Pkcs1 {
                    iqmp: add(&key.iqmp, &key.p),
                    ..key.clone()
                },
            ),
            (
                "iqmp = 0",
                Pkcs1 {
                    iqmp: vec![],
                    ..key.clone()
                },
            ),
            // Swapping the primes with their exponents leaves only iqmp wrong.
            (
                "p and q swapped",
                Pkcs1 {
                    p: key.q.clone(),
                    q: key.p.clone(),
                    dp: key.dq.clone(),
                    dq: key.dp.clone(),
                    ..key.clone()
                },
            ),
            (
                "n from another key",
                Pkcs1 {
                    n: Pkcs1::decode(include_bytes!("rsa/rsa3072.der")).n,
                    ..key.clone()
                },
            ),
        ];

        for (name, mutant) in mutants {
            let der = mutant.encode();
            assert!(
                matches!(SigningKey::from_pkcs1_der(&der), Err(Error::KeyRejected(_))),
                "{name}"
            );
            #[cfg(not(any(miri, target_family = "wasm")))]
            assert!(aws_lc_rs::rsa::KeyPair::from_der(&der).is_err(), "{name}");
        }

        // d + (p - 1)(q - 1) still inverts e mod p - 1 and q - 1, which is
        // all d must do.
        let phi = sub(&add(&key.n, &[1]), &add(&key.p, &key.q));
        let der = Pkcs1 {
            d: add(&key.d, &phi),
            ..key.clone()
        }
        .encode();
        #[cfg(not(any(miri, target_family = "wasm")))]
        aws_lc_rs::rsa::KeyPair::from_der(&der).unwrap();
        let private_key = SigningKey::from_pkcs1_der(&der).unwrap();
        check_all_algs(&mut [0u8; 256], &private_key, &private_key.public_key());
    }

    /// A signature from a faulted CRT would reveal a prime, so it is
    /// refused rather than returned.
    #[test]
    fn refuses_a_faulty_signature() {
        let mut key = SigningKey::from_pkcs1_der(include_bytes!("rsa/rsa2048.der")).unwrap();
        key.0.swap_crt_exponents();
        assert_eq!(
            key.sign_pkcs1_sha256(&mut [0u8; 256], b"message").err(),
            Some(Error::Fault)
        );
    }

    /// PKCS#1 does not order the primes, and aws-lc-rs loads either order.
    #[test]
    fn loads_q_above_p() {
        let der = include_bytes!("rsa/rsa2048-q-above-p.der");
        let key = Pkcs1::decode(der);
        assert!(key.q.len() == key.p.len() && key.q > key.p);
        #[cfg(not(any(miri, target_family = "wasm")))]
        aws_lc_rs::rsa::KeyPair::from_der(der).unwrap();
        let private_key = SigningKey::from_pkcs1_der(der).unwrap();
        check_all_algs(&mut [0u8; 256], &private_key, &private_key.public_key());
    }

    /// Primes of 1028 and 1058 bits: both fill 17 words, but only q's top
    /// 32 bits are nonzero, so q is wider than p's 32-bit width.
    #[test]
    fn loads_unbalanced_primes() {
        let der = include_bytes!("rsa/rsa2086-unbalanced.der");
        let key = Pkcs1::decode(der);
        assert!(key.q.len() > key.p.len());
        #[cfg(not(any(miri, target_family = "wasm")))]
        aws_lc_rs::rsa::KeyPair::from_der(der).unwrap();
        let private_key = SigningKey::from_pkcs1_der(der).unwrap();
        check_all_algs(&mut [0u8; 261], &private_key, &private_key.public_key());
    }

    /// With q above p, `s mod q` can exceed `p + s mod p`, which a random
    /// message reaches about once in a thousand signatures with this key.
    /// `s = q * iqmp - 1` is 0 mod p and q - 1 mod q, the widest gap.
    #[test]
    fn signs_with_crt_half_above_p() {
        let der = include_bytes!("rsa/rsa2048-q-above-p.der");
        let key = Pkcs1::decode(der);
        let private_key = SigningKey::from_pkcs1_der(der).unwrap();
        let s = sub(&mul(&key.q, &key.iqmp), &[1]);
        let m = PosInt::from_bytes(&s).unwrap();
        let m = private_key.0.public_key().public_op(m).unwrap();
        let signature = ct::into_public(private_key.0.private_op(&m).unwrap());
        assert_eq!(trim(i2osp(&signature, &mut [0u8; 256]).unwrap()), s);
    }

    /// rind generated `d` mod (p - 1)(q - 1) before it reduced `d` mod
    /// lcm(p - 1, q - 1), so a `d` above the lcm still loads, as in
    /// aws-lc-rs.
    #[test]
    fn loads_d_above_lcm() {
        let key = Pkcs1::decode(include_bytes!("rsa/rsa2048.der"));
        // This key's p - 1 and q - 1 share only a factor of two, so their
        // lcm is (p - 1)(q - 1) / 2 = (n - p - q + 1) / 2.
        let phi = sub(&add(&key.n, &[1]), &add(&key.p, &key.q));
        let mut carry = 0;
        let lcm = phi
            .iter()
            .map(|b| {
                let half = (carry << 7) | (b >> 1);
                carry = b & 1;
                half
            })
            .collect::<Vec<_>>();
        let der = Pkcs1 {
            d: add(&key.d, &lcm),
            ..key
        }
        .encode();
        #[cfg(not(any(miri, target_family = "wasm")))]
        aws_lc_rs::rsa::KeyPair::from_der(&der).unwrap();
        let private_key = SigningKey::from_pkcs1_der(&der).unwrap();
        check_all_algs(&mut [0u8; 256], &private_key, &private_key.public_key());
    }

    /// e must be odd, above one, and at most 33 bits, as in aws-lc-rs, for
    /// public keys as components or DER, and for private keys.
    #[test]
    fn refuses_even_unit_or_wide_exponent() {
        let key = Pkcs1::decode(include_bytes!("rsa/rsa2048.der"));
        let n = [&[0][..], &key.n].concat();
        for (e, ok) in [
            (&[1][..], false),
            (&[2], false),
            (&[4], false),
            (&[1, 0, 0], false),
            (&[3], true),
            (&[1, 0, 1], true),
            (&[0x80, 0, 0, 1], true),
            (&[1, 0, 0, 0, 1], true),
            (&[1, 0xff, 0xff, 0xff, 0xff], true),
            (&[2, 0, 0, 0, 1], false),
            // Too wide for a `u64`, where a wrapping read would give 3.
            (&[1, 0, 0, 0, 0, 0, 0, 0, 3], false),
        ] {
            let mut der = [0u8; 512];
            let len = pkix::RSAPublicKey {
                modulus: asn1::Integer::new(&n),
                publicExponent: asn1::Integer::new(&[&[0][..], e].concat()),
            }
            .encode(&mut asn1::Encoder::new(&mut der))
            .unwrap();
            let der = &der[..len];
            let want = match ok {
                true => Ok(()),
                false => Err(KeyFormatError::RsaExponent.into()),
            };
            match VerifyingKey::from_pkcs1_der(der) {
                // It encodes as it was read, whatever its top bit.
                Ok(key) => assert_eq!(key.to_pkcs1_der(&mut [0; 512]), Ok(der), "{e:?}"),
                Err(err) => assert_eq!(Err(err), want, "{e:?}"),
            }
            assert_eq!(
                VerifyingKey::from_components(&key.n, e).map(|_| ()),
                want,
                "{e:?}"
            );

            // Only the original exponent agrees with d.
            let der = Pkcs1 {
                e: e.to_vec(),
                ..key.clone()
            }
            .encode();
            let ours = SigningKey::from_pkcs1_der(&der).map(|_| ()).err();
            #[cfg(not(any(miri, target_family = "wasm")))]
            assert!(
                aws_lc_rs::rsa::KeyPair::from_der(&der).is_ok() == (e == [1, 0, 1]),
                "{e:?}"
            );
            match e {
                [1, 0, 1] => assert_eq!(ours, None),
                _ if ok => assert_eq!(ours, Some(KeyFormatError::MismatchedRsaComponents.into())),
                _ => assert_eq!(ours, Some(KeyFormatError::RsaExponent.into()), "{e:?}"),
            }
        }

        // A negative exponent, whose bytes alone would read as 129.
        let mut der = [0u8; 512];
        let len = pkix::RSAPublicKey {
            modulus: asn1::Integer::new(&n),
            publicExponent: asn1::Integer::new(&[0x81]),
        }
        .encode(&mut asn1::Encoder::new(&mut der))
        .unwrap();
        assert_eq!(
            VerifyingKey::from_pkcs1_der(&der[..len]).map(|_| ()),
            Err(KeyFormatError::RsaExponent.into())
        );

        // With e = 1 a signature is its own encoded message, so anyone could
        // forge one.
        let mut em = [0u8; 256];
        pkcs1::encode_pkcs1_sig(
            &mut em,
            pkcs1::DIGESTINFO_SHA256,
            hash::Sha256::hash(b"hello").as_ref(),
        );
        #[cfg(not(any(miri, target_family = "wasm")))]
        assert!(
            aws_lc_rs::signature::RsaPublicKeyComponents {
                n: &key.n[..],
                e: &[1][..]
            }
            .verify(
                &aws_lc_rs::signature::RSA_PKCS1_2048_8192_SHA256,
                b"hello",
                &em
            )
            .is_err()
        );
    }
}
