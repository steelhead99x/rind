// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use super::asn1::{self, Type, pkix};
use super::hash::{Hash, HashContext, Sha384};
use super::rsa::{self, PssSalt};
use super::signature::{Buffer, Pkcs8, PublicKeyComponents, RSA_MIN_BITS, Spki};
use crate::error::{Error, KeyFormatError};
use crate::low;
use crate::mid::rng::{RandomSource, SystemRandom};
use crate::mid::rsa_key_size::RsaKeySize;
use crate::mid::rsa_pub::MAX_PUBLIC_MODULUS_BYTES;

/// The length of a Randomized variant's message prefix.
const PREFIX_LEN: usize = 32;

/// SHA-384's output length.
const HASH_LEN: usize = 48;

/// An RFC 9474 RSABSSA variant: SHA-384, MGF1 with SHA-384, a salt of 48
/// bytes or none, and Randomized or Deterministic message preparation.
pub struct Algorithm {
    name: &'static str,
    salt: PssSalt,
    randomized: bool,
    /// The body of the key's `id-RSASSA-PSS` `AlgorithmIdentifier`, as
    /// RFC 9578 encodes it.
    algorithm_id: &'static [u8],
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name)
    }
}

/// `id-RSASSA-PSS` with `RSASSA-PSS-params` naming SHA-384, MGF1 with
/// SHA-384, and the salt length `SALT`, each present.
const fn pss_sha384_algorithm_id<const SALT: u8>() -> [u8; 61] {
    let mut id = *b"\x06\x09\x2a\x86\x48\x86\xf7\x0d\x01\x01\x0a\
        \x30\x30\
        \xa0\x0d\x30\x0b\x06\x09\x60\x86\x48\x01\x65\x03\x04\x02\x02\
        \xa1\x1a\x30\x18\x06\x09\x2a\x86\x48\x86\xf7\x0d\x01\x01\x08\
        \x30\x0b\x06\x09\x60\x86\x48\x01\x65\x03\x04\x02\x02\
        \xa2\x03\x02\x01\x00";
    id[60] = SALT;
    id
}

static PSS_ALGORITHM_ID: [u8; 61] = pss_sha384_algorithm_id::<{ HASH_LEN as u8 }>();
static PSSZERO_ALGORITHM_ID: [u8; 61] = pss_sha384_algorithm_id::<0>();

/// RSABSSA-SHA384-PSS-Randomized: a 48-byte salt, and a random prefix on
/// each message. RFC 9474 recommends it, or the PSSZERO variant, wherever a
/// message may be guessable.
pub static RSABSSA_SHA384_PSS_RANDOMIZED: Algorithm = Algorithm {
    name: "RSABSSA-SHA384-PSS-Randomized",
    salt: PssSalt::Hash,
    randomized: true,
    algorithm_id: &PSS_ALGORITHM_ID,
};

/// RSABSSA-SHA384-PSSZERO-Randomized: no salt, and a random prefix on each
/// message.
pub static RSABSSA_SHA384_PSSZERO_RANDOMIZED: Algorithm = Algorithm {
    name: "RSABSSA-SHA384-PSSZERO-Randomized",
    salt: PssSalt::Len(0),
    randomized: true,
    algorithm_id: &PSSZERO_ALGORITHM_ID,
};

/// RSABSSA-SHA384-PSS-Deterministic: a 48-byte salt, and the message as
/// given, which must be unguessable to the signer. Privacy Pass's publicly
/// verifiable tokens (RFC 9578, type `0x0002`) use it.
pub static RSABSSA_SHA384_PSS_DETERMINISTIC: Algorithm = Algorithm {
    name: "RSABSSA-SHA384-PSS-Deterministic",
    salt: PssSalt::Hash,
    randomized: false,
    algorithm_id: &PSS_ALGORITHM_ID,
};

/// RSABSSA-SHA384-PSSZERO-Deterministic: no salt, and the message as given,
/// which must be unguessable to the signer, so each message has one
/// signature.
pub static RSABSSA_SHA384_PSSZERO_DETERMINISTIC: Algorithm = Algorithm {
    name: "RSABSSA-SHA384-PSSZERO-Deterministic",
    salt: PssSalt::Len(0),
    randomized: false,
    algorithm_id: &PSSZERO_ALGORITHM_ID,
};

impl Algorithm {
    /// The SHA-384 digest of the message as this algorithm signs it:
    /// after `prefix` for a Randomized variant.
    fn digest(&self, prefix: &[u8; PREFIX_LEN], message: &[u8]) -> [u8; HASH_LEN] {
        let mut context = Sha384::new();
        if self.randomized {
            context.update(prefix);
        }
        context.update(message);
        let mut digest = [0; HASH_LEN];
        digest.copy_from_slice(context.finish().as_ref());
        digest
    }

    fn prefix_len(&self) -> usize {
        match self.randomized {
            true => PREFIX_LEN,
            false => 0,
        }
    }
}

/// A server's two-prime RSA private key, with a modulus of 2048 to 8192
/// bits, bound to the one RSABSSA variant it signs blinded messages for.
///
/// It signs whatever it is given, so it must serve no other protocol and
/// no other variant, as RFC 9474 requires.
pub struct KeyPair {
    key: rsa::SigningKey,
    algorithm: AlgorithmRef,
}

/// The key's algorithm, aligned as `DecryptingKey`'s is, so its drop wipes
/// any padding `KeyPair` needs.
#[derive(Clone, Copy)]
struct AlgorithmRef(low::ZeroableRef<Algorithm>, [u64; 0]);

impl low::Zeroable for AlgorithmRef {}

impl KeyPair {
    /// Generates a key of `size` for `algorithm` from the system random
    /// source.
    ///
    /// This is slow: about 30 milliseconds for 2048 bits, and 15 seconds or
    /// more for 8192 bits, with no upper bound. Its timing reveals only which
    /// candidate primes it discards.
    pub fn generate(algorithm: &'static Algorithm, size: RsaKeySize) -> Result<Self, Error> {
        Ok(Self::new(algorithm, rsa::SigningKey::generate(size)?))
    }

    /// Loads a PKCS#8 v1 RSA private key for `algorithm`, named
    /// `rsaEncryption`, `id-RSAES-OAEP`, or `id-ea-rsa`.
    pub fn from_pkcs8(algorithm: &'static Algorithm, der: &[u8]) -> Result<Self, Error> {
        Ok(Self::new(algorithm, rsa::SigningKey::from_pkcs8_der(der)?))
    }

    fn new(algorithm: &'static Algorithm, key: rsa::SigningKey) -> Self {
        Self {
            key,
            algorithm: AlgorithmRef(low::ZeroableRef::new(algorithm), []),
        }
    }

    fn algorithm(&self) -> &'static Algorithm {
        self.algorithm.0.get()
    }

    /// Returns the public key, which clients blind messages to.
    pub fn public_key(&self) -> PublicKey {
        // A private key's modulus is at least 2048 bits.
        PublicKey {
            key: self.key.public_key(),
            algorithm: self.algorithm(),
        }
    }

    /// Signs a client's blinded message, which must be as long as the
    /// modulus and below it, or this fails with [`Error::WrongLength`].
    ///
    /// The signer learns nothing of the message, so each call is worth one
    /// signature to the client: limit them as the protocol requires.
    pub fn blind_sign(&self, blinded_message: &[u8]) -> Result<BlindSignature, Error> {
        Buffer::write(|output| self.key.blind_sign(output, blinded_message)).map(BlindSignature)
    }

    /// Encodes the private key as PKCS#8, naming `rsaEncryption`.
    pub fn to_pkcs8(&self) -> Pkcs8 {
        Pkcs8(Buffer::encode(|output| self.key.to_pkcs8_der(output)))
    }
}

impl fmt::Debug for KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KeyPair")
            .field("algorithm", self.algorithm())
            .finish_non_exhaustive()
    }
}

impl Drop for KeyPair {
    fn drop(&mut self) {
        // The private key wipes itself. Wiping this, which is not secret,
        // lets `tests/zeroing.rs` check every byte.
        low::zeroise_value(&mut self.algorithm);
    }
}

/// A server's RSA public key, with a modulus of 2048 to 8192 bits, bound to
/// one RSABSSA variant: clients blind messages to it, and anyone verifies
/// the signatures they finalize.
#[derive(Clone)]
pub struct PublicKey {
    key: rsa::VerifyingKey,
    algorithm: &'static Algorithm,
}

impl PublicKey {
    /// Parses a `SubjectPublicKeyInfo` naming `id-RSASSA-PSS`, whose
    /// parameters must name `algorithm`'s hash, mask, and salt length, as
    /// RFC 9578 requires of Privacy Pass issuers' keys.
    ///
    /// RFC 9474 forbids `rsaEncryption` for these keys, so it is refused.
    pub fn new(algorithm: &'static Algorithm, spki: &[u8]) -> Result<Self, Error> {
        let _entry = low::Entry::new_public();
        let spki =
            pkix::FixedAlgorithmPublicKeyInfo::from_bytes(spki).map_err(KeyFormatError::Asn1)?;
        if spki.algorithm.body() != algorithm.algorithm_id {
            return Err(KeyFormatError::MismatchedSpkiAlgorithm.into());
        }
        let key = rsa::VerifyingKey::from_pkcs1_der(spki.subjectPublicKey.as_octets())?;
        Self::checked(algorithm, key)
    }

    /// Loads a key for `algorithm` from its big-endian modulus and exponent.
    pub fn from_components(
        algorithm: &'static Algorithm,
        components: &PublicKeyComponents<impl AsRef<[u8]>>,
    ) -> Result<Self, Error> {
        Self::checked(
            algorithm,
            rsa::VerifyingKey::from_components(components.n.as_ref(), components.e.as_ref())?,
        )
    }

    /// Refuses a key below 2048 bits, which [`rsa::VerifyingKey`] takes for
    /// legacy verification.
    fn checked(algorithm: &'static Algorithm, key: rsa::VerifyingKey) -> Result<Self, Error> {
        match key.modulus_len_bits() >= RSA_MIN_BITS {
            true => Ok(Self { key, algorithm }),
            false => Err(KeyFormatError::RsaModulus.into()),
        }
    }

    /// Blinds `message` for the server to sign, returning the blinded
    /// message to send it and the [`Blinding`] that finalizes its reply.
    ///
    /// Fails with a [`KeyRejected`](crate::KeyRejected) error if the key
    /// shares a factor with the encoded message, which only a key made to
    /// attack its clients does more than negligibly often.
    pub fn blind(&self, message: &[u8]) -> Result<(BlindedMessage, Blinding), Error> {
        self.blind_with(message, &mut SystemRandom)
    }

    fn blind_with(
        &self,
        message: &[u8],
        rng: &mut dyn RandomSource,
    ) -> Result<(BlindedMessage, Blinding), Error> {
        let _entry = low::Entry::new_secret();
        let mut prefix = [0; PREFIX_LEN];
        rng.fill(&mut prefix[..self.algorithm.prefix_len()])?;
        let digest = self.algorithm.digest(&prefix, message);

        let mut unblinder = None;
        let blinded = Buffer::write(|output| {
            let (blinded, inverse) =
                self.key
                    .blind_pss::<Sha384>(self.algorithm.salt, &digest, rng, output)?;
            unblinder = Some(inverse);
            Ok(blinded)
        })?;
        let blinding = Blinding {
            key: self.clone(),
            unblinder: unblinder.expect("set by a successful blind"),
            prefix,
        };
        Ok((BlindedMessage(blinded), blinding))
    }

    /// Verifies a signature of `message`, as [`Blinding::finalize`] returns
    /// it: for a Randomized variant, its message prefix, then the RSASSA-PSS
    /// signature.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        let _entry = low::Entry::new_public();
        let Some((prefix, signature)) = signature.split_at_checked(self.algorithm.prefix_len())
        else {
            return Err(Error::BadSignature);
        };
        let mut padded = [0; PREFIX_LEN];
        padded[..prefix.len()].copy_from_slice(prefix);
        let digest = self.algorithm.digest(&padded, message);
        self.key
            .verify_pss_digest::<Sha384>(Some(self.algorithm.salt), signature, &digest)
    }

    /// Encodes the key as a `SubjectPublicKeyInfo` naming `id-RSASSA-PSS`
    /// with the algorithm's parameters, as RFC 9578 does: Privacy Pass's
    /// `token_key_id` is its SHA-256 digest.
    pub fn to_spki(&self) -> Spki {
        Spki(Buffer::encode(|output| {
            let mut pkcs1 = [0; rsa::MAX_PUBLIC_KEY_LEN];
            let pkcs1 = self.key.to_pkcs1_der(&mut pkcs1)?;
            let len = pkix::FixedAlgorithmPublicKeyInfo {
                algorithm: asn1::Sequence::new(self.algorithm.algorithm_id),
                subjectPublicKey: asn1::BitString::new(pkcs1),
            }
            .encode(&mut asn1::Encoder::new(output))
            .map_err(|_| Error::WrongLength)?;
            Ok(&output[..len])
        }))
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PublicKey")
            .field("algorithm", self.algorithm)
            .field("bits", &self.key.modulus_len_bits())
            .finish()
    }
}

/// A client's secret for one blinded message, which turns the server's
/// [`BlindSignature`] into a signature of the message.
pub struct Blinding {
    key: PublicKey,
    unblinder: rsa::Unblinder,
    prefix: [u8; PREFIX_LEN],
}

impl Blinding {
    /// Unblinds the server's reply into a signature of the blinded
    /// message, checked to be one in constant time, so a malicious reply
    /// learns nothing of the blind.
    ///
    /// For a Randomized variant, the signature begins with the message's
    /// random prefix, which [`PublicKey::verify`] reads.
    ///
    /// A reply that does not unblind to a valid signature fails with
    /// [`Error::BadSignature`].
    pub fn finalize(self, blind_signature: &[u8]) -> Result<Signature, Error> {
        let algorithm = self.key.algorithm;
        let prefix_len = algorithm.prefix_len();
        Buffer::write(|output| {
            let (prefix, rest) = output.split_at_mut(prefix_len);
            let len = prefix_len
                + (self.key.key)
                    .finalize(&self.unblinder, blind_signature, rest)?
                    .len();
            // The prefix is revealed with the signature it begins.
            prefix.copy_from_slice(&self.prefix[..prefix_len]);
            low::ct::public_slice(prefix);
            Ok(&output[..len])
        })
        .map(Signature)
    }
}

impl fmt::Debug for Blinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Blinding")
            .field("algorithm", self.key.algorithm)
            .finish_non_exhaustive()
    }
}

/// A blinded message, as long as the modulus, for the server to sign.
#[derive(Clone)]
pub struct BlindedMessage(Buffer<MAX_PUBLIC_MODULUS_BYTES>);

/// The server's signature of a blinded message, as long as the modulus.
#[derive(Clone)]
pub struct BlindSignature(Buffer<MAX_PUBLIC_MODULUS_BYTES>);

/// A finalized signature: for a Randomized variant, the message's 32-byte
/// random prefix, then the RSASSA-PSS signature, as long as the modulus.
#[derive(Clone)]
pub struct Signature(Buffer<{ PREFIX_LEN + MAX_PUBLIC_MODULUS_BYTES }>);

macro_rules! bytes {
    ($($name:ident),+) => {$(
        impl AsRef<[u8]> for $name {
            fn as_ref(&self) -> &[u8] {
                self.0.as_ref()
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_tuple(stringify!($name)).field(&self.as_ref()).finish()
            }
        }
    )+};
}

bytes!(BlindedMessage, BlindSignature, Signature);

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::high::hash::Sha256;
    use crate::low::{PosInt, ct};
    use crate::mid::rng::SliceRandomSource;

    const ALGORITHMS: [&Algorithm; 4] = [
        &RSABSSA_SHA384_PSS_RANDOMIZED,
        &RSABSSA_SHA384_PSSZERO_RANDOMIZED,
        &RSABSSA_SHA384_PSS_DETERMINISTIC,
        &RSABSSA_SHA384_PSSZERO_DETERMINISTIC,
    ];

    /// Keys whose modulus fills a whole number of words, or not, or bytes:
    /// at 2049 bits the encoded message is a byte shorter than the modulus.
    const KEYS: [&[u8]; 3] = [
        include_bytes!("rsa/rsa2048.pkcs8.der"),
        include_bytes!("rsa/rsa2049.pkcs8.der"),
        include_bytes!("rsa/rsa4096.pkcs8.der"),
    ];

    fn salt_len(algorithm: &Algorithm) -> usize {
        match algorithm.salt {
            PssSalt::Hash => HASH_LEN,
            _ => 0,
        }
    }

    fn hex(value: &serde_json::Value) -> Vec<u8> {
        let hex = value.as_str().unwrap();
        let hex = hex.strip_prefix("0x").unwrap_or(hex);
        let pad = if hex.len() % 2 == 1 { "0" } else { "" };
        ::hex::decode(format!("{pad}{hex}")).unwrap()
    }

    /// `r` from its inverse `inv` mod `n`, as long as `n`.
    fn blind_from_inverse(n: &[u8], inv: &[u8]) -> Vec<u8> {
        type Int = PosInt<{ MAX_PUBLIC_MODULUS_BYTES / 8 }>;
        let n_int = Int::from_bytes(n).unwrap();
        let r = Int::from_bytes(inv).unwrap().mod_inverse(&n_int);
        let mut out = vec![0; MAX_PUBLIC_MODULUS_BYTES];
        let r = r.to_bytes(&mut out).unwrap();
        r[r.len() - n.len()..].to_vec()
    }

    /// Every step of each of RFC 9474's Appendix A vectors, whose randomness
    /// is fed in the order the RFC draws it: the message prefix, the salt,
    /// then the blind.
    #[test]
    fn rfc9474_vectors() {
        let path = format!(
            "{}/../thirdparty/vectors/rfc9474/test-vectors.json",
            env!("CARGO_MANIFEST_DIR")
        );
        let vectors: Vec<serde_json::Value> =
            serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap();
        assert_eq!(vectors.len(), 4);
        for vector in vectors {
            let name = vector["name"].as_str().unwrap();
            let algorithm = *ALGORITHMS.iter().find(|a| a.name == name).unwrap();
            assert_eq!(hex(&vector["is_randomized"]) == [1], algorithm.randomized);
            assert_eq!(hex(&vector["sLen"]), [salt_len(algorithm) as u8]);

            let n = hex(&vector["n"]);
            let key_pair = KeyPair::new(
                algorithm,
                rsa::SigningKey::from_primes(
                    RsaKeySize::Rsa4096,
                    &hex(&vector["p"]),
                    &hex(&vector["q"]),
                ),
            );
            let public_key = PublicKey::from_components(
                algorithm,
                &PublicKeyComponents {
                    n: &n,
                    e: &hex(&vector["e"]),
                },
            )
            .unwrap();
            assert_eq!(
                public_key.to_spki().as_ref(),
                key_pair.public_key().to_spki().as_ref()
            );

            let message = hex(&vector["msg"]);
            let prefix = hex(&vector["msg_prefix"]);
            let random = [
                &prefix[..],
                &hex(&vector["salt"]),
                &blind_from_inverse(&n, &hex(&vector["inv"])),
            ]
            .concat();
            let (blinded, blinding) = public_key
                .blind_with(&message, &mut SliceRandomSource(&random))
                .unwrap();
            assert_eq!(blinded.as_ref(), hex(&vector["blinded_msg"]));

            let blind_signature = key_pair.blind_sign(blinded.as_ref()).unwrap();
            assert_eq!(blind_signature.as_ref(), hex(&vector["blind_sig"]));

            let signature = blinding.finalize(blind_signature.as_ref()).unwrap();
            assert_eq!(
                signature.as_ref(),
                [&prefix[..], &hex(&vector["sig"])].concat()
            );
            public_key.verify(&message, signature.as_ref()).unwrap();
        }
    }

    /// RFC 9578's first publicly verifiable token vector (type `0x0002`):
    /// the issuer's key encodings, the token request and response, and the
    /// token, whose authenticator signs the fields before it.
    #[test]
    fn rfc9578_token() {
        let vector: serde_json::Value =
            serde_json::from_str(include_str!("rsa/rfc9578.json")).unwrap();
        let algorithm = &RSABSSA_SHA384_PSS_DETERMINISTIC;
        let key_pair =
            KeyPair::from_pkcs8(algorithm, include_bytes!("rsa/rfc9578.pkcs8.der")).unwrap();
        let spki = hex(&vector["pkI"]);
        assert_eq!(key_pair.public_key().to_spki().as_ref(), spki);
        let public_key = PublicKey::new(algorithm, &spki).unwrap();

        let token = hex(&vector["token"]);
        let (token_input, authenticator) = token.split_at(2 + 32 + 32 + 32);
        let token_key_id = &token_input[66..];
        assert_eq!(Sha256::hash(&spki).as_ref(), token_key_id);

        let request = hex(&vector["token_request"]);
        assert_eq!(request[..3], [0, 2, token_key_id[31]]);
        let random = [&hex(&vector["salt"])[..], &hex(&vector["blind"])].concat();
        let (blinded, blinding) = public_key
            .blind_with(token_input, &mut SliceRandomSource(&random))
            .unwrap();
        assert_eq!(blinded.as_ref(), &request[3..]);

        let response = key_pair.blind_sign(blinded.as_ref()).unwrap();
        assert_eq!(response.as_ref(), hex(&vector["token_response"]));
        let signature = blinding.finalize(response.as_ref()).unwrap();
        assert_eq!(signature.as_ref(), authenticator);
        public_key.verify(token_input, authenticator).unwrap();
    }

    #[test]
    fn round_trip() {
        for der in KEYS {
            for algorithm in ALGORITHMS {
                let key_pair = KeyPair::from_pkcs8(algorithm, der).unwrap();
                let spki = key_pair.public_key().to_spki();
                let public_key = PublicKey::new(algorithm, spki.as_ref()).unwrap();
                assert_eq!(public_key.to_spki().as_ref(), spki.as_ref());

                for message in [&b""[..], b"hello", &[0xa5; 300]] {
                    let (blinded, blinding) = public_key.blind(message).unwrap();
                    let blind_signature = key_pair.blind_sign(blinded.as_ref()).unwrap();
                    let signature = blinding.finalize(blind_signature.as_ref()).unwrap();
                    let modulus_len = blinded.as_ref().len();
                    assert_eq!(
                        signature.as_ref().len(),
                        algorithm.prefix_len() + modulus_len
                    );
                    public_key.verify(message, signature.as_ref()).unwrap();
                    assert_eq!(
                        public_key.verify(b"other", signature.as_ref()),
                        Err(Error::BadSignature)
                    );
                }
            }
        }
    }

    /// A signature verifies only for its own variant, and a Randomized one
    /// only with its prefix, not over the message the prefix was put on.
    #[test]
    fn signatures_are_bound_to_their_variant() {
        let der = KEYS[0];
        for signer in ALGORITHMS {
            let key_pair = KeyPair::from_pkcs8(signer, der).unwrap();
            let public_key = key_pair.public_key();
            let (blinded, blinding) = public_key.blind(b"hello").unwrap();
            let signature = blinding
                .finalize(key_pair.blind_sign(blinded.as_ref()).unwrap().as_ref())
                .unwrap();
            let signature = signature.as_ref();

            for verifier in ALGORITHMS {
                let result = KeyPair::from_pkcs8(verifier, der)
                    .unwrap()
                    .public_key()
                    .verify(b"hello", signature);
                assert_eq!(result.is_ok(), core::ptr::eq(signer, verifier));
            }

            if signer.randomized {
                let (prefix, rest) = signature.split_at(PREFIX_LEN);
                let deterministic = match signer.salt {
                    PssSalt::Hash => &RSABSSA_SHA384_PSS_DETERMINISTIC,
                    _ => &RSABSSA_SHA384_PSSZERO_DETERMINISTIC,
                };
                let deterministic = KeyPair::from_pkcs8(deterministic, der).unwrap();
                let prepared = [prefix, b"hello"].concat();
                deterministic.public_key().verify(&prepared, rest).unwrap();
                assert_eq!(public_key.verify(&prepared, rest), Err(Error::BadSignature));
                assert_eq!(
                    public_key.verify(b"hello", &signature[..31]),
                    Err(Error::BadSignature)
                );
            }
        }
    }

    #[test]
    fn finalize_refuses_bad_replies() {
        let key_pair = KeyPair::from_pkcs8(&RSABSSA_SHA384_PSS_RANDOMIZED, KEYS[0]).unwrap();
        let public_key = key_pair.public_key();
        let (other, _) = public_key.blind(b"other").unwrap();
        let other = key_pair.blind_sign(other.as_ref()).unwrap();
        let (blinded, _) = public_key.blind(b"hello").unwrap();
        let good = key_pair.blind_sign(blinded.as_ref()).unwrap();
        let good = good.as_ref();
        let mut flipped = good.to_vec();
        flipped[100] ^= 1;

        for reply in [
            &good[1..],
            &[good, &[0]].concat(),
            &flipped,
            other.as_ref(),
            &[0; 256],
            &[0xff; 256],
            &[],
        ] {
            let (_, blinding) = public_key
                .blind_with(b"hello", &mut SliceRandomSource(&[7; 32 + 48 + 256]))
                .unwrap();
            assert_eq!(blinding.finalize(reply).err(), Some(Error::BadSignature));
        }
    }

    #[test]
    fn blind_sign_refuses_bad_requests() {
        let key_pair = KeyPair::from_pkcs8(&RSABSSA_SHA384_PSS_RANDOMIZED, KEYS[0]).unwrap();
        for request in [&[1; 255][..], &[1; 257], &[0xff; 256], &[]] {
            assert_eq!(key_pair.blind_sign(request).err(), Some(Error::WrongLength));
        }
    }

    /// A blind at least the modulus, or sharing a factor with it, as zero
    /// does, is drawn again.
    #[test]
    fn blinding_rejects_bad_blinds() {
        let key_pair = KeyPair::from_pkcs8(&RSABSSA_SHA384_PSS_DETERMINISTIC, KEYS[1]).unwrap();
        let public_key = key_pair.public_key();
        let salt = [3; HASH_LEN];
        let r = [0, 1, 2, 3].repeat(65)[..257].to_vec();
        let blind = |rejected: &[&[u8]]| {
            let random = [&salt[..], &rejected.concat(), &r].concat();
            let (blinded, _) = public_key
                .blind_with(b"hello", &mut SliceRandomSource(&random))
                .unwrap();
            blinded
        };

        // The top byte holds one bit of a 2049-bit modulus, so 0xff is
        // masked to below it, and only a draw above it is refused.
        let expected = blind(&[]);
        // Miri, which is slow, runs only the last case, which holds both.
        if !cfg!(miri) {
            assert_eq!(blind(&[&[0; 257]]).as_ref(), expected.as_ref());
            assert_eq!(blind(&[&[0xff; 257]]).as_ref(), expected.as_ref());
        }
        assert_eq!(
            blind(&[&[0xff; 257], &[0; 257], &[0xff; 257]]).as_ref(),
            expected.as_ref()
        );
    }

    /// A modulus of `5m / 4` for an encoded message `m`, which ends in
    /// `0xbc`, so `m / 4` is odd, shares the factor `m / 4` with it.
    #[test]
    fn refuses_a_key_sharing_a_factor_with_the_message() {
        let algorithm = &RSABSSA_SHA384_PSS_DETERMINISTIC;
        let digest = algorithm.digest(&[0; PREFIX_LEN], b"hello");
        // About one salt in five gives an `m` whose `5m / 4` has 2048 bits.
        let (salt, n) = (0..=255)
            .find_map(|byte| {
                let salt = [byte; HASH_LEN];
                let mut m = [0; 256];
                crate::high::pkcs1::encode_pss_sig::<Sha384>(
                    &mut m,
                    2047,
                    &mut SliceRandomSource(&salt),
                    &digest,
                    HASH_LEN,
                )
                .unwrap();
                // m + m / 4, from the least significant byte up.
                let (mut n, mut carry) = ([0; 256], 0u16);
                for i in (0..256).rev() {
                    let quarter = m[i] >> 2 | m.get(i.wrapping_sub(1)).map_or(0, |b| b << 6);
                    let sum = u16::from(m[i]) + u16::from(quarter) + carry;
                    n[i] = sum as u8;
                    carry = sum >> 8;
                }
                (carry == 0 && n[0] >= 0x80).then_some((salt, n))
            })
            .unwrap();
        let public_key = PublicKey::from_components(
            algorithm,
            &PublicKeyComponents {
                n: &n[..],
                e: &[1, 0, 1][..],
            },
        )
        .unwrap();
        let random = [&salt[..], &[1; 256]].concat();
        assert_eq!(
            public_key
                .blind_with(b"hello", &mut SliceRandomSource(&random))
                .err(),
            Some(KeyFormatError::RsaModulus.into())
        );
    }

    #[test]
    fn refuses_other_keys() {
        let key_pair = KeyPair::from_pkcs8(&RSABSSA_SHA384_PSS_RANDOMIZED, KEYS[0]).unwrap();
        let pss = key_pair.public_key().to_spki();
        let pss_zero = KeyPair::from_pkcs8(&RSABSSA_SHA384_PSSZERO_RANDOMIZED, KEYS[0])
            .unwrap()
            .public_key()
            .to_spki();
        let rsa_encryption = rsa::SigningKey::from_pkcs8_der(KEYS[0]).unwrap();
        let mut rsa_encryption_spki = [0; 1024];
        let rsa_encryption = rsa_encryption
            .public_key()
            .to_spki_der(&mut rsa_encryption_spki)
            .unwrap();

        PublicKey::new(&RSABSSA_SHA384_PSS_DETERMINISTIC, pss.as_ref()).unwrap();
        for (algorithm, spki) in [
            (&RSABSSA_SHA384_PSS_RANDOMIZED, pss_zero.as_ref()),
            (&RSABSSA_SHA384_PSSZERO_RANDOMIZED, pss.as_ref()),
            (&RSABSSA_SHA384_PSS_RANDOMIZED, rsa_encryption),
        ] {
            assert_eq!(
                PublicKey::new(algorithm, spki).err(),
                Some(KeyFormatError::MismatchedSpkiAlgorithm.into())
            );
        }

        let small = include_bytes!("rsa/rsa2047.pub.der");
        let small = rsa::VerifyingKey::from_der(small).unwrap();
        let small = PublicKey {
            key: small,
            algorithm: &RSABSSA_SHA384_PSS_RANDOMIZED,
        }
        .to_spki();
        assert_eq!(
            PublicKey::new(&RSABSSA_SHA384_PSS_RANDOMIZED, small.as_ref()).err(),
            Some(KeyFormatError::RsaModulus.into())
        );
    }

    #[test]
    fn debug_shows_no_secrets() {
        let key_pair = KeyPair::from_pkcs8(&RSABSSA_SHA384_PSS_RANDOMIZED, KEYS[0]).unwrap();
        assert_eq!(
            format!("{key_pair:?}"),
            "KeyPair { algorithm: RSABSSA-SHA384-PSS-Randomized, .. }"
        );
        let (_, blinding) = key_pair.public_key().blind(b"hello").unwrap();
        assert_eq!(
            format!("{blinding:?}"),
            "Blinding { algorithm: RSABSSA-SHA384-PSS-Randomized, .. }"
        );
    }

    /// Under `admin/ctgrind`, memcheck fails this if blinding branches on or
    /// indexes by the message, its prefix, salt, or blind, or signing by the
    /// key, or unblinding by the blind's inverse, for good replies or bad.
    #[test]
    fn stays_secret() {
        for algorithm in ALGORITHMS {
            let key_pair =
                KeyPair::from_pkcs8(algorithm, include_bytes!("rsa/rsa2049.pkcs8.der")).unwrap();
            let public_key = key_pair.public_key();
            let message = [0x5a; 40];
            ct::secret_slice(&message);
            // The blind's top byte is below the modulus's, so it is drawn
            // once.
            let random = [
                &vec![0x6b; algorithm.prefix_len() + salt_len(algorithm)][..],
                &[0],
                &[0x6b; 256],
            ]
            .concat();
            ct::secret_slice(&random);

            let blind = || {
                public_key
                    .blind_with(&message, &mut SliceRandomSource(&random))
                    .unwrap()
            };
            let (blinded, blinding) = blind();
            let blind_signature = key_pair.blind_sign(blinded.as_ref()).unwrap();
            let blind_signature = blind_signature.as_ref();

            // A malicious signer's replies: 1, which unblinds to the inverse
            // itself, and a tampered signature.
            let mut one = vec![0; blind_signature.len()];
            *one.last_mut().unwrap() = 1;
            let mut tampered = blind_signature.to_vec();
            tampered[9] ^= 1;
            for reply in [one, tampered] {
                let (_, blinding) = blind();
                assert_eq!(blinding.finalize(&reply).err(), Some(Error::BadSignature));
            }

            let signature = blinding.finalize(blind_signature).unwrap();
            public_key.verify(&[0x5a; 40], signature.as_ref()).unwrap();
        }
    }
}
