//! RSA key pairs and public keys.

use alloc::boxed::Box;
use core::fmt;
use core::marker::PhantomData;

use crate::{der, error, rand, signature};

/// Signs with any [`signature::RsaEncoding`]; its modulus is 2048 to 4096 bits, a multiple of 512, as ring requires.
pub struct KeyPair {
    key: rind::rsa::KeyPair,
    public: PublicKey,
}

impl KeyPair {
    /// Loads a PKCS#8 RSA private key, named `rsaEncryption`, `id-RSAES-OAEP`,
    /// or `id-ea-rsa`.
    pub fn from_pkcs8(pkcs8: &[u8]) -> Result<Self, error::KeyRejected> {
        der::pkcs8_v1_only(pkcs8)?;
        rind::rsa::KeyPair::from_pkcs8(pkcs8)
            .map_err(error::KeyRejected::rind)
            .and_then(Self::new)
    }

    /// Loads a PKCS#1 `RSAPrivateKey`.
    pub fn from_der(input: &[u8]) -> Result<Self, error::KeyRejected> {
        rind::rsa::KeyPair::from_pkcs1(input)
            .map_err(error::KeyRejected::rind)
            .and_then(Self::new)
    }

    /// Loads a private key from its big-endian integers.
    ///
    /// Unlike ring, this takes private integers with leading zero bytes, as
    /// aws-lc-rs does: refusing them would branch on their secret first
    /// bytes. It refuses integers that disagree, which ring may take.
    pub fn from_components<Public, Private>(
        components: &KeyPairComponents<Public, Private>,
    ) -> Result<Self, error::KeyRejected>
    where
        Public: AsRef<[u8]>,
        Private: AsRef<[u8]>,
    {
        let public_key = &components.public_key;
        let components = rind::rsa::KeyPairComponents {
            public_key: rind::rsa::PublicKeyComponents {
                n: public_key.n.as_ref(),
                e: public_key.e.as_ref(),
            },
            d: components.d.as_ref(),
            p: components.p.as_ref(),
            q: components.q.as_ref(),
            dp: components.dP.as_ref(),
            dq: components.dQ.as_ref(),
            qi: components.qInv.as_ref(),
        };
        rind::rsa::KeyPair::from_components(&components)
            .map_err(error::KeyRejected::rind)
            .and_then(Self::new)
    }

    // rind takes moduli up to 8192 bits of any length; ring refuses the
    // rest, and an exponent below 65537.
    fn new(key: rind::rsa::KeyPair) -> Result<Self, error::KeyRejected> {
        // rind's encoding of a key it loaded always parses.
        let public = PublicKey::new(key.public_key().as_ref())
            .or(Err(error::KeyRejected::invalid_encoding()))?;
        let bits = public.modulus_bits();
        if bits < 2048 {
            return Err(error::KeyRejected::too_small());
        }
        if bits > 4096 {
            return Err(error::KeyRejected::too_large());
        }
        if bits % 512 != 0 {
            return Err(error::KeyRejected::private_modulus_len_not_multiple_of_512_bits());
        }
        if public.exponent() < 65537 {
            return Err(error::KeyRejected::too_small());
        }
        Ok(Self { key, public })
    }

    /// The public key.
    pub fn public(&self) -> &PublicKey {
        &self.public
    }

    /// The length of the modulus, and of every signature, in bytes.
    pub fn public_modulus_len(&self) -> usize {
        self.public.modulus_len()
    }

    /// Signs `msg` with `padding_alg` into `signature`, which must be [`Self::public_modulus_len`] bytes.
    pub fn sign(
        &self,
        padding_alg: &'static dyn signature::RsaEncoding,
        rng: &dyn rand::SecureRandom,
        msg: &[u8],
        signature: &mut [u8],
    ) -> Result<(), error::Unspecified> {
        let _ = rng;
        if signature.len() != self.public_modulus_len() {
            return Err(error::Unspecified);
        }
        let signed = self
            .key
            .sign(padding_alg.rind(), msg)
            .map_err(|_| error::Unspecified)?;
        if signed.as_ref().len() != signature.len() {
            return Err(error::Unspecified);
        }
        signature.copy_from_slice(signed.as_ref());
        Ok(())
    }
}

impl signature::KeyPair for KeyPair {
    type PublicKey = PublicKey;

    fn public_key(&self) -> &PublicKey {
        &self.public
    }
}

impl fmt::Debug for KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RsaKeyPair")
            .field("public", &self.public)
            .finish()
    }
}

/// An RSA private key as its big-endian integers.
#[derive(Clone, Copy)]
#[allow(non_snake_case)]
pub struct KeyPairComponents<Public, Private = Public> {
    /// The modulus and public exponent.
    pub public_key: PublicKeyComponents<Public>,
    /// The private exponent.
    pub d: Private,
    /// The first prime factor of the modulus.
    pub p: Private,
    /// The second prime factor of the modulus.
    pub q: Private,
    /// `d` mod `p - 1`.
    pub dP: Private,
    /// `d` mod `q - 1`.
    pub dQ: Private,
    /// The inverse of `q` mod `p`.
    pub qInv: Private,
}

impl<Public, Private> fmt::Debug for KeyPairComponents<Public, Private>
where
    PublicKeyComponents<Public>: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // As ring, leaving out the private integers.
        f.debug_struct("KeyPairComponents")
            .field("public_key", &self.public_key)
            .finish()
    }
}

/// An RSA public key, whose bytes are its PKCS#1 `RSAPublicKey` DER.
#[derive(Clone)]
pub struct PublicKey {
    der: Box<[u8]>,
    n: Box<[u8]>,
    e: Box<[u8]>,
}

impl PublicKey {
    fn new(der: &[u8]) -> Result<Self, error::Unspecified> {
        let (n, e) = der::rsa_public_key(der)?;
        Ok(Self {
            der: der.into(),
            n: n.into(),
            e: e.into(),
        })
    }

    /// The length of the modulus, in bytes.
    pub fn modulus_len(&self) -> usize {
        self.n.len()
    }

    // `der::rsa_public_key` returns the modulus without leading zero bytes.
    fn modulus_bits(&self) -> usize {
        8 * self.n.len() - self.n.first().map_or(8, |top| top.leading_zeros() as usize)
    }

    fn exponent(&self) -> u64 {
        self.e.iter().fold(0u64, |e, byte| {
            e.saturating_mul(256).saturating_add(u64::from(*byte))
        })
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        &self.der
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PublicKey")
            .field(&crate::Hex(self.as_ref()))
            .finish()
    }
}

/// An RSA public key as its big-endian modulus and exponent, without leading zero bytes.
#[derive(Clone, Copy, Debug)]
pub struct PublicKeyComponents<B> {
    /// The modulus.
    pub n: B,
    /// The public exponent.
    pub e: B,
}

impl<B: AsRef<[u8]>> PublicKeyComponents<B> {
    /// Verifies `signature` over `message` with this key and `params`.
    pub fn verify(
        &self,
        params: &RsaParameters,
        message: &[u8],
        signature: &[u8],
    ) -> Result<(), error::Unspecified> {
        let components = rind::rsa::PublicKeyComponents {
            n: self.n.as_ref(),
            e: self.e.as_ref(),
        };
        signature::verified(
            rind::rsa::PublicKey::from_components(&components)
                .and_then(|key| key.verify(params.rind, message, signature)),
        )
    }
}

impl<B: FromIterator<u8>> From<&PublicKey> for PublicKeyComponents<B> {
    fn from(public_key: &PublicKey) -> Self {
        Self {
            n: public_key.n.iter().copied().collect(),
            e: public_key.e.iter().copied().collect(),
        }
    }
}

/// An RSA verification algorithm: a padding, a hash, and the smallest modulus it accepts, up to 8192 bits.
pub struct RsaParameters {
    rind: &'static rind::rsa::VerificationAlgorithm,
    id: &'static str,
    // ring's holds a `&'static dyn` padding, which is neither `UnwindSafe`
    // nor `RefUnwindSafe`, so neither is this.
    unwind: PhantomData<&'static dyn Sync>,
}

impl fmt::Debug for RsaParameters {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.id)
    }
}

impl crate::sealed::Sealed for RsaParameters {}

impl signature::VerificationAlgorithm for RsaParameters {
    fn verify(
        &self,
        public_key: untrusted::Input<'_>,
        msg: untrusted::Input<'_>,
        signature: untrusted::Input<'_>,
    ) -> Result<(), error::Unspecified> {
        let key = rind::rsa::PublicKey::new(public_key.as_slice_less_safe());
        signature::verified(key.and_then(|key| {
            key.verify(
                self.rind,
                msg.as_slice_less_safe(),
                signature.as_slice_less_safe(),
            )
        }))
    }
}

pub(crate) mod verification {
    use super::RsaParameters;

    macro_rules! rsa_params {
        ($name:ident, $rind:path, $doc:expr) => {
            #[doc = $doc]
            pub static $name: RsaParameters = RsaParameters {
                rind: &$rind,
                id: stringify!($name),
                unwind: core::marker::PhantomData,
            };
        };
    }

    rsa_params!(
        RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY,
        rind::rsa::verify::legacy::PKCS1_1024_SHA1,
        "PKCS#1 v1.5 with SHA-1 and a modulus of 1024 to 8192 bits, for legacy protocols only."
    );
    rsa_params!(
        RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY,
        rind::rsa::verify::legacy::PKCS1_1024_SHA256,
        "PKCS#1 v1.5 with SHA-256 and a modulus of 1024 to 8192 bits, for legacy protocols only."
    );
    rsa_params!(
        RSA_PKCS1_1024_8192_SHA512_FOR_LEGACY_USE_ONLY,
        rind::rsa::verify::legacy::PKCS1_1024_SHA512,
        "PKCS#1 v1.5 with SHA-512 and a modulus of 1024 to 8192 bits, for legacy protocols only."
    );
    rsa_params!(
        RSA_PKCS1_2048_8192_SHA1_FOR_LEGACY_USE_ONLY,
        rind::rsa::verify::legacy::PKCS1_SHA1,
        "PKCS#1 v1.5 with SHA-1 and a modulus of 2048 to 8192 bits, for legacy protocols only."
    );
    rsa_params!(
        RSA_PKCS1_2048_8192_SHA256,
        rind::rsa::verify::PKCS1_SHA256,
        "PKCS#1 v1.5 with SHA-256 and a modulus of 2048 to 8192 bits."
    );
    rsa_params!(
        RSA_PKCS1_2048_8192_SHA384,
        rind::rsa::verify::PKCS1_SHA384,
        "PKCS#1 v1.5 with SHA-384 and a modulus of 2048 to 8192 bits."
    );
    rsa_params!(
        RSA_PKCS1_2048_8192_SHA512,
        rind::rsa::verify::PKCS1_SHA512,
        "PKCS#1 v1.5 with SHA-512 and a modulus of 2048 to 8192 bits."
    );
    rsa_params!(
        RSA_PKCS1_3072_8192_SHA384,
        rind::rsa::verify::legacy::PKCS1_3072_SHA384,
        "PKCS#1 v1.5 with SHA-384 and a modulus of 3072 to 8192 bits."
    );
    rsa_params!(
        RSA_PSS_2048_8192_SHA256,
        rind::rsa::verify::PSS_SHA256,
        "PSS with SHA-256, MGF1, a 32-byte salt, and a modulus of 2048 to 8192 bits."
    );
    rsa_params!(
        RSA_PSS_2048_8192_SHA384,
        rind::rsa::verify::PSS_SHA384,
        "PSS with SHA-384, MGF1, a 48-byte salt, and a modulus of 2048 to 8192 bits."
    );
    rsa_params!(
        RSA_PSS_2048_8192_SHA512,
        rind::rsa::verify::PSS_SHA512,
        "PSS with SHA-512, MGF1, a 64-byte salt, and a modulus of 2048 to 8192 bits."
    );
}

pub(crate) mod padding {
    use core::fmt;

    use crate::{digest, sealed};

    /// An RSA signature encoding, a padding and a hash, for [`super::KeyPair::sign`].
    pub trait RsaEncoding: Encoding {}

    // A caller bounded by `E: RsaEncoding` can call this trait's methods, so
    // it has exactly those of ring's `Padding`.
    #[allow(private_bounds)]
    pub trait Encoding: fmt::Debug + Sync + sealed::Sealed + Signs + 'static {
        fn digest_alg(&self) -> &'static digest::Algorithm;
    }

    // `pub(crate)`, so callers cannot reach the rind algorithm through it.
    pub(crate) trait Signs {
        fn rind(&self) -> &'static rind::rsa::SigningAlgorithm;
    }

    // ring's PKCS#1 and PSS encodings are two types, so a caller cannot
    // assign one's value where the other's goes; neither can rind-ring's.
    macro_rules! padding_type {
        ($ty:ident, $doc:expr) => {
            #[doc = $doc]
            pub struct $ty {
                rind: &'static rind::rsa::SigningAlgorithm,
                digest: &'static digest::Algorithm,
                id: &'static str,
            }

            impl fmt::Debug for $ty {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    f.write_str(self.id)
                }
            }

            impl sealed::Sealed for $ty {}

            impl Encoding for $ty {
                fn digest_alg(&self) -> &'static digest::Algorithm {
                    self.digest
                }
            }

            impl Signs for $ty {
                fn rind(&self) -> &'static rind::rsa::SigningAlgorithm {
                    self.rind
                }
            }

            impl RsaEncoding for $ty {}
        };
    }

    padding_type!(Pkcs1, "One of the `RSA_PKCS1_*` signing encodings.");
    padding_type!(Pss, "One of the `RSA_PSS_*` signing encodings.");

    macro_rules! padding {
        ($name:ident, $rind:ident, $ty:ident, $digest:ident, $doc:expr) => {
            #[doc = $doc]
            pub static $name: $ty = $ty {
                rind: &rind::rsa::sign::$rind,
                digest: &digest::$digest,
                id: stringify!($name),
            };
        };
    }

    padding!(
        RSA_PKCS1_SHA256,
        PKCS1_SHA256,
        Pkcs1,
        SHA256,
        "PKCS#1 v1.5 signatures with SHA-256."
    );
    padding!(
        RSA_PKCS1_SHA384,
        PKCS1_SHA384,
        Pkcs1,
        SHA384,
        "PKCS#1 v1.5 signatures with SHA-384."
    );
    padding!(
        RSA_PKCS1_SHA512,
        PKCS1_SHA512,
        Pkcs1,
        SHA512,
        "PKCS#1 v1.5 signatures with SHA-512."
    );
    padding!(
        RSA_PSS_SHA256,
        PSS_SHA256,
        Pss,
        SHA256,
        "PSS signatures with SHA-256, MGF1, and a 32-byte random salt."
    );
    padding!(
        RSA_PSS_SHA384,
        PSS_SHA384,
        Pss,
        SHA384,
        "PSS signatures with SHA-384, MGF1, and a 48-byte random salt."
    );
    padding!(
        RSA_PSS_SHA512,
        PSS_SHA512,
        Pss,
        SHA512,
        "PSS signatures with SHA-512, MGF1, and a 64-byte random salt."
    );
}

#[cfg(test)]
mod tests {
    use super::PublicKey;
    use crate::der::tests::tlv;

    #[test]
    fn modulus_bits_counts_a_top_byte_below_0x80() {
        // 0x01ff is 9 bits. `8 * len - leading_zeros` becomes `8 * len +
        // leading_zeros` only for this shape: a modulus whose top bit is set
        // has no leading zeros, and the two agree.
        let modulus = tlv(0x02, &[0x01, 0xff]);
        let exponent = tlv(0x02, &[0x01, 0x00, 0x01]);
        let der = tlv(0x30, &[modulus, exponent].concat());
        let key = PublicKey::new(&der).unwrap();
        assert_eq!(key.modulus_bits(), 9);
    }
}
