//! RSA key pairs and public keys.
//!
//! ring's `KeyPair::from_components` and `KeyPairComponents` are not
//! offered: building a key from big-endian private components means
//! encoding them as DER here, which branches on their secret leading bytes.
//! Load the key as PKCS#1 or PKCS#8 instead.

use core::fmt;

use crate::{der, error, rand, signature};

/// Signs with any [`signature::RsaEncoding`]; its modulus is 2048 to 4096 bits, a multiple of 512, as ring requires.
pub struct KeyPair {
    key: rind::signature::RsaKeyPair,
    public: PublicKey,
}

impl KeyPair {
    /// Loads a PKCS#8 RSA private key, named `rsaEncryption`, `id-RSAES-OAEP`,
    /// or `id-ea-rsa`.
    pub fn from_pkcs8(pkcs8: &[u8]) -> Result<Self, error::KeyRejected> {
        rind::signature::RsaKeyPair::from_pkcs8(pkcs8)
            .map_err(error::KeyRejected::rind)
            .and_then(Self::new)
    }

    /// Loads a PKCS#1 `RSAPrivateKey`.
    pub fn from_der(input: &[u8]) -> Result<Self, error::KeyRejected> {
        rind::signature::RsaKeyPair::from_pkcs1(input)
            .map_err(error::KeyRejected::rind)
            .and_then(Self::new)
    }

    // rind takes moduli up to 8192 bits of any length; ring refuses the
    // rest, and an exponent below 65537.
    fn new(key: rind::signature::RsaKeyPair) -> Result<Self, error::KeyRejected> {
        let public = key.public_key(&rind::signature::sign::RSA_PKCS1_SHA256);
        let public =
            PublicKey::new(public.as_ref()).map_err(|_| error::KeyRejected::invalid_encoding())?;
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
            .sign(padding_alg.padding().rind, msg)
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
        rind::signature::PublicKey::from_components(params.rind, &components)
            .and_then(|key| key.verify(message, signature))
            .map_err(|_| error::Unspecified)
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
    rind: &'static rind::signature::RsaVerificationAlgorithm,
    id: &'static str,
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
        signature::verify(self.rind, public_key, msg, signature)
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
            };
        };
    }

    rsa_params!(
        RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY,
        rind::signature::verify::legacy::RSA_PKCS1_1024_SHA1,
        "PKCS#1 v1.5 with SHA-1 and a modulus of 1024 to 8192 bits, for legacy protocols only."
    );
    rsa_params!(
        RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY,
        rind::signature::verify::legacy::RSA_PKCS1_1024_SHA256,
        "PKCS#1 v1.5 with SHA-256 and a modulus of 1024 to 8192 bits, for legacy protocols only."
    );
    rsa_params!(
        RSA_PKCS1_1024_8192_SHA512_FOR_LEGACY_USE_ONLY,
        rind::signature::verify::legacy::RSA_PKCS1_1024_SHA512,
        "PKCS#1 v1.5 with SHA-512 and a modulus of 1024 to 8192 bits, for legacy protocols only."
    );
    rsa_params!(
        RSA_PKCS1_2048_8192_SHA1_FOR_LEGACY_USE_ONLY,
        rind::signature::verify::legacy::RSA_PKCS1_SHA1,
        "PKCS#1 v1.5 with SHA-1 and a modulus of 2048 to 8192 bits, for legacy protocols only."
    );
    rsa_params!(
        RSA_PKCS1_2048_8192_SHA256,
        rind::signature::verify::RSA_PKCS1_SHA256,
        "PKCS#1 v1.5 with SHA-256 and a modulus of 2048 to 8192 bits."
    );
    rsa_params!(
        RSA_PKCS1_2048_8192_SHA384,
        rind::signature::verify::RSA_PKCS1_SHA384,
        "PKCS#1 v1.5 with SHA-384 and a modulus of 2048 to 8192 bits."
    );
    rsa_params!(
        RSA_PKCS1_2048_8192_SHA512,
        rind::signature::verify::RSA_PKCS1_SHA512,
        "PKCS#1 v1.5 with SHA-512 and a modulus of 2048 to 8192 bits."
    );
    rsa_params!(
        RSA_PKCS1_3072_8192_SHA384,
        rind::signature::verify::legacy::RSA_PKCS1_3072_SHA384,
        "PKCS#1 v1.5 with SHA-384 and a modulus of 3072 to 8192 bits."
    );
    rsa_params!(
        RSA_PSS_2048_8192_SHA256,
        rind::signature::verify::RSA_PSS_SHA256,
        "PSS with SHA-256, MGF1, a 32-byte salt, and a modulus of 2048 to 8192 bits."
    );
    rsa_params!(
        RSA_PSS_2048_8192_SHA384,
        rind::signature::verify::RSA_PSS_SHA384,
        "PSS with SHA-384, MGF1, a 48-byte salt, and a modulus of 2048 to 8192 bits."
    );
    rsa_params!(
        RSA_PSS_2048_8192_SHA512,
        rind::signature::verify::RSA_PSS_SHA512,
        "PSS with SHA-512, MGF1, a 64-byte salt, and a modulus of 2048 to 8192 bits."
    );
}

pub(crate) mod padding {
    use core::fmt;

    use crate::sealed;

    /// An RSA signature encoding, a padding and a hash, for [`super::KeyPair::sign`].
    pub trait RsaEncoding: Encoding {}

    // Returns rind-ring's own `Padding`, never a rind type: a caller bounded
    // by `E: RsaEncoding` can call this, and rind-ring's public API must not
    // name rind.
    pub trait Encoding: fmt::Debug + Sync + sealed::Sealed + 'static {
        fn padding(&self) -> &Padding;
    }

    /// One of the `RSA_PKCS1_*` and `RSA_PSS_*` signing encodings.
    pub struct Padding {
        pub(super) rind: &'static rind::signature::RsaSigningAlgorithm,
        id: &'static str,
    }

    impl fmt::Debug for Padding {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str(self.id)
        }
    }

    impl sealed::Sealed for Padding {}

    impl Encoding for Padding {
        fn padding(&self) -> &Padding {
            self
        }
    }

    impl RsaEncoding for Padding {}

    macro_rules! padding {
        ($name:ident, $doc:expr) => {
            #[doc = $doc]
            pub static $name: Padding = Padding {
                rind: &rind::signature::sign::$name,
                id: stringify!($name),
            };
        };
    }

    padding!(RSA_PKCS1_SHA256, "PKCS#1 v1.5 signatures with SHA-256.");
    padding!(RSA_PKCS1_SHA384, "PKCS#1 v1.5 signatures with SHA-384.");
    padding!(RSA_PKCS1_SHA512, "PKCS#1 v1.5 signatures with SHA-512.");
    padding!(
        RSA_PSS_SHA256,
        "PSS signatures with SHA-256, MGF1, and a 32-byte random salt."
    );
    padding!(
        RSA_PSS_SHA384,
        "PSS signatures with SHA-384, MGF1, and a 48-byte random salt."
    );
    padding!(
        RSA_PSS_SHA512,
        "PSS signatures with SHA-512, MGF1, and a 64-byte random salt."
    );
}

#[cfg(test)]
mod tests {
    use super::PublicKey;

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

    fn tlv(tag: u8, body: &[u8]) -> Vec<u8> {
        assert!(body.len() < 128);
        let mut out = vec![tag, body.len() as u8];
        out.extend_from_slice(body);
        out
    }
}
