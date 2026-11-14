// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! HKDF (HMAC-based Key Derivation Function).
//!
//! HKDF is standardized in [RFC 5869](https://datatracker.ietf.org/doc/html/rfc5869).

use core::fmt;

use super::digest::{Digest, MAX_OUTPUT_LEN};
use super::hmac;
use crate::low::Entry;
use crate::{Error, aead};

/// An HKDF algorithm, chosen by one of this module's constants.
#[derive(Debug)]
pub struct Algorithm(&'static hmac::Algorithm);

impl Algorithm {
    /// The HMAC this HKDF is built on.
    pub(crate) fn hmac(&self) -> &'static hmac::Algorithm {
        self.0
    }

    /// The hash's output length, a pseudorandom key's.
    pub(crate) fn hash_len(&self) -> usize {
        self.0.tag_len()
    }
}

/// HKDF-SHA1, for legacy protocols only.
///
/// Like HMAC, HKDF does not rely on SHA-1's broken collision resistance, but
/// new protocols should pick a SHA-2 hash.
pub static HKDF_SHA1: Algorithm = Algorithm(&hmac::HMAC_SHA1);

/// HKDF-SHA256.
pub static HKDF_SHA256: Algorithm = Algorithm(&hmac::HMAC_SHA256);

/// HKDF-SHA384.
pub static HKDF_SHA384: Algorithm = Algorithm(&hmac::HMAC_SHA384);

/// HKDF-SHA512.
pub static HKDF_SHA512: Algorithm = Algorithm(&hmac::HMAC_SHA512);

/// A salt, keyed once and reused for every secret it extracts from.
pub struct Salt(hmac::Key);

impl Salt {
    /// Keys `algorithm` with `value`; an empty `value` is RFC 5869's absent salt.
    pub fn new(algorithm: &'static Algorithm, value: &[u8]) -> Self {
        Self(hmac::Key::new(algorithm.0, value))
    }

    /// Extracts a pseudorandom key from `secret` (HKDF-Extract).
    ///
    /// Never fails in rind. It returns a `Result` because rind-fips, whose API
    /// is rind's, refuses an empty salt, which FIPS 140-3 does not approve.
    pub fn extract(&self, secret: &[u8]) -> Result<Prk, Error> {
        let _entry = Entry::new_secret();
        let prk = hmac::sign(&self.0, secret);
        Ok(Prk(hmac::Key::new(self.0.algorithm(), prk.as_ref())))
    }
}

impl fmt::Debug for Salt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Salt")
            .field("algorithm", &self.0.id())
            .finish_non_exhaustive()
    }
}

/// A pseudorandom key, from which [`Prk::expand`] derives any number of keys; wiped on drop under the `wipe` feature.
//
// Held as an HMAC key so each expand block skips the two key compressions.
pub struct Prk(hmac::Key);

impl Prk {
    /// A pseudorandom key `algorithm` extracted elsewhere, such as from
    /// HPKE's labeled input.
    pub(crate) fn new(algorithm: &'static Algorithm, bytes: &[u8]) -> Self {
        Self(hmac::Key::new(algorithm.0, bytes))
    }

    /// Derives key material for the concatenation of `info` (HKDF-Expand), as long as `len` says.
    ///
    /// Fails with [`Error::WrongLength`] if `len` is more than 255 hash
    /// outputs, as far as HKDF-Expand's one-byte block counter reaches.
    /// rind-fips also refuses an empty `info`, which FIPS 140-3 does not
    /// approve.
    pub fn expand<'a, L: KeyType>(
        &'a self,
        info: &'a [&'a [u8]],
        len: L,
    ) -> Result<Okm<'a, L>, Error> {
        if sealed::Sealed::len(&len) > 255 * self.0.algorithm().tag_len() {
            return Err(Error::WrongLength);
        }
        Ok(Okm {
            prk: self,
            info,
            len,
        })
    }

    // Fills `out`, which `expand` limited to 255 hash outputs.
    fn expand_into(&self, info: &[&[u8]], out: &mut [u8]) {
        let _entry = Entry::new_secret();
        let mut block: Option<Digest> = None;
        for (counter, chunk) in (1..=255u8).zip(out.chunks_mut(self.0.algorithm().tag_len())) {
            let mut ctx = self.0.start();
            if let Some(block) = &block {
                ctx.update(block.as_ref());
            }
            for part in info {
                ctx.update(part);
            }
            ctx.update(&[counter]);
            let tag = ctx.finish();
            chunk.copy_from_slice(&tag.as_ref()[..chunk.len()]);
            block = Some(tag);
        }
    }
}

mod sealed {
    pub trait Sealed {
        /// The output length in bytes.
        fn len(&self) -> usize;
    }
}

/// A length of HKDF output: a plain `usize`, or the algorithm of the key it becomes.
pub trait KeyType: sealed::Sealed {}

/// Raw key material of this many bytes, for [`Okm::fill`].
impl sealed::Sealed for usize {
    fn len(&self) -> usize {
        *self
    }
}
impl KeyType for usize {}

/// A key of the algorithm's [`aead::Algorithm::key_len`].
impl sealed::Sealed for &'static aead::Algorithm {
    fn len(&self) -> usize {
        self.key_len()
    }
}
impl KeyType for &'static aead::Algorithm {}

/// A key of the algorithm's [`aead::quic::Algorithm::key_len`].
impl sealed::Sealed for &'static aead::quic::Algorithm {
    fn len(&self) -> usize {
        self.key_len()
    }
}
impl KeyType for &'static aead::quic::Algorithm {}

/// A key of the algorithm's [`hmac::Algorithm::tag_len`].
impl sealed::Sealed for &'static hmac::Algorithm {
    fn len(&self) -> usize {
        self.tag_len()
    }
}
impl KeyType for &'static hmac::Algorithm {}

/// The pseudorandom key of a further [`Prk::expand`], the hash's output length.
impl sealed::Sealed for &'static Algorithm {
    fn len(&self) -> usize {
        self.hash_len()
    }
}
impl KeyType for &'static Algorithm {}

impl fmt::Debug for Prk {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Prk")
            .field("algorithm", &self.0.id())
            .finish_non_exhaustive()
    }
}

/// Key material from [`Prk::expand`], sized by `L`: fill a buffer for a `usize` length, or convert it into the key an algorithm names.
#[must_use]
pub struct Okm<'a, L: KeyType> {
    prk: &'a Prk,
    info: &'a [&'a [u8]],
    len: L,
}

impl<L: KeyType> fmt::Debug for Okm<'_, L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Okm")
            .field("algorithm", &self.prk.0.id())
            .finish_non_exhaustive()
    }
}

impl Okm<'_, usize> {
    /// Writes the key material into `out`.
    ///
    /// Fails with [`Error::WrongLength`], leaving `out` unchanged, unless
    /// `out` is the length [`Prk::expand`] was given.
    pub fn fill(self, out: &mut [u8]) -> Result<(), Error> {
        if out.len() != self.len {
            return Err(Error::WrongLength);
        }
        self.prk.expand_into(self.info, out);
        Ok(())
    }
}

// Each conversion expands into a stack buffer for its key to copy. Every key
// length fits the buffer and the 255-block limit.
impl From<Okm<'_, &'static aead::Algorithm>> for aead::Key {
    fn from(okm: Okm<'_, &'static aead::Algorithm>) -> Self {
        let algorithm = okm.len;
        let mut buf = [0u8; MAX_OUTPUT_LEN];
        let bytes = &mut buf[..algorithm.key_len()];
        okm.prk.expand_into(okm.info, bytes);
        Self::new(algorithm, bytes).expect("HKDF output is the algorithm's key length")
    }
}

impl From<Okm<'_, &'static aead::quic::Algorithm>> for aead::quic::HeaderProtectionKey {
    fn from(okm: Okm<'_, &'static aead::quic::Algorithm>) -> Self {
        let algorithm = okm.len;
        let mut buf = [0u8; MAX_OUTPUT_LEN];
        let bytes = &mut buf[..algorithm.key_len()];
        okm.prk.expand_into(okm.info, bytes);
        Self::new(algorithm, bytes).expect("HKDF output is the algorithm's key length")
    }
}

impl From<Okm<'_, &'static hmac::Algorithm>> for hmac::Key {
    fn from(okm: Okm<'_, &'static hmac::Algorithm>) -> Self {
        let algorithm = okm.len;
        let mut buf = [0u8; MAX_OUTPUT_LEN];
        let bytes = &mut buf[..algorithm.tag_len()];
        okm.prk.expand_into(okm.info, bytes);
        Self::new(algorithm, bytes)
    }
}

impl From<Okm<'_, &'static Algorithm>> for Prk {
    fn from(okm: Okm<'_, &'static Algorithm>) -> Self {
        let algorithm = okm.len;
        let mut buf = [0u8; MAX_OUTPUT_LEN];
        let bytes = &mut buf[..algorithm.0.tag_len()];
        okm.prk.expand_into(okm.info, bytes);
        Self(hmac::Key::new(algorithm.0, bytes))
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::test::{Acvp, acvp};

    /// SP 800-56C's two-step KDF over HKDF, with the fixed info its groups
    /// name: each party's identity and optional ephemeral data, then the
    /// output length in bits as 32 bits.
    #[test]
    fn acvp_kda() {
        for group in acvp("KDA-HKDF-Sp800-56Cr2") {
            assert!(!group.flag("multiExpansion"));
            let config = &group["kdfConfiguration"];
            assert_eq!(config.str("fixedInfoPattern"), "uPartyInfo||vPartyInfo||l");
            assert_eq!(config.str("fixedInfoEncoding"), "concatenation");
            let algorithm = match config.str("hmacAlg") {
                "SHA2-256" => &HKDF_SHA256,
                "SHA2-384" => &HKDF_SHA384,
                "SHA2-512" => &HKDF_SHA512,
                other => panic!("unexpected hash {other}"),
            };
            for test in group.tests() {
                let params = &test["kdfParameter"];
                let mut secret = params.hex("z");
                if group.flag("usesHybridSharedSecret") {
                    secret.extend(params.hex("t"));
                }
                let len = params.int("l");
                let mut info = Vec::new();
                for party in [&test["fixedInfoPartyU"], &test["fixedInfoPartyV"]] {
                    info.extend(party.hex("partyId"));
                    if party.get("ephemeralData").is_some() {
                        info.extend(party.hex("ephemeralData"));
                    }
                }
                info.extend((len as u32).to_be_bytes());

                let mut dkm = vec![0; len / 8];
                Salt::new(algorithm, &params.hex("salt"))
                    .extract(&secret)
                    .unwrap()
                    .expand(&[&info], dkm.len())
                    .unwrap()
                    .fill(&mut dkm)
                    .unwrap();
                let matches = dkm == test.hex("dkm");
                match group.str("testType") {
                    "AFT" => assert!(matches),
                    "VAL" => assert_eq!(matches, test.flag("testPassed")),
                    other => panic!("unexpected test type {other}"),
                }
            }
        }
    }
    use crate::aead::{AES_128_GCM, AES_256_GCM, CHACHA20_POLY1305, Nonce, quic};

    #[test]
    fn rfc5869() {
        // Appendix A: SHA-256 in A.1 to A.3, SHA-1 in A.4 to A.7. A.3 and A.6
        // have no salt or info; A.7's absent salt is an empty one.
        let cases = [
            (
                &HKDF_SHA256,
                "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b",
                "000102030405060708090a0b0c",
                "f0f1f2f3f4f5f6f7f8f9",
                "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5",
                "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf\
                 34007208d5b887185865",
            ),
            (
                &HKDF_SHA256,
                "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f\
                 202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\
                 404142434445464748494a4b4c4d4e4f",
                "606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f\
                 808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f\
                 a0a1a2a3a4a5a6a7a8a9aaabacadaeaf",
                "b0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecf\
                 d0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeef\
                 f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff",
                "06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244",
                "b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c\
                 59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71\
                 cc30c58179ec3e87c14c01d5c1f3434f1d87",
            ),
            (
                &HKDF_SHA256,
                "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b",
                "",
                "",
                "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04",
                "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d\
                 9d201395faa4b61a96c8",
            ),
            (
                &HKDF_SHA1,
                "0b0b0b0b0b0b0b0b0b0b0b",
                "000102030405060708090a0b0c",
                "f0f1f2f3f4f5f6f7f8f9",
                "9b6c18c432a7bf8f0e71c8eb88f4b30baa2ba243",
                "085a01ea1b10f36933068b56efa5ad81a4f14b822f5b091568a9cdd4f155fda2\
                 c22e422478d305f3f896",
            ),
            (
                &HKDF_SHA1,
                "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f\
                 202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\
                 404142434445464748494a4b4c4d4e4f",
                "606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f\
                 808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f\
                 a0a1a2a3a4a5a6a7a8a9aaabacadaeaf",
                "b0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecf\
                 d0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeef\
                 f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff",
                "8adae09a2a307059478d309b26c4115a224cfaf6",
                "0bd770a74d1160f7c9f12cd5912a06ebff6adcae899d92191fe4305673ba2ffe\
                 8fa3f1a4e5ad79f3f334b3b202b2173c486ea37ce3d397ed034c7f9dfeb15c5e\
                 927336d0441f4c4300e2cff0d0900b52d3b4",
            ),
            (
                &HKDF_SHA1,
                "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b",
                "",
                "",
                "da8c8a73c7fa77288ec6f5e7c297786aa0d32d01",
                "0ac1af7002b3d761d1e55298da9d0506b9ae52057220a306e07b6b87e8df21d0\
                 ea00033de03984d34918",
            ),
            (
                &HKDF_SHA1,
                "0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c",
                "",
                "",
                "2adccada18779e7c2077ad2eb19d3f3e731385dd",
                "2c91117204d745f3500d636a62f64f0ab3bae548aa53d423b0d1f27ebba6f5e5\
                 673a081d70cce7acfc48",
            ),
        ];

        for (algorithm, ikm, salt, info, prk, okm) in cases {
            let got = Salt::new(algorithm, &hex::decode(salt).unwrap())
                .extract(&hex::decode(ikm).unwrap())
                .unwrap();
            // HMAC of the empty message under the stored key identifies the PRK.
            let wanted = hmac::Key::new(algorithm.0, &hex::decode(prk).unwrap());
            assert_eq!(
                hmac::sign(&got.0, b"").as_ref(),
                hmac::sign(&wanted, b"").as_ref()
            );

            let info = hex::decode(info).unwrap();
            let mut out = vec![0u8; okm.len() / 2];
            got.expand(&[&info], out.len())
                .unwrap()
                .fill(&mut out)
                .unwrap();
            assert_eq!(hex::encode(out), okm);
        }
    }

    #[test]
    fn rfc9001_initial_secrets() {
        // Appendix A.1: each secret is the pseudorandom key of the next expand.
        let label = |name: &[u8], len: u16| {
            let mut info = len.to_be_bytes().to_vec();
            info.push(6 + name.len() as u8);
            info.extend_from_slice(b"tls13 ");
            info.extend_from_slice(name);
            info.push(0);
            info
        };
        let salt = hex::decode("38762cf7f55934b34d179ae6a4c80cadccbb7f0a").unwrap();
        let initial = Salt::new(&HKDF_SHA256, &salt)
            .extract(&hex::decode("8394c8f03e515708").unwrap())
            .unwrap();

        let client_in = label(b"client in", 32);
        let client = Prk::from(initial.expand(&[&client_in], &HKDF_SHA256).unwrap());
        let mut out = [0u8; 16];
        let quic_key = label(b"quic key", 16);
        client
            .expand(&[&quic_key], 16)
            .unwrap()
            .fill(&mut out)
            .unwrap();
        assert_eq!(hex::encode(out), "1f369613dd76d5467730efcbe3b1a22d");
        let quic_hp = label(b"quic hp", 16);
        client
            .expand(&[&quic_hp], 16)
            .unwrap()
            .fill(&mut out)
            .unwrap();
        assert_eq!(hex::encode(out), "9f50449e04a0e810283a1e9933adedd2");
    }

    static ALGORITHMS: [&Algorithm; 4] = [&HKDF_SHA1, &HKDF_SHA256, &HKDF_SHA384, &HKDF_SHA512];

    #[test]
    fn lengths() {
        // The one-byte block counter caps each hash at 255 of its outputs.
        for algorithm in ALGORITHMS {
            let prk = Salt::new(algorithm, b"salt").extract(b"secret").unwrap();
            let max = 255 * algorithm.0.tag_len();

            let mut out = vec![0u8; max];
            prk.expand(&[], max).unwrap().fill(&mut out).unwrap();
            assert_eq!(prk.expand(&[], max + 1).unwrap_err(), Error::WrongLength);
            for len in [0, max - 1, max + 1] {
                let mut wrong = vec![0u8; len];
                assert_eq!(
                    prk.expand(&[], max).unwrap().fill(&mut wrong),
                    Err(Error::WrongLength)
                );
                assert!(wrong.iter().all(|b| *b == 0));
            }
        }
    }

    #[test]
    fn keys_match_filled_bytes() {
        let prk = Salt::new(&HKDF_SHA256, b"salt").extract(b"secret").unwrap();
        let info: [&[u8]; 2] = [b"label", b"context"];

        for algorithm in [&AES_128_GCM, &AES_256_GCM, &CHACHA20_POLY1305] {
            let mut bytes = vec![0u8; algorithm.key_len()];
            prk.expand(&info, bytes.len())
                .unwrap()
                .fill(&mut bytes)
                .unwrap();
            let seal = |key: aead::Key| {
                key.seal_in_place_separate_tag(
                    Nonce::assume_unique_for_key([0; 12]),
                    &[],
                    &mut [0u8; 16],
                )
                .unwrap()
            };
            assert_eq!(
                seal(aead::Key::from(prk.expand(&info, algorithm).unwrap())).as_ref(),
                seal(aead::Key::new(algorithm, &bytes).unwrap()).as_ref(),
            );
        }

        for algorithm in [&quic::AES_128, &quic::AES_256, &quic::CHACHA20] {
            let mut bytes = vec![0u8; algorithm.key_len()];
            prk.expand(&info, bytes.len())
                .unwrap()
                .fill(&mut bytes)
                .unwrap();
            let key = quic::HeaderProtectionKey::from(prk.expand(&info, algorithm).unwrap());
            assert_eq!(
                key.mask(&[7; 16]),
                quic::HeaderProtectionKey::new(algorithm, &bytes)
                    .unwrap()
                    .mask(&[7; 16]),
            );
        }

        for algorithm in [
            &hmac::HMAC_SHA1,
            &hmac::HMAC_SHA256,
            &hmac::HMAC_SHA384,
            &hmac::HMAC_SHA512,
        ] {
            let mut bytes = vec![0u8; algorithm.tag_len()];
            prk.expand(&info, bytes.len())
                .unwrap()
                .fill(&mut bytes)
                .unwrap();
            let key = hmac::Key::from(prk.expand(&info, algorithm).unwrap());
            assert_eq!(key.algorithm().tag_len(), algorithm.tag_len());
            assert_eq!(
                hmac::sign(&key, b"message").as_ref(),
                hmac::sign(&hmac::Key::new(algorithm, &bytes), b"message").as_ref()
            );
        }
    }

    #[test]
    fn secret_ikm() {
        // Under `admin/ctgrind`, nothing may branch on or index by the input
        // key material or anything derived from it, including the keys an
        // `Okm` becomes.
        let info: [&[u8]; 1] = [b"info"];
        let derive = |algorithm: &'static Algorithm, ikm: &[u8]| {
            let prk = Salt::new(algorithm, b"salt").extract(ikm).unwrap();
            let chained = Prk::from(prk.expand(&info, algorithm).unwrap());
            let mut bytes = [0u8; 100];
            chained
                .expand(&info, bytes.len())
                .unwrap()
                .fill(&mut bytes)
                .unwrap();
            let aead_key = aead::Key::from(prk.expand(&info, &AES_256_GCM).unwrap());
            let aead_tag = aead_key
                .seal_in_place_separate_tag(Nonce::assume_unique_for_key([0; 12]), &[], &mut [])
                .unwrap();
            let hmac_key = hmac::Key::from(prk.expand(&info, &hmac::HMAC_SHA256).unwrap());
            let hmac_tag = hmac::sign(&hmac_key, b"message");
            (
                bytes,
                aead_tag.as_ref().to_vec(),
                hmac_tag.as_ref().to_vec(),
            )
        };

        for algorithm in ALGORITHMS {
            let ikm = [0x5a; 48];
            let wanted = derive(algorithm, &ikm);

            crate::low::ct::secret_slice(&ikm);
            let (bytes, aead_tag, hmac_tag) = derive(algorithm, &ikm);
            crate::low::ct::public_slice(&bytes);
            crate::low::ct::public_slice(&aead_tag);
            crate::low::ct::public_slice(&hmac_tag);
            assert_eq!((bytes, aead_tag, hmac_tag), wanted);
        }
    }
}
