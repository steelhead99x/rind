// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::asn1::pkix;
use super::asn1::{self, Type};
use crate::error::{Error, KeyFormatError};

pub(crate) struct Key<'a>(pkix::OneAsymmetricKey<'a>);

impl<'a> Key<'a> {
    /// Helper for decoding PKCS#8 key encodings.
    ///
    /// This decodes the given slice as a whole `OneAsymmetricKey`, and then:
    ///
    /// - refuses a publicKey field in a v1 document; a v2 document may omit it,
    ///   as RFC 5958 allows and aws-lc takes,
    /// - ensures the key algorithm is one of `algorithms`,
    /// - ensures the parameters are `parameters`.
    ///
    /// Any `attributes` are skipped, as aws-lc and ring do.
    ///
    /// The caller must then  validate and process the `private_key()` value.
    ///
    /// The caller may also validate and cross-check the `public_key()`, if present,
    /// against the public key calculated from the private key.
    pub(crate) fn decode(
        slice: &'a [u8],
        algorithms: &[&asn1::ObjectId],
        parameters: Option<asn1::Any<'_>>,
    ) -> Result<Self, Error> {
        let oak = pkix::OneAsymmetricKey::from_bytes(slice).map_err(KeyFormatError::Asn1)?;

        if oak.version == pkix::Pkcs8Version::Pkcs8v1 && oak.publicKey.inner().is_some() {
            return Err(KeyFormatError::UnsupportedPkcs8Version.into());
        }

        if !algorithms.contains(&&oak.privateKeyAlgorithm.algorithm) {
            return Err(KeyFormatError::MismatchedPkcs8Algorithm.into());
        }

        if oak.privateKeyAlgorithm.parameters != parameters {
            return Err(KeyFormatError::MismatchedPkcs8Parameters.into());
        }

        Ok(Self(oak))
    }

    /// Construct a PKCS#8 key encoding.
    ///
    /// If `public_key_encoding` is given, it is the bytes in the
    /// `publicKey` BIT STRING and a PKCS#8 v2 object is returned.
    /// Otherwise, a PKCS#8 v1 object is returned.
    pub(crate) fn construct(
        private_key_encoding: &'a [u8],
        public_key_encoding: Option<&'a [u8]>,
        algorithm: asn1::ObjectId,
        parameters: Option<asn1::Any<'a>>,
    ) -> Self {
        let (public, version) = match public_key_encoding {
            Some(pub_key) => (
                asn1::Context::from(asn1::BitString::new(pub_key)),
                pkix::Pkcs8Version::Pkcs8v2,
            ),
            None => (asn1::Context::absent(), pkix::Pkcs8Version::Pkcs8v1),
        };

        Self(pkix::OneAsymmetricKey {
            version,
            privateKeyAlgorithm: pkix::AlgorithmIdentifier {
                algorithm,
                parameters,
            },
            privateKey: asn1::OctetString::new(private_key_encoding),
            attributes: asn1::Context::absent(),
            publicKey: public,
        })
    }

    /// Writes the encoding into `output`, returning the used prefix.
    pub(crate) fn encode<'b>(&self, output: &'b mut [u8]) -> Result<&'b [u8], Error> {
        let len = self
            .0
            .encode(&mut asn1::Encoder::new(output))
            .map_err(|_| Error::WrongLength)?;

        output.get(..len).ok_or(Error::WrongLength)
    }

    /// Returns the `privateKey` body of a document without a public key.
    ///
    /// For key types whose v2 public key the caller does not check, which
    /// aws-lc-rs refuses for ECDSA and RSA.
    pub(crate) fn v1_private_key(&self) -> Result<&'a [u8], Error> {
        match self.public_key() {
            Some(_) => Err(KeyFormatError::UnsupportedPkcs8Version.into()),
            None => Ok(self.private_key()),
        }
    }

    /// Returns the slice that covers the `privateKey` `OCTET STRING` body.
    ///
    /// This can be decoded by the caller as the correct asn1 type.
    pub(crate) fn private_key(&self) -> &'a [u8] {
        self.0.privateKey.as_octets()
    }

    /// Returns the slice that covers the `publicKey` `BIT STRING` body.
    ///
    /// This can be decoded by the caller as the correct asn1 type (or
    /// used raw, depending on the type)
    pub(crate) fn public_key(&self) -> Option<&'a [u8]> {
        self.0.publicKey.inner().as_ref().map(|x| x.as_octets())
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::high::asn1::oid;

    #[test]
    fn round_trip_ed25519_v2() {
        let bytes = include_bytes!("asn1/testdata/ed25519-p8v2.bin");
        let k = Key::decode(bytes, &[&oid::id_ed25519], None).unwrap();

        assert_eq!(k.private_key().len(), 34);
        assert_eq!(k.public_key().unwrap().len(), 32);

        let mut buffer = vec![0; bytes.len()];
        let buffer = k.encode(&mut buffer).unwrap();
        assert_eq!(buffer, bytes);
    }

    #[test]
    fn construct_ed25519() {
        let private_key = &[
            0x04, 0x20, 0xe9, 0x7e, 0x54, 0xef, 0x0c, 0xd2, 0x04, 0x78, 0xd2, 0x9e, 0x1f, 0x0e,
            0x16, 0xf0, 0x7d, 0x95, 0x8d, 0x2b, 0xce, 0xc8, 0xed, 0xb0, 0x3c, 0x28, 0xcc, 0xa5,
            0xac, 0x10, 0x35, 0x80, 0x0c, 0x3f,
        ][..];
        let public_key = &[
            0xde, 0x4e, 0x8b, 0xdc, 0xbc, 0xef, 0x5e, 0x9f, 0xff, 0x0b, 0xa1, 0x19, 0x89, 0xfe,
            0xc6, 0x92, 0x82, 0xba, 0xe7, 0x4f, 0xb1, 0x6a, 0xd9, 0x96, 0xac, 0xbd, 0xdd, 0xcc,
            0x07, 0x55, 0xbc, 0x09,
        ][..];
        let k = Key::construct(private_key, Some(public_key), oid::id_ed25519.clone(), None);
        assert_eq!(k.private_key(), private_key);
        assert_eq!(k.public_key(), Some(public_key));

        let bytes = include_bytes!("asn1/testdata/ed25519-p8v2.bin");
        let mut buffer = vec![0; bytes.len()];
        let buffer = k.encode(&mut buffer).unwrap();
        assert_eq!(buffer, bytes);
    }

    /// An Ed25519 PKCS#8 document of `version` whose fields after the
    /// private key are `tail`, from RFC 8410's example key.
    fn ed25519_with(version: u8, tail: &[&[u8]]) -> Vec<u8> {
        let mut body = hex::decode(
            "020100300506032b657004220420d4ee72dbf913584ad5b6d8f1f769f8ad3afe7c28cbf1d4fbe097a88f44755842",
        )
        .unwrap();
        body[2] = version;
        body.extend(tail.concat());
        [&[0x30, body.len() as u8][..], &body].concat()
    }

    #[test]
    fn skips_attributes() {
        const ATTRIBUTE: &[u8] = &[0xa0, 0x03, 0xff, 0xff, 0xff];
        const RFC_ATTRIBUTE: &str =
            "a01f301d060a2a864886f70d01090914310f0c0d437572646c6520436861697273";
        let public_key =
            hex::decode("19bf44096984cdfe8541bac167dc3b96c85086aa30b6b6cb0c5c38ad703166e1")
                .unwrap();
        let public_key_field = [&[0x81, 0x21, 0x00][..], &public_key].concat();

        // Skipped, not interpreted: the contents need not be valid DER.
        for (version, tail) in [
            (0, vec![&[0xa0, 0x00][..]]),
            (0, vec![ATTRIBUTE]),
            (
                1,
                vec![&hex::decode(RFC_ATTRIBUTE).unwrap(), &public_key_field],
            ),
        ] {
            let bytes = ed25519_with(version, &tail);
            let k = Key::decode(&bytes, &[&oid::id_ed25519], None).unwrap();
            assert_eq!(k.private_key().len(), 34);
            assert_eq!(k.public_key(), (version == 1).then_some(&public_key[..]));
        }

        use asn1::Error::*;
        for (version, tail, error) in [
            (0, vec![&[0xa0, 0x04, 0x30, 0x00][..]], UnexpectedEof),
            (0, vec![&[0xa0, 0x81, 0x01, 0x00]], NonCanonicalEncoding),
            (0, vec![&[0x80, 0x00]], UnexpectedTrailingData),
            (0, vec![&[0xa2, 0x00]], UnexpectedTrailingData),
            (0, vec![ATTRIBUTE, &[0x05, 0x00]], UnexpectedTrailingData),
            (0, vec![ATTRIBUTE, ATTRIBUTE], UnexpectedTrailingData),
            (
                1,
                vec![&public_key_field, ATTRIBUTE],
                UnexpectedTrailingData,
            ),
        ] {
            assert_eq!(
                Some(KeyFormatError::Asn1(error).into()),
                Key::decode(&ed25519_with(version, &tail), &[&oid::id_ed25519], None).err(),
                "{tail:02x?}",
            );
        }
    }

    #[test]
    fn v2_without_public_key() {
        const ATTRIBUTE: &[u8] = &[0xa0, 0x03, 0xff, 0xff, 0xff];
        for tail in [vec![], vec![ATTRIBUTE]] {
            let bytes = ed25519_with(1, &tail);
            let k = Key::decode(&bytes, &[&oid::id_ed25519], None).unwrap();
            assert_eq!(k.private_key().len(), 34);
            assert_eq!(k.public_key(), None);
        }
    }

    #[test]
    fn rejects_unknown_version() {
        let mut bytes = include_bytes!("asn1/testdata/ed25519-p8v2.bin").to_vec();
        bytes[4] = 0x03;
        assert_eq!(
            Some(KeyFormatError::Asn1(asn1::Error::UnhandledEnumValue).into()),
            Key::decode(&bytes, &[&oid::id_ed25519], None).err(),
        );
    }

    #[test]
    fn rejects_wrong_version_for_public_key() {
        let mut bytes = include_bytes!("asn1/testdata/ed25519-p8v2.bin").to_vec();
        bytes[4] = 0x00;
        assert_eq!(
            Some(KeyFormatError::UnsupportedPkcs8Version.into()),
            Key::decode(&bytes, &[&oid::id_ed25519], None).err(),
        );
    }
}
