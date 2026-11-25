//! Key bytes for the binding targets: arbitrary, or one of rind's test keys
//! with an [`Edit`], so a target reaches the paths past a parser's checks
//! without a seed corpus.

// Each target uses some of these.
#![allow(dead_code)]

use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary};

use crate::edit::Edit;

pub const FILES: &[&[u8]] = &[
    include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der"),
    include_bytes!("../../rind/src/high/rsa/rsa2048.der"),
    include_bytes!("../../rind/src/high/rsa/rsa2048-e34.pub.der"),
    include_bytes!("../../rind/src/high/asn1/testdata/spki-rsa-2k.bin"),
    include_bytes!("../../rind/src/high/asn1/testdata/rsapublickey-1k.bin"),
    include_bytes!("../../rind/src/high/ecdsa/secp256r1.pkcs8.der"),
    include_bytes!("../../rind/src/high/ecdsa/secp256r1.der"),
    include_bytes!("../../rind/src/high/ecdsa/secp384r1.pkcs8.der"),
    include_bytes!("../../rind/src/high/ecdsa/secp384r1.der"),
    include_bytes!("../../rind/src/high/ecdsa/secp521r1.pkcs8.der"),
    include_bytes!("../../rind/src/high/ecdsa/secp521r1.der"),
    include_bytes!("../../rind/src/high/asn1/testdata/spki-ec-nistp256.bin"),
    include_bytes!("../../rind/src/high/asn1/testdata/ed25519-p8v1.bin"),
    include_bytes!("../../rind/src/high/asn1/testdata/ed25519-p8v2.bin"),
];

/// Key bytes: arbitrary, or a test key, edited.
#[derive(Arbitrary, Debug)]
pub enum Material {
    Raw(Vec<u8>),
    File(u8, Edit),
}

impl Material {
    pub fn bytes(&self) -> Vec<u8> {
        match self {
            Self::Raw(bytes) => bytes.clone(),
            Self::File(index, edit) => {
                let mut bytes = FILES[usize::from(*index) % FILES.len()].to_vec();
                edit.apply(&mut bytes);
                bytes
            }
        }
    }
}
