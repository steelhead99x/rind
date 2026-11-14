#![no_main]

use aws_lc_rs::cipher::{
    DecryptionContext, EncryptionContext, PaddedBlockDecryptingKey, PaddedBlockEncryptingKey,
    UnboundCipherKey,
};
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::cipher::{AES_128, AES_192, AES_256, AesCbcDecryptingKey, AesCbcEncryptingKey, CbcIv};

mod edit;

fuzz_target!(|input: (Operation, [u8; 16], Vec<u8>, edit::Edit)| {
    let (op, iv, msg, edit) = input;
    let (ours, theirs, key) = match &op {
        Operation::Aes128 { key } => (&AES_128, &aws_lc_rs::cipher::AES_128, &key[..]),
        Operation::Aes256 { key } => (&AES_256, &aws_lc_rs::cipher::AES_256, &key[..]),
        Operation::Aes192 { key } => (&AES_192, &aws_lc_rs::cipher::AES_192, &key[..]),
    };
    let theirs = || UnboundCipherKey::new(theirs, key).unwrap();

    // Both encrypt alike.
    let mut ct = msg.clone();
    AesCbcEncryptingKey::new(ours, key)
        .unwrap()
        .encrypt(CbcIv::assume_unpredictable(iv), &mut ct)
        .unwrap();
    let mut right = msg.clone();
    PaddedBlockEncryptingKey::cbc_pkcs7(theirs())
        .unwrap()
        .less_safe_encrypt(&mut right, EncryptionContext::Iv128(iv.into()))
        .unwrap();
    assert_eq!(ct, right);

    // Both decrypt the ciphertext tampered with alike, or refuse it.
    edit.apply(&mut ct);
    let mut ours_out = ct.clone();
    let ours_result = AesCbcDecryptingKey::new(ours, key)
        .unwrap()
        .decrypt(&iv, &mut ours_out)
        .map(|pt| pt.to_vec());
    let mut theirs_out = ct.clone();
    let theirs_result = PaddedBlockDecryptingKey::cbc_pkcs7(theirs())
        .unwrap()
        .decrypt(&mut theirs_out, DecryptionContext::Iv128(iv.into()))
        .map(|pt| pt.to_vec());
    assert_eq!(ours_result.as_ref().ok(), theirs_result.as_ref().ok());
    assert_eq!(ours_result.is_err(), theirs_result.is_err());
});

#[derive(Arbitrary, Debug)]
enum Operation {
    Aes128 { key: [u8; 16] },
    Aes256 { key: [u8; 32] },
    Aes192 { key: [u8; 24] },
}
