// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::aead::{
    AES_128_GCM, Aad, LessSafeKey, NONCE_LEN, Nonce, RandomizedNonceKey, TlsProtocolId,
    TlsRecordSealingKey, UnboundKey,
};

// rind-aws-lc-rs: these test aws-lc-rs's private `UnboundKey::seal_combined`
// and `seal_combined_randnonce` through the public methods that call them,
// `LessSafeKey::seal_in_place_append_tag` and
// `RandomizedNonceKey::seal_in_place_append_tag`.

struct NormalBuffer(Vec<u8>);

impl AsMut<[u8]> for NormalBuffer {
    fn as_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_slice()
    }
}

impl<'a> Extend<&'a u8> for NormalBuffer {
    fn extend<T: IntoIterator<Item = &'a u8>>(&mut self, iter: T) {
        self.0.extend(iter);
    }
}

struct NoGrowBuffer(Vec<u8>);

impl AsMut<[u8]> for NoGrowBuffer {
    fn as_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_slice()
    }
}

impl<'a> Extend<&'a u8> for NoGrowBuffer {
    fn extend<T: IntoIterator<Item = &'a u8>>(&mut self, _iter: T) {}
}

struct ShortExtendBuffer(Vec<u8>);

impl AsMut<[u8]> for ShortExtendBuffer {
    fn as_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_slice()
    }
}

impl<'a> Extend<&'a u8> for ShortExtendBuffer {
    fn extend<T: IntoIterator<Item = &'a u8>>(&mut self, iter: T) {
        self.0.extend(iter.into_iter().take(1));
    }
}

struct ShrinkingBuffer(Vec<u8>);

impl AsMut<[u8]> for ShrinkingBuffer {
    fn as_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_slice()
    }
}

impl<'a> Extend<&'a u8> for ShrinkingBuffer {
    fn extend<T: IntoIterator<Item = &'a u8>>(&mut self, _iter: T) {
        let new_len = self.0.len().saturating_sub(1);
        self.0.truncate(new_len);
    }
}

fn test_key() -> LessSafeKey {
    LessSafeKey::new(UnboundKey::new(&AES_128_GCM, &[0x42u8; 16]).unwrap())
}

fn test_randnonce_key() -> RandomizedNonceKey {
    RandomizedNonceKey::new(&AES_128_GCM, &[0x42u8; 16]).unwrap()
}

fn test_nonce() -> Nonce {
    Nonce::try_assume_unique_for_key(&[0x24u8; NONCE_LEN]).unwrap()
}

#[test]
fn seal_combined_normal_extend_succeeds_and_roundtrips() {
    let key = test_key();
    let plaintext = b"seal_combined soundness regression test".to_vec();
    let mut in_out = NormalBuffer(plaintext.clone());

    key.seal_in_place_append_tag(test_nonce(), Aad::empty(), &mut in_out)
        .expect("a normal, Vec-like Extend impl must succeed");
    let nonce = test_nonce();

    assert_eq!(in_out.0.len(), plaintext.len() + key.algorithm().tag_len());

    let opened: &[u8] = key
        .open_within(nonce, Aad::empty(), &mut in_out.0, 0..)
        .expect("the sealed output must open back to the original plaintext");
    assert_eq!(opened, plaintext.as_slice());
}

#[test]
fn seal_combined_rejects_no_grow_extend() {
    let key = test_key();
    let plaintext = b"some plaintext".to_vec();
    let original_len = plaintext.len();
    let mut in_out = NoGrowBuffer(plaintext);

    let result = key.seal_in_place_append_tag(test_nonce(), Aad::empty(), &mut in_out);

    assert!(
        result.is_err(),
        "a no-op Extend impl must not be trusted to have appended the tag"
    );
    assert_eq!(in_out.0.len(), original_len);
}

#[test]
fn seal_combined_rejects_short_extend() {
    let key = test_key();
    let mut in_out = ShortExtendBuffer(b"some plaintext".to_vec());

    let result = key.seal_in_place_append_tag(test_nonce(), Aad::empty(), &mut in_out);

    assert!(
        result.is_err(),
        "an Extend impl that appends fewer bytes than the tag length must be rejected"
    );
}

#[test]
fn seal_combined_rejects_shrinking_extend() {
    let key = test_key();
    let mut in_out = ShrinkingBuffer(b"some plaintext".to_vec());

    let result = key.seal_in_place_append_tag(test_nonce(), Aad::empty(), &mut in_out);

    assert!(
        result.is_err(),
        "an Extend impl that shrinks the collection must be rejected"
    );
}

#[test]
fn seal_combined_randnonce_normal_extend_succeeds_and_roundtrips() {
    let key = test_randnonce_key();
    let plaintext = b"seal_combined_randnonce soundness regression test".to_vec();
    let mut in_out = NormalBuffer(plaintext.clone());

    let nonce = key
        .seal_in_place_append_tag(Aad::empty(), &mut in_out)
        .expect("a normal, Vec-like Extend impl must succeed");

    assert_eq!(in_out.0.len(), plaintext.len() + key.algorithm().tag_len());

    // rind-aws-lc-rs: `RandomizedNonceKey` opens in place.
    let opened = key
        .open_in_place(nonce, Aad::empty(), &mut in_out.0)
        .expect("the sealed output must open back to the original plaintext");
    assert_eq!(opened, plaintext.as_slice());
}

#[test]
fn seal_combined_randnonce_rejects_no_grow_extend() {
    let key = test_randnonce_key();
    let plaintext = b"some plaintext".to_vec();
    let original_len = plaintext.len();
    let mut in_out = NoGrowBuffer(plaintext);

    let result = key.seal_in_place_append_tag(Aad::empty(), &mut in_out);

    assert!(
        result.is_err(),
        "a no-op Extend impl must not be trusted to have appended the tag"
    );
    assert_eq!(in_out.0.len(), original_len);
}

#[test]
fn seal_combined_randnonce_rejects_short_extend() {
    let key = test_randnonce_key();
    let mut in_out = ShortExtendBuffer(b"some plaintext".to_vec());

    let result = key.seal_in_place_append_tag(Aad::empty(), &mut in_out);

    assert!(
        result.is_err(),
        "an Extend impl that appends fewer bytes than the tag length must be rejected"
    );
}

#[test]
fn seal_combined_randnonce_rejects_shrinking_extend() {
    let key = test_randnonce_key();
    let mut in_out = ShrinkingBuffer(b"some plaintext".to_vec());

    let result = key.seal_in_place_append_tag(Aad::empty(), &mut in_out);

    assert!(
        result.is_err(),
        "an Extend impl that shrinks the collection must be rejected"
    );
}

// rind-aws-lc-rs: added. AWS-LC's TLS AEAD records a nonce only once it seals,
// so a buffer refused before that leaves the nonce free for a retry.
#[test]
fn tls_seal_rejected_extend_leaves_nonce_unused() {
    for protocol in [TlsProtocolId::TLS12, TlsProtocolId::TLS13] {
        let mut key = TlsRecordSealingKey::new(&AES_128_GCM, protocol, &[0x42u8; 16]).unwrap();
        let mut refused = NoGrowBuffer(b"some plaintext".to_vec());
        assert!(
            key.seal_in_place_append_tag(test_nonce(), Aad::empty(), &mut refused)
                .is_err()
        );
        assert_eq!(refused.0, b"some plaintext");

        let mut in_out = b"some plaintext".to_vec();
        key.seal_in_place_append_tag(test_nonce(), Aad::empty(), &mut in_out)
            .expect("the refused seal must not have used the nonce");
        let opened: &[u8] = test_key()
            .open_within(test_nonce(), Aad::empty(), &mut in_out, 0..)
            .unwrap();
        assert_eq!(opened, b"some plaintext");
    }
}
