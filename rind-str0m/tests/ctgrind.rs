//! Constant-time checks for each secret path, run under valgrind by
//! `admin/ctgrind`.
//!
//! Secret inputs are marked undefined, so memcheck flags any branch or memory
//! index that depends on them. Outputs that are public by design are marked
//! defined before the test checks them. DTLS runs on `rind-dimpl`, and its
//! certificate key on `rind-rcgen`, whose own ctgrind tests cover them.
//!
//! Expected outputs are fixed: aws-lc-rs computes some of them wrongly under
//! valgrind on armv7. `tests/differential.rs` compares against it natively.

use crabgrind::memcheck::{self, MemState};
use crabgrind::valgrind::{self, RunningMode};
use str0m::crypto::{AeadAes128Gcm, Aes128CmSha1_80, CryptoProvider};

/// Marks `value` secret: memcheck flags any branch or index that depends on it.
fn secret<T: ?Sized>(value: &T) {
    mark(value, MemState::Undefined);
}

/// Marks `value` public, so the test may branch on it.
fn public<T: ?Sized>(value: &T) {
    mark(value, MemState::Defined);
}

fn mark<T: ?Sized>(value: &T, state: MemState) {
    if let RunningMode::Valgrind = valgrind::running_mode() {
        memcheck::mark_memory((value as *const T).cast(), size_of_val(value), state).unwrap();
    }
}

fn rind() -> CryptoProvider {
    rind_str0m::default_provider()
}

fn hex(s: &str) -> Vec<u8> {
    let s: String = s.split_whitespace().collect();
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

#[test]
fn key_derivation() {
    let rind = rind();
    let input = [0x24; 16];
    let (key128, key256) = ([0x42; 16], [0x42; 32]);
    let mut ours = [0u8; 32];

    secret(&key128);
    rind.srtp_provider
        .srtp_aes_128_ecb_round(&key128, &input, &mut ours);
    public(&ours);
    assert_eq!(ours[..16], hex("5b327e72d47a5e29f9b4056755e2a654"));

    secret(&key256);
    rind.srtp_provider
        .srtp_aes_256_ecb_round(&key256, &input, &mut ours);
    public(&ours);
    assert_eq!(ours[..16], hex("f3bd0549faac94a41a5e14396d29b64a"));
}

#[test]
fn aes_cm() {
    let rind = rind();
    let key = [0x42; 16];
    let iv = Aes128CmSha1_80::rtp_iv([0x24; 14], 0x1234_5678, 7);
    let input = [0x11; 100];
    let expected = hex(
        "cc7c1db36e91ebb7c6709caa327bd111e8d2ebc34b89636cff6221768f55e0b1
        090b3125b03f45d2140fe327b089ac2bec2f4cc14798a36d36fcae8f6f1eb91b
        7656e05937434fda160ca03b2fa226776f5abfb1efc342b1c94c688ebb0a7433
        bd76da40",
    );

    secret(&key);
    let srtp = rind.srtp_provider.aes_128_cm_sha1_80();
    let mut ciphertext = [0u8; 100];
    srtp.create_cipher(key, true)
        .encrypt(&iv, &input, &mut ciphertext)
        .unwrap();
    public(&ciphertext);
    assert_eq!(ciphertext[..], expected);

    let mut plaintext = [0u8; 100];
    srtp.create_cipher(key, false)
        .decrypt(&iv, &ciphertext, &mut plaintext)
        .unwrap();
    public(&plaintext);
    assert_eq!(plaintext, input);
}

#[test]
fn aes_gcm() {
    let rind = rind();
    let iv = AeadAes128Gcm::rtp_iv([0x24; 12], 0x1234_5678, 7, 7);
    let aad = [0x33; 12];
    let input = [0x11; 100];

    let key = [0x42; 16];
    let expected = hex(
        "f5a1658039881ba721f39426313eaba3a5c15dbee7e85644c2cde3394c377f75
        fa0b7d3521fc4cec414dd017847e55be648ca5830a67513b49671e2115a312a3
        79de9910ee4bd9ad17f66045eb2e4c2bb0a05ef1db1929dfc3f93c41cee54285
        0ef02525efd2aac0f827baa601e5bed47d8f6857",
    );
    secret(&key);
    let srtp = rind.srtp_provider.aead_aes_128_gcm();
    let mut sealed = [0u8; 100 + 16];
    srtp.create_cipher(key, true)
        .encrypt(&iv, &aad, &input, &mut sealed)
        .unwrap();
    public(&sealed);
    assert_eq!(sealed[..], expected);
    let mut plaintext = [0u8; 100];
    let len = srtp
        .create_cipher(key, false)
        .decrypt(&iv, &[&aad], &sealed, &mut plaintext)
        .unwrap();
    public(&plaintext);
    assert_eq!(plaintext[..len], input);

    let key = [0x42; 32];
    let expected = hex(
        "a7384fb327d6aebdfc0cdf7bb5edd012681bccf8213779c4988a7dfb5998afe2
        177e9887e174d1d2ff18ce813e3efd3b4a73f3d74c52be147a3ae94f292a82d6
        51cac720952c713290144056b1ab821a3b42b5cf61eade5f176595f1f9c37c11
        75ca8e0a52fe99e8c90294a692c208a549380b09",
    );
    secret(&key);
    let srtp = rind.srtp_provider.aead_aes_256_gcm();
    srtp.create_cipher(key, true)
        .encrypt(&iv, &aad, &input, &mut sealed)
        .unwrap();
    public(&sealed);
    assert_eq!(sealed[..], expected);
    let len = srtp
        .create_cipher(key, false)
        .decrypt(&iv, &[&aad], &sealed, &mut plaintext)
        .unwrap();
    public(&plaintext);
    assert_eq!(plaintext[..len], input);
}

#[test]
fn stun_hmac() {
    let rind = rind();
    let key = *b"a STUN password";

    secret(&key);
    let tag = rind
        .sha1_hmac_provider
        .sha1_hmac(&key, &[b"binding ", b"request"]);
    public(&tag);
    assert_eq!(tag[..], hex("72401b789d07c4b41ddd3ddedf214a106c8720cb"));
}
