//! Every provider operation agrees with str0m's aws-lc-rs provider.

use str0m::crypto::{AeadAes128Gcm, Aes128CmSha1_80, CryptoProvider};

fn providers() -> (CryptoProvider, CryptoProvider) {
    (
        rind_str0m::default_provider(),
        str0m_aws_lc_rs::default_provider(),
    )
}

/// A fixed-seed xorshift, so a failure reproduces.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn bytes(&mut self, len: usize) -> Vec<u8> {
        (0..len).map(|_| self.next() as u8).collect()
    }

    fn array<const N: usize>(&mut self) -> [u8; N] {
        std::array::from_fn(|_| self.next() as u8)
    }
}

// Every length up to a few blocks past a full packet, so partial blocks and
// the eight-block batches both get covered.
const LENGTHS: std::ops::Range<usize> = 0..300;
const MTU: usize = 1500;

fn lengths(rng: &mut Rng) -> impl Iterator<Item = usize> + '_ {
    LENGTHS.chain((0..50).map(|_| rng.below(MTU)))
}

#[test]
fn aes_cm() {
    let (rind, aws) = providers();
    let mut rng = Rng(1);
    for len in lengths(&mut Rng(2)) {
        let key = rng.array();
        let iv = Aes128CmSha1_80::rtp_iv(rng.array(), rng.next() as u32, rng.next() >> 16);
        let input = rng.bytes(len);

        let mut ours = vec![0u8; len];
        let mut theirs = vec![0u8; len + 16];
        let srtp = rind.srtp_provider.aes_128_cm_sha1_80();
        srtp.create_cipher(key, true)
            .encrypt(&iv, &input, &mut ours)
            .unwrap();
        aws.srtp_provider
            .aes_128_cm_sha1_80()
            .create_cipher(key, true)
            .encrypt(&iv, &input, &mut theirs)
            .unwrap();
        assert_eq!(ours, theirs[..len], "len {len}");

        let mut back = vec![0u8; len];
        srtp.create_cipher(key, false)
            .decrypt(&iv, &ours, &mut back)
            .unwrap();
        assert_eq!(back, input);
    }
}

/// The counter carries out of the low bits as RFC 3711's `IV + i mod 2^128`
/// does, for IVs str0m never makes.
#[test]
fn aes_cm_counter_carry() {
    let (rind, aws) = providers();
    let key = [0x42; 16];
    for low in [0xffff_u128, u32::MAX.into(), u64::MAX.into(), u128::MAX] {
        let iv = (0x0123_4567_89ab_cdef_0123_4567_89ab_cdef_u128 | low).to_be_bytes();
        let input = [0x11; 100];
        let (mut ours, mut theirs) = ([0u8; 100], [0u8; 100]);
        rind.srtp_provider
            .aes_128_cm_sha1_80()
            .create_cipher(key, true)
            .encrypt(&iv, &input, &mut ours)
            .unwrap();
        aws.srtp_provider
            .aes_128_cm_sha1_80()
            .create_cipher(key, true)
            .encrypt(&iv, &input, &mut theirs)
            .unwrap();
        assert_eq!(ours, theirs, "low bits {low:x}");
    }
}

#[test]
fn aes_gcm() {
    let (rind, aws) = providers();
    let mut rng = Rng(3);
    for len in lengths(&mut Rng(4)) {
        let iv = AeadAes128Gcm::rtp_iv(rng.array(), rng.next() as u32, rng.next() as u32, 7);
        // aws-lc-rs's provider asserts SRTP's minimum 12-byte AAD.
        let aad_len = 12 + rng.below(40);
        let aad = rng.bytes(aad_len);
        let split = rng.below(aad.len() + 1);
        let aads: [&[u8]; 2] = [&aad[..split], &aad[split..]];
        let input = rng.bytes(len);

        let mut ours = vec![0u8; len + 16];
        let mut theirs = vec![0u8; len + 16];
        let mut plain = vec![0u8; len];

        let key = rng.array();
        let (r, a) = (
            rind.srtp_provider.aead_aes_128_gcm(),
            aws.srtp_provider.aead_aes_128_gcm(),
        );
        r.create_cipher(key, true)
            .encrypt(&iv, &aad, &input, &mut ours)
            .unwrap();
        a.create_cipher(key, true)
            .encrypt(&iv, &aad, &input, &mut theirs)
            .unwrap();
        assert_eq!(ours, theirs, "AES-128 len {len}");
        let n = r
            .create_cipher(key, false)
            .decrypt(&iv, &aads, &theirs, &mut plain)
            .unwrap();
        assert_eq!(plain[..n], input);

        let key = rng.array();
        let (r, a) = (
            rind.srtp_provider.aead_aes_256_gcm(),
            aws.srtp_provider.aead_aes_256_gcm(),
        );
        r.create_cipher(key, true)
            .encrypt(&iv, &aad, &input, &mut ours)
            .unwrap();
        a.create_cipher(key, true)
            .encrypt(&iv, &aad, &input, &mut theirs)
            .unwrap();
        assert_eq!(ours, theirs, "AES-256 len {len}");
        let n = r
            .create_cipher(key, false)
            .decrypt(&iv, &aads, &theirs, &mut plain)
            .unwrap();
        assert_eq!(plain[..n], input);
    }
}

#[test]
fn key_derivation_rounds() {
    let (rind, aws) = providers();
    let mut rng = Rng(5);
    for _ in 0..100 {
        let input = rng.bytes(16);
        let key128 = rng.bytes(16);
        let key256 = rng.bytes(32);
        let (mut ours, mut theirs) = ([0u8; 32], [0u8; 32]);

        rind.srtp_provider
            .srtp_aes_128_ecb_round(&key128, &input, &mut ours);
        aws.srtp_provider
            .srtp_aes_128_ecb_round(&key128, &input, &mut theirs);
        assert_eq!(ours[..16], theirs[..16]);

        rind.srtp_provider
            .srtp_aes_256_ecb_round(&key256, &input, &mut ours);
        aws.srtp_provider
            .srtp_aes_256_ecb_round(&key256, &input, &mut theirs);
        assert_eq!(ours[..16], theirs[..16]);
    }
}

#[test]
fn hashes() {
    let (rind, aws) = providers();
    let mut rng = Rng(6);
    for len in lengths(&mut Rng(7)) {
        let data = rng.bytes(len);
        assert_eq!(
            rind.sha1_provider.sha1(&data),
            aws.sha1_provider.sha1(&data)
        );
        assert_eq!(
            rind.sha256_provider.sha256(&data),
            aws.sha256_provider.sha256(&data)
        );

        // Keys longer than SHA-1's 64-byte block are hashed first.
        let key_len = rng.below(100);
        let key = rng.bytes(key_len);
        let split = rng.below(len + 1);
        let payloads: [&[u8]; 3] = [&data[..split], &[], &data[split..]];
        assert_eq!(
            rind.sha1_hmac_provider.sha1_hmac(&key, &payloads),
            aws.sha1_hmac_provider.sha1_hmac(&key, &[&data]),
        );
    }
}
