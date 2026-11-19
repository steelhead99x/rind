//! Every hash and HMAC here against RustCrypto's own crate for the same
//! algorithm, on fixed and pseudo-random inputs and at the edges.
#![cfg(feature = "digest-0_11")]

use digest::{Digest, DynDigest, FixedOutputReset, KeyInit, Mac, Reset};

/// A fixed-seed generator, so a failure reproduces.
struct Xorshift(u64);

impl Xorshift {
    fn bytes(&mut self, len: usize) -> Vec<u8> {
        (0..len)
            .map(|_| {
                self.0 ^= self.0 << 13;
                self.0 ^= self.0 >> 7;
                self.0 ^= self.0 << 17;
                (self.0 >> 24) as u8
            })
            .collect()
    }
}

/// Lengths that straddle every block and padding boundary of the hashes here
/// (64, 72, 104, 128, 136), plus empty and a long one.
const LENGTHS: &[usize] = &[
    0, 1, 2, 55, 56, 63, 64, 65, 71, 72, 73, 103, 104, 105, 111, 112, 127, 128, 129, 135, 136, 137,
    255, 256, 257, 1000, 4096, 10_007,
];

fn digest_of<D: Digest>(data: &[u8]) -> Vec<u8> {
    D::digest(data).to_vec()
}

fn same_as_rustcrypto<Ours: Digest, Theirs: Digest>() {
    assert_eq!(
        <Ours as Digest>::output_size(),
        <Theirs as Digest>::output_size()
    );
    let mut rng = Xorshift(0x9e37_79b9_7f4a_7c15);
    for &len in LENGTHS {
        let data = rng.bytes(len);
        assert_eq!(
            digest_of::<Ours>(&data),
            digest_of::<Theirs>(&data),
            "{len} bytes"
        );
        // In pieces, however the message is cut.
        for cut in [0, 1, len / 3, len / 2, len.saturating_sub(1), len] {
            let cut = cut.min(len);
            let mut ours = Ours::new();
            Digest::update(&mut ours, &data[..cut]);
            Digest::update(&mut ours, &data[cut..]);
            assert_eq!(
                ours.finalize().to_vec(),
                digest_of::<Theirs>(&data),
                "{len} bytes cut at {cut}"
            );
        }
    }
}

macro_rules! hash_tests {
    ($($test:ident: $ours:ty, $theirs:ty;)*) => {$(
        #[test]
        fn $test() {
            same_as_rustcrypto::<$ours, $theirs>();
            clone_forks_and_reset_restarts::<$ours, $theirs>();
            dyn_digest::<$ours, $theirs>();
        }
    )*};
}

hash_tests! {
    sha256: rind_rustcrypto::sha2::Sha256, sha2::Sha256;
    sha384: rind_rustcrypto::sha2::Sha384, sha2::Sha384;
    sha512: rind_rustcrypto::sha2::Sha512, sha2::Sha512;
    sha512_256: rind_rustcrypto::sha2::Sha512_256, sha2::Sha512_256;
    sha3_256: rind_rustcrypto::sha3::Sha3_256, sha3::Sha3_256;
    sha3_384: rind_rustcrypto::sha3::Sha3_384, sha3::Sha3_384;
    sha3_512: rind_rustcrypto::sha3::Sha3_512, sha3::Sha3_512;
}

fn clone_forks_and_reset_restarts<Ours, Theirs>()
where
    Ours: Digest + Clone + Reset + FixedOutputReset,
    Theirs: Digest,
{
    let mut ours = Ours::new();
    Digest::update(&mut ours, b"shared prefix, ");
    // A clone forks the running hash: two messages share the prefix.
    let mut fork = ours.clone();
    Digest::update(&mut ours, b"one");
    Digest::update(&mut fork, b"two");
    assert_eq!(
        ours.finalize_reset().to_vec(),
        digest_of::<Theirs>(b"shared prefix, one")
    );
    // `finalize_reset` left it empty, so it hashes a fresh message.
    Digest::update(&mut ours, b"abc");
    assert_eq!(ours.finalize_reset().to_vec(), digest_of::<Theirs>(b"abc"));
    assert_eq!(
        fork.finalize().to_vec(),
        digest_of::<Theirs>(b"shared prefix, two")
    );
    // `reset` drops what was fed.
    Digest::update(&mut ours, b"discarded");
    Digest::reset(&mut ours);
    Digest::update(&mut ours, b"kept");
    assert_eq!(ours.finalize().to_vec(), digest_of::<Theirs>(b"kept"));
}

/// The object-safe form generic code often takes.
fn dyn_digest<Ours, Theirs>()
where
    Ours: Digest + Clone + Reset + FixedOutputReset + 'static,
    Theirs: Digest,
{
    let mut boxed: Box<dyn DynDigest> = Box::new(Ours::new());
    boxed.update(b"dyn ");
    boxed.update(b"digest");
    assert_eq!(
        &*boxed.finalize_reset(),
        digest_of::<Theirs>(b"dyn digest").as_slice()
    );
    assert_eq!(
        DynDigest::output_size(&*boxed),
        <Ours as Digest>::output_size()
    );
}

// One generic function per trait, instantiated with rind's types.
fn generic_digest<D: Digest>(data: &[u8]) -> Vec<u8> {
    let mut hasher = D::new();
    hasher.update(data);
    hasher.finalize().to_vec()
}

#[test]
fn a_generic_function_runs_on_rind() {
    let data = b"generic over Digest";
    assert_eq!(
        generic_digest::<rind_rustcrypto::sha2::Sha256>(data),
        generic_digest::<sha2::Sha256>(data)
    );
    assert_eq!(
        generic_digest::<rind_rustcrypto::sha3::Sha3_512>(data),
        generic_digest::<sha3::Sha3_512>(data)
    );
}

fn generic_mac<M: Mac + KeyInit>(key: &[u8], data: &[u8]) -> Vec<u8> {
    let mut mac = <M as KeyInit>::new_from_slice(key).expect("HMAC takes any key length");
    Mac::update(&mut mac, data);
    mac.finalize().into_bytes().to_vec()
}

macro_rules! hmac_tests {
    ($($test:ident: $hash:ident;)*) => {$(
        #[test]
        fn $test() {
            type Ours = rind_rustcrypto::hmac::Hmac<rind_rustcrypto::sha2::$hash>;
            type Theirs = hmac::Hmac<sha2::$hash>;
            let mut rng = Xorshift(0xd1b5_4a32_d192_ed03);
            let block = <rind_rustcrypto::sha2::$hash as digest::common::BlockSizeUser>::block_size();
            // Keys around the block size, which HMAC hashes when it is longer,
            // and the empty key.
            for key_len in [0, 1, 20, block - 1, block, block + 1, 2 * block + 3, 1000] {
                let key = rng.bytes(key_len);
                for &len in &[0usize, 1, 63, 64, 65, 127, 128, 129, 1000] {
                    let data = rng.bytes(len);
                    assert_eq!(
                        generic_mac::<Ours>(&key, &data),
                        generic_mac::<Theirs>(&key, &data),
                        "key {key_len} bytes, message {len}"
                    );
                }
            }
        }
    )*};
}

hmac_tests! {
    hmac_sha256: Sha256;
    hmac_sha384: Sha384;
    hmac_sha512: Sha512;
}

#[test]
fn hmac_verifies_and_refuses_as_rustcrypto_does() {
    use rind_rustcrypto::{hmac::Hmac, sha2::Sha256};
    let key = b"a key";
    let mut ours = <Hmac<Sha256> as KeyInit>::new_from_slice(key).unwrap();
    Mac::update(&mut ours, b"message");
    let tag = ours.clone().finalize().into_bytes();
    // Right tag, wrong tag, truncated and extended tags.
    assert!(ours.clone().verify(&tag).is_ok());
    let mut wrong = tag;
    wrong[0] ^= 1;
    assert!(ours.clone().verify(&wrong).is_err());
    assert!(ours.clone().verify_slice(&tag[..31]).is_err());
    assert!(
        ours.clone()
            .verify_slice(&[tag.as_slice(), &[0]].concat())
            .is_err()
    );
    assert!(ours.clone().verify_slice(&tag).is_ok());
    // A truncated tag is accepted only through `verify_truncated_left`, as for
    // RustCrypto's own.
    assert!(ours.clone().verify_truncated_left(&tag[..16]).is_ok());
    // Reset forgets the message and keeps the key.
    let mut reused = ours.clone();
    Reset::reset(&mut reused);
    Mac::update(&mut reused, b"message");
    assert_eq!(reused.finalize().into_bytes(), tag);
    // `finalize_reset` returns the tag and starts again under the same key.
    let mut resetting = ours;
    assert_eq!(Mac::finalize_reset(&mut resetting).into_bytes(), tag);
    Mac::update(&mut resetting, b"message");
    assert_eq!(resetting.finalize().into_bytes(), tag);
}
