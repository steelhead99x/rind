//! RustCrypto's README examples for `sha2`, `sha3` and `hmac`, with only the
//! crate in each path swapped for its rind-digest module, so code written
//! against those crates builds here unchanged; each result is checked against
//! the crate's own.

#[test]
fn sha2_readme() {
    use rind_digest::sha2::{Digest, Sha256, Sha512};

    assert_eq!(
        Sha256::digest(b"hello world")[..],
        sha2::Sha256::digest(b"hello world")[..]
    );
    let mut hasher = Sha256::new();
    hasher.update(b"hello ");
    hasher.update(b"world");
    assert_eq!(
        hasher.finalize()[..],
        sha2::Sha256::digest(b"hello world")[..]
    );
    let mut hasher = Sha512::new();
    hasher.update(b"hello world");
    assert_eq!(
        hasher.finalize()[..],
        sha2::Sha512::digest(b"hello world")[..]
    );
}

#[test]
fn sha3_readme() {
    use rind_digest::sha3::{Digest, Sha3_256};

    let mut hasher = Sha3_256::new();
    hasher.update(b"abc");
    assert_eq!(hasher.finalize()[..], sha3::Sha3_256::digest(b"abc")[..]);
}

#[test]
fn hmac_readme() {
    use rind_digest::hmac::{Hmac, KeyInit, Mac};
    use rind_digest::sha2::Sha256;

    type HmacSha256 = Hmac<Sha256>;

    let theirs = {
        let mut mac = <hmac::Hmac<sha2::Sha256> as hmac::KeyInit>::new_from_slice(
            b"my secret and secure key",
        )
        .unwrap();
        hmac::Mac::update(&mut mac, b"input message");
        hmac::Mac::finalize(mac).into_bytes()
    };
    let mut mac = HmacSha256::new_from_slice(b"my secret and secure key")
        .expect("HMAC can take key of any size");
    mac.update(b"input message");
    let code_bytes = mac.clone().finalize().into_bytes();
    assert_eq!(code_bytes[..], theirs[..]);
    mac.verify_slice(&code_bytes[..]).unwrap();
}

/// The re-exports the crates make, which callers reach through them.
#[test]
fn reexports() {
    use rind_digest::hmac::{HmacReset, digest};
    use rind_digest::sha2::Sha384;
    use rind_digest::sha3::Digest as _;

    let mut mac = <HmacReset<Sha384> as rind_digest::hmac::KeyInit>::new_from_slice(b"k").unwrap();
    digest::Mac::update(&mut mac, b"m");
    let first = digest::Mac::finalize_reset(&mut mac).into_bytes();
    digest::Mac::update(&mut mac, b"m");
    assert_eq!(digest::Mac::finalize(mac).into_bytes(), first);
    let _: rind_digest::sha2::digest::Output<Sha384> = Sha384::digest(b"");
}
