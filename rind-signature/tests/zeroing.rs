//! Every signing key here wipes its whole value on drop, public key included,
//! as AGENTS.md requires of a key type: each is only rind's key pair, which
//! wipes itself, with no other copy of the key beside it.

use core::mem::size_of;
use core::ptr;
use std::alloc::{Layout, dealloc};

#[test]
fn ed25519() {
    use rind_signature::ed25519::SigningKey;
    assert_eq!(size_of::<SigningKey>(), size_of::<rind::ed25519::KeyPair>());
    check_zeroed_on_drop(Box::new(SigningKey::from_bytes(&[0x9d; 32])));
}

macro_rules! ecdsa {
    ($test:ident, $module:ident, $len:expr) => {
        #[test]
        fn $test() {
            use rind_signature::$module::ecdsa::SigningKey;
            assert_eq!(size_of::<SigningKey>(), size_of::<rind::ecdsa::KeyPair>());
            let mut scalar = [0x11u8; $len];
            scalar[0] = 0;
            check_zeroed_on_drop(Box::new(SigningKey::from_slice(&scalar).unwrap()));
        }
    };
}

ecdsa!(ecdsa_p256, p256, 32);
ecdsa!(ecdsa_p384, p384, 48);
ecdsa!(ecdsa_p521, p521, 66);

#[test]
fn ml_dsa() {
    use ml_dsa::{MlDsa44, MlDsa65, MlDsa87, Seed};
    use rind_signature::ml_dsa::{Params, SigningKey};
    fn check<P: Params>() {
        assert_eq!(
            size_of::<SigningKey<P>>(),
            size_of::<rind::ml_dsa::KeyPair<P::Rind>>()
        );
        let seed = Seed::try_from([0x5au8; 32].as_slice()).unwrap();
        check_zeroed_on_drop(Box::new(SigningKey::<P>::from_seed(&seed)));
    }
    check::<MlDsa44>();
    check::<MlDsa65>();
    check::<MlDsa87>();
}

#[test]
fn rsa() {
    use rind_signature::rsa::{pkcs1v15, pss};
    use rsa::pkcs8::DecodePrivateKey;
    type Hash = rind_digest::sha2::Sha256;
    let key = rsa::PrivateKey::from_pkcs8_der(include_bytes!("data/rsa2048.pkcs8.der")).unwrap();
    assert_eq!(
        size_of::<pkcs1v15::SigningKey<Hash>>(),
        size_of::<rind::rsa::KeyPair>()
    );
    assert_eq!(
        size_of::<pss::SigningKey<Hash>>(),
        size_of::<rind::rsa::KeyPair>()
    );
    check_zeroed_on_drop(Box::new(
        pkcs1v15::SigningKey::<Hash>::try_new(key.clone()).unwrap(),
    ));
    check_zeroed_on_drop(Box::new(pss::SigningKey::<Hash>::try_new(key).unwrap()));
}

/// Checks that dropping `value` zeroes every byte of it, public key included,
/// by dropping it in place and reading its memory before freeing it.
///
/// A deliberate read after drop, as `rind/tests/zeroing.rs` does: unsound in
/// principle, but deterministic, since nothing can reuse the allocation
/// before the read.
fn check_zeroed_on_drop<T>(value: Box<T>) {
    let len = size_of::<T>();
    assert_ne!(len, 0);
    let addr = Box::into_raw(value);
    let ptr = addr as *const u8;
    // SAFETY: `addr` came from a valid `Box<T>`, and is dropped only here.
    unsafe { ptr::drop_in_place(addr) };
    // SAFETY: the allocation is still live, and `len` bytes long.
    let after: Vec<u8> = (0..len)
        .map(|i| unsafe { ptr::read_volatile(ptr.add(i)) })
        .collect();
    // SAFETY: `addr` came from a `Box<T>`, so it was allocated with `T`'s layout.
    unsafe { dealloc(addr as *mut u8, Layout::new::<T>()) };
    if let Some(i) = after.iter().position(|&b| b != 0) {
        panic!("byte {i} of {len} was not cleared after drop: {after:02x?}");
    }
}
