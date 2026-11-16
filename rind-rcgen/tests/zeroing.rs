//! Checks that the PKCS#8 copy a rind-rcgen `KeyPair` keeps on the heap,
//! beyond the rind key it wraps, is wiped before it is freed.
//!
//! This uses rind-aws-lc-rs's method: an allocator that, while armed with a
//! secret, counts each freed block still holding it. Like that test, it
//! reads blocks as they are freed, which is not sound in theory;
//! `detects_a_leak` checks that it catches a leak in practice.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use rcgen::{PKCS_ED25519, PKCS_RSA_SHA256, SignatureAlgorithm};
use rind_rcgen::KeyPair;
use rustls_pki_types::PrivatePkcs8KeyDer;

/// How many bytes of a secret the allocator looks for.
const NEEDLE_LEN: usize = 16;

/// The secret being watched for, if any.
static NEEDLE: Mutex<Option<[u8; NEEDLE_LEN]>> = Mutex::new(None);
/// Blocks freed while still holding the needle.
static LEAKS: AtomicUsize = AtomicUsize::new(0);

struct Scan;

// SAFETY: forwards every call to `System`, and only reads a block it is
// about to free; the module documentation explains what that read risks.
unsafe impl GlobalAlloc for Scan {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller's contract, passed on.
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // Locking allocates nothing, so this cannot recurse.
        if let Some(needle) = *NEEDLE.lock().unwrap_or_else(|e| e.into_inner()) {
            // The last `NEEDLE_LEN` bytes read, oldest first.
            let mut window = [0u8; NEEDLE_LEN];
            for i in 0..layout.size() {
                window.copy_within(1.., 0);
                // SAFETY: `ptr` is `layout.size()` bytes that `System` keeps
                // allocated until the call below.
                window[NEEDLE_LEN - 1] = unsafe { ptr.add(i).read_volatile() };
                if i + 1 >= NEEDLE_LEN && window == needle {
                    LEAKS.fetch_add(1, Ordering::Relaxed);
                    break;
                }
            }
        }
        // SAFETY: the caller's contract, passed on.
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static ALLOCATOR: Scan = Scan;

/// Serializes the tests, which share the allocator's needle.
static SERIAL: Mutex<()> = Mutex::new(());

/// Counts the blocks freed while `drop` runs that still hold the first
/// bytes of `secret`.
fn leaks(secret: &[u8], drop: impl FnOnce()) -> usize {
    let _serial = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let needle = secret[..NEEDLE_LEN].try_into().unwrap();
    LEAKS.store(0, Ordering::Relaxed);
    *NEEDLE.lock().unwrap() = Some(needle);
    drop();
    *NEEDLE.lock().unwrap() = None;
    LEAKS.load(Ordering::Relaxed)
}

/// Bytes unlikely to appear anywhere else.
fn distinct<const N: usize>(start: u8) -> [u8; N] {
    core::array::from_fn(|i| start.wrapping_add((i as u8).wrapping_mul(29)))
}

/// The check sees a secret left on the heap, so a clean result means something.
#[test]
fn detects_a_leak() {
    let secret: [u8; 32] = distinct(1);
    let copy = secret.to_vec();
    assert_eq!(leaks(&secret, || drop(copy)), 1);
}

/// Loads `pkcs8`, signs with it, and drops it, counting the freed blocks
/// that still hold `secret`. The caller's own copy outlives the count.
fn load_and_drop(pkcs8: &[u8], alg: &'static SignatureAlgorithm, secret: &[u8]) -> usize {
    let der = PrivatePkcs8KeyDer::from(pkcs8);
    leaks(secret, || {
        let key = KeyPair::from_pkcs8_der_and_sign_algo(&der, alg).unwrap();
        rcgen::SigningKey::sign(&key, b"message").unwrap();
        assert_eq!(key.serialized_der(), pkcs8);
    })
}

#[test]
fn ed25519() {
    let seed: [u8; 32] = distinct(3);
    // RFC 8410's PKCS#8 v1 prefix for an Ed25519 seed.
    let mut pkcs8 = vec![
        0x30, 0x2e, 0x02, 0x01, 0x00, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x04, 0x22, 0x04,
        0x20,
    ];
    pkcs8.extend_from_slice(&seed);
    assert_eq!(load_and_drop(&pkcs8, &PKCS_ED25519, &seed), 0);
}

#[test]
fn rsa() {
    let pkcs8 = include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der");
    // The last bytes are the CRT coefficient, which only the private key holds.
    let secret = &pkcs8[pkcs8.len() - NEEDLE_LEN..];
    assert_eq!(load_and_drop(pkcs8, &PKCS_RSA_SHA256, secret), 0);
}

/// `zeroize` clears the PKCS#8 copy at once, as rcgen's does.
#[cfg(feature = "zeroize")]
#[test]
fn zeroize_clears() {
    use zeroize::Zeroize;
    let seed: [u8; 32] = distinct(5);
    let mut pkcs8 = vec![
        0x30, 0x2e, 0x02, 0x01, 0x00, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x04, 0x22, 0x04,
        0x20,
    ];
    pkcs8.extend_from_slice(&seed);
    let der = PrivatePkcs8KeyDer::from(pkcs8.as_slice());
    let mut key = KeyPair::from_pkcs8_der_and_sign_algo(&der, &PKCS_ED25519).unwrap();
    key.zeroize();
    assert!(key.serialized_der().is_empty());
}
