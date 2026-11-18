// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ChaCha20-Poly1305 in one pass: pyca/verified-garbage's SVE2 routines,
//! imported by `admin/import-vg`, where the CPU has SVE2, and otherwise
//! aws-lc's `chacha20_poly1305_armv8`, which interleaves NEON ChaCha20 with
//! scalar Poly1305, imported by `admin/import-aws-lc`, since VG's NEON
//! routines took up to 1.06 of its time at 32 to 512 bytes on Apple's M4.
//!
//! VG proves in Lean that its routines meet RFC 8439 and take the same
//! branches and memory addresses whatever the key, nonce, and data. Those
//! proofs rest on VG's models of the instructions, which nothing yet checks
//! against a CPU, so rind claims no proof of them until they are
//! cosimulated. The aws-lc assembly is not formally verified: its
//! correctness rests on its use and testing in BoringSSL and aws-lc. rind
//! tests both against RFC 8439, Wycheproof, aws-lc-rs, and separate
//! ChaCha20 and Poly1305 passes.
//!
//! VG's routines zero their stack scratch before returning, which AGENTS.md
//! allows an imported proven routine: VG defines each routine with that
//! wipe, offers none without it, and its proofs are of the instructions as
//! emitted. They outrun aws-lc's code at every size with that cost included.

use super::cpu::HaveSve2;
use super::vg::vg_chacha20_poly1305_open_sve2::vg_chacha20_poly1305_open_sve2;
use super::vg::vg_chacha20_poly1305_seal_sve2::vg_chacha20_poly1305_seal_sve2;
use crate::low::ct_equal;

/// Encrypts `inout` in place, returning the tag over `aad` and the ciphertext.
pub(crate) fn seal(key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], inout: &mut [u8]) -> [u8; 16] {
    match HaveSve2::check() {
        Some(sve2) => seal_sve2(sve2, key, nonce, aad, inout),
        None => seal_neon(key, nonce, aad, inout),
    }
}

/// Decrypts `inout` in place, and returns whether `tag` is its tag over
/// `aad` and the ciphertext, a secret.
pub(crate) fn open(
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    inout: &mut [u8],
    tag: &[u8; 16],
) -> bool {
    match HaveSve2::check() {
        Some(sve2) => open_sve2(sve2, key, nonce, aad, inout, tag),
        None => ct_equal(&open_neon(key, nonce, aad, inout), tag),
    }
}

fn seal_sve2(
    _: HaveSve2,
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    inout: &mut [u8],
) -> [u8; 16] {
    let mut tag = [0u8; 16];
    let (data, len) = (inout.as_mut_ptr(), inout.len());
    // SAFETY: each pointer is to a distinct Rust object of the length the
    // routine reads or writes, and the token proves SVE2.
    unsafe {
        asm_call!(unsafe extern "C" vg_chacha20_poly1305_seal_sve2(key, nonce, aad.as_ptr(), aad.len(), data, len, &mut tag))
    };
    tag
}

/// As `open`, and zeroes `inout` when `tag` is not its tag.
fn open_sve2(
    _: HaveSve2,
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    inout: &mut [u8],
    tag: &[u8; 16],
) -> bool {
    let (data, len) = (inout.as_mut_ptr(), inout.len());
    // SAFETY: as in `seal_sve2`.
    let valid = unsafe {
        asm_call!(unsafe extern "C" vg_chacha20_poly1305_open_sve2(key, nonce, aad.as_ptr(), aad.len(), data, len, tag))
    };
    valid == 1
}

fn seal_neon(key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], inout: &mut [u8]) -> [u8; 16] {
    let mut data = Data::new(key, nonce);
    let ptr = inout.as_mut_ptr();
    // SAFETY: `inout` is `inout.len()` readable and writable bytes, which the
    // routine allows to alias exactly, `aad` is `aad.len()` readable bytes,
    // and `data` is the block it reads and writes. rind requires NEON.
    unsafe {
        asm_call!(unsafe extern "C" chacha20_poly1305_seal(ptr, ptr, inout.len(), aad.as_ptr(), aad.len(), &mut data))
    };
    data.tag()
}

/// Decrypts `inout` in place, returning the tag over `aad` and the
/// ciphertext.
fn open_neon(key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], inout: &mut [u8]) -> [u8; 16] {
    let mut data = Data::new(key, nonce);
    let ptr = inout.as_mut_ptr();
    // SAFETY: as in `seal_neon`.
    unsafe {
        asm_call!(unsafe extern "C" chacha20_poly1305_open(ptr, ptr, inout.len(), aad.as_ptr(), aad.len(), &mut data))
    };
    data.tag()
}

/// The routines' argument block: aws-lc's `chacha20_poly1305_seal_data`,
/// whose first 48 bytes are its `chacha20_poly1305_open_data`. On return,
/// the tag overwrites the start of the key.
#[repr(C, align(16))]
struct Data {
    key: [u8; 32],
    counter: u32,
    nonce: [u8; 12],
    extra_ciphertext: *const u8,
    extra_ciphertext_len: usize,
}

impl Data {
    fn new(key: &[u8; 32], nonce: &[u8; 12]) -> Self {
        Self {
            key: *key,
            // Block 0 keys Poly1305.
            counter: 0,
            nonce: *nonce,
            extra_ciphertext: core::ptr::null(),
            extra_ciphertext_len: 0,
        }
    }

    fn tag(&self) -> [u8; 16] {
        let mut tag = [0u8; 16];
        tag.copy_from_slice(&self.key[..16]);
        tag
    }
}

/// The ChaCha20 constant, the counter increments, a rotation mask, and the
/// Poly1305 clamp, which the routines load at once.
#[repr(C, align(128))]
struct Consts([u8; 64]);

static CHACHA20_CONSTS: Consts = Consts(include!(
    "aws_lc/chacha20_poly1305_armv8.chacha20_consts.rs"
));

/// Defines a naked function running an imported routine, which reaches its
/// table and helper through the `sym` operands listed.
macro_rules! routine {
    ($name:ident($($arg:ident: $ty:ty),*) { $($op:ident = $sym:ident),* }) => {
        #[unsafe(naked)]
        unsafe extern "C" fn $name($($arg: $ty),*) {
            #[cfg(not(target_vendor = "apple"))]
            core::arch::naked_asm!(
                include_str!(concat!("aws_lc/", stringify!($name), ".linux.s"))
                $(, $op = sym $sym)*
            );
            #[cfg(target_vendor = "apple")]
            core::arch::naked_asm!(
                include_str!(concat!("aws_lc/", stringify!($name), ".apple.s"))
                $(, $op = sym $sym)*
            );
        }
    };
}

routine!(chacha20_poly1305_seal(
    out: *mut u8,
    input: *const u8,
    len: usize,
    aad: *const u8,
    aad_len: usize,
    data: *mut Data
) {
    chacha20_consts = CHACHA20_CONSTS,
    poly_hash_ad_internal = poly_hash_ad_internal
});
routine!(chacha20_poly1305_open(
    out: *mut u8,
    input: *const u8,
    len: usize,
    aad: *const u8,
    aad_len: usize,
    data: *mut Data
) {
    chacha20_consts = CHACHA20_CONSTS,
    poly_hash_ad_internal = poly_hash_ad_internal
});

// Hashes the AAD into the Poly1305 state the routines keep in registers, so
// only they call it.
routine!(poly_hash_ad_internal() { poly_hash_ad_internal = poly_hash_ad_internal });

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::ct;
    use crate::low::generic::chacha20poly1305 as separate;

    type Seal = fn(&[u8; 32], &[u8; 12], &[u8], &mut [u8]) -> [u8; 16];
    type Open = fn(&[u8; 32], &[u8; 12], &[u8], &mut [u8], &[u8; 16]) -> bool;

    /// Each one-pass path the CPU can run, by name.
    fn paths() -> Vec<(&'static str, Seal, Open)> {
        let mut paths: Vec<(&'static str, Seal, Open)> =
            vec![("neon", seal_neon, |key, nonce, aad, inout, tag| {
                ct_equal(&open_neon(key, nonce, aad, inout), tag)
            })];
        if HaveSve2::check().is_some() {
            paths.push((
                "sve2",
                |key, nonce, aad, inout| {
                    seal_sve2(HaveSve2::check().unwrap(), key, nonce, aad, inout)
                },
                |key, nonce, aad, inout, tag| {
                    open_sve2(HaveSve2::check().unwrap(), key, nonce, aad, inout, tag)
                },
            ));
        }
        paths
    }

    // Every message length through the routines' blocks and the tails after
    // them, AAD lengths around their 16-byte blocks, and a long message, on
    // each path, against separate ChaCha20 and Poly1305 passes, under a key
    // `admin/ctgrind` keeps secret, and opening under a tag one bit off.
    // Valgrind hides SVE2, so ctgrind checks only aws-lc's routines, and
    // `ct_qemu_chacha20poly1305` VG's.
    #[test]
    fn matches_separate_passes() {
        let key = core::array::from_fn(|i| i as u8);
        ct::secret_slice(&key);
        let nonce = core::array::from_fn(|i| (i * 7) as u8);
        let input: Vec<u8> = (0..16384 + 15).map(|i| (i * 13 + 5) as u8).collect();
        let lens = (0..=1100)
            .map(|len| (len, 13))
            .chain((0..=48).map(|aad| (300, aad)));
        for (len, aad_len) in lens.chain([(16384 + 15, 13)]) {
            let aad = &input[..aad_len];
            let mut sealed = input[..len].to_vec();
            let tag = ct::into_public(separate::seal(&key, &nonce, aad, &mut sealed));
            ct::public_slice(&sealed);
            for (path, seal, open) in paths() {
                let mut ours = input[..len].to_vec();
                let ours_tag = ct::into_public(seal(&key, &nonce, aad, &mut ours));
                ct::public_slice(&ours);
                assert_eq!(
                    ours_tag, tag,
                    "{path} seal tag, {len} bytes, {aad_len} of AAD"
                );
                assert_eq!(ours, sealed, "{path} seal, {len} bytes, {aad_len} of AAD");
                let valid = ct::into_public(open(&key, &nonce, aad, &mut ours, &tag));
                ct::public_slice(&ours);
                assert!(valid, "{path} open, {len} bytes, {aad_len} of AAD");
                assert_eq!(
                    ours,
                    input[..len],
                    "{path} open, {len} bytes, {aad_len} of AAD"
                );

                let mut wrong = tag;
                wrong[len % 16] ^= 1 << (len % 8);
                let mut forged = sealed.clone();
                let valid = ct::into_public(open(&key, &nonce, aad, &mut forged, &wrong));
                assert!(!valid, "{path} forged, {len} bytes, {aad_len} of AAD");
            }
        }
    }

    // Valgrind hides SVE2, so `admin/ctgrind` never reaches VG's routines;
    // `admin/ct-qemu` traces them here instead, under qemu-aarch64's `max`
    // CPU, with a secret key, nonce, AAD, message, and tag, opening under
    // the right tag and a wrong one, which only the result may tell apart.
    // The routines branch on the lengths into size-specialized kernels and
    // tails. These lengths reach every basic block, of both routines and
    // their callees, that qemu's exec log saw in 3,471 sampled pairs of
    // lengths (messages to 8 KiB, AAD to 600 bytes), sealed, opened, and
    // forged.
    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_chacha20poly1305() {
        use crate::low::aarch64::ct_qemu;

        let sve2 = HaveSve2::check().expect("SVE2");
        let seed = ct_qemu::seed().to_le_bytes();
        let bytes = |n| seed.iter().cycle().take(n).copied().collect::<Vec<u8>>();
        let key = bytes(32).try_into().unwrap();
        let nonce = bytes(12).try_into().unwrap();
        let wrong = bytes(16).try_into().unwrap();
        for (aad_len, msg_len) in [
            (29, 43),
            (4, 262),
            (13, 322),
            (2, 459),
            (3, 520),
            (13, 768),
            (13, 769),
            (13, 896),
            (13, 960),
            (9, 1028),
            (13, 1088),
            (13, 1090),
            (3, 1351),
        ] {
            let aad = bytes(aad_len);
            let mut msg = bytes(msg_len);
            let tag = ct_qemu::traced(|| seal_sve2(sve2, &key, &nonce, &aad, &mut msg));
            assert!(ct_qemu::traced(|| open_sve2(
                sve2, &key, &nonce, &aad, &mut msg, &tag
            )));
            assert!(!ct_qemu::traced(|| open_sve2(
                sve2, &key, &nonce, &aad, &mut msg, &wrong
            )));
        }
    }
}
