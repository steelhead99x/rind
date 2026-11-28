#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;
#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
#[cfg(not(target_arch = "xtensa"))]
mod ossl_aead;

#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use common::{AEAD_ROWS, Aead, Dit, QUIC_AAD, dit};

#[cfg(not(target_arch = "xtensa"))]
const NONCE: [u8; 12] = [0; 12];

/// The AEAD rows, then QUIC's ACK-sized packets under its 13 B short header.
#[cfg(not(target_arch = "xtensa"))]
const ROWS: [Aead; 9] = [
    AEAD_ROWS[0],
    AEAD_ROWS[1],
    AEAD_ROWS[2],
    AEAD_ROWS[3],
    AEAD_ROWS[4],
    AEAD_ROWS[5],
    AEAD_ROWS[6],
    Aead::new(32, "quic-32B", QUIC_AAD),
    Aead::new(64, "quic-64B", QUIC_AAD),
];

#[cfg(not(target_arch = "xtensa"))]
fn test_ring_aes_gcm(key: &ring::aead::LessSafeKey, nonce: &[u8; 12], aad: &[u8], buf: &mut [u8]) {
    let _tag = key
        .seal_in_place_separate_tag(
            ring::aead::Nonce::assume_unique_for_key(*nonce),
            ring::aead::Aad::from(aad),
            buf,
        )
        .unwrap();
}

#[cfg(not(target_arch = "xtensa"))]
fn test_aws_aes_gcm(
    key: &aws_lc_rs::aead::LessSafeKey,
    nonce: &[u8; 12],
    aad: &[u8],
    buf: &mut [u8],
) {
    let _tag = key
        .seal_in_place_separate_tag(nonce.into(), aws_lc_rs::aead::Aad::from(aad), buf)
        .unwrap();
}

#[cfg(not(target_arch = "xtensa"))]
fn test_rc_aes128_gcm(key: &aes_gcm::Aes128Gcm, nonce: &[u8; 12], aad: &[u8], buf: &mut [u8]) {
    use aes_gcm::AeadInOut;
    let _tag = key
        .encrypt_inout_detached(nonce.into(), aad, buf.into())
        .unwrap();
}

#[cfg(not(target_arch = "xtensa"))]
fn test_rc_aes256_gcm(key: &aes_gcm::Aes256Gcm, nonce: &[u8; 12], aad: &[u8], buf: &mut [u8]) {
    use aes_gcm::AeadInOut;
    let _tag = key
        .encrypt_inout_detached(nonce.into(), aad, buf.into())
        .unwrap();
}

#[cfg(not(target_arch = "xtensa"))]
fn test_rind_aes_gcm(key: &rind::aead::Key, nonce: &[u8; 12], aad: &[u8], buf: &mut [u8]) {
    let _tag = key
        .seal_in_place_separate_tag(rind::aead::Nonce::assume_unique_for_key(*nonce), aad, buf)
        .unwrap();
}

/// A key and the buffer it seals in place each call: the same buffer, so a
/// call times the cipher alone, without an allocation or a copy of the input.
#[cfg(not(target_arch = "xtensa"))]
struct Seal<K> {
    key: K,
    aad: &'static [u8],
    buf: Vec<u8>,
}

#[cfg(not(target_arch = "xtensa"))]
impl<K> Seal<K> {
    fn new(key: K, row: Aead) -> Self {
        Self {
            key,
            aad: row.aad,
            buf: row.size.zeros(),
        }
    }
}

/// A key, with the tag it opens under, and a ciphertext rind sealed under
/// the same key. Opening consumes its ciphertext, so each call first copies
/// it into a buffer a whole number of 4 KiB pages after it. Two separate
/// heap buffers can instead land with the destination just past the source
/// in a page, where Zen 3 and 4 run the `rep movsb` that glibc's memcpy can
/// pick for 16 KB about 30x slower.
#[cfg(not(target_arch = "xtensa"))]
struct Open<K> {
    key: K,
    aad: &'static [u8],
    buf: Vec<u8>,
    stride: usize,
}

#[cfg(not(target_arch = "xtensa"))]
impl<K> Open<K> {
    /// Seals `row` with rind under `alg` and `key`, then makes the row's key
    /// from the tag.
    fn new(
        row: Aead,
        alg: &'static rind::aead::Algorithm,
        key: &[u8],
        make: impl FnOnce([u8; 16]) -> K,
    ) -> Self {
        let stride = row.len().next_multiple_of(4096);
        let mut buf = vec![0; stride + row.len()];
        let tag = rind::aead::Key::new(alg, key)
            .unwrap()
            .seal_in_place_separate_tag(
                rind::aead::Nonce::assume_unique_for_key(NONCE),
                row.aad,
                &mut buf[..row.len()],
            )
            .unwrap();
        Self {
            key: make(tag.as_ref().try_into().unwrap()),
            aad: row.aad,
            buf,
            stride,
        }
    }

    /// The key, the ciphertext, and the buffer it is opened in.
    fn parts(&mut self) -> (&mut K, &[u8], &mut [u8]) {
        let (ct, pt) = self.buf.split_at_mut(self.stride);
        (&mut self.key, &ct[..pt.len()], pt)
    }
}

/// verified-garbage's sealing key, after checking its ciphertext and tag
/// match rind's.
#[cfg(not(target_arch = "xtensa"))]
fn vg_seal(
    key: &[u8],
    ours: &'static rind::aead::Algorithm,
    row: Aead,
) -> Seal<verified_garbage::aead::aes_gcm::AesGcm> {
    let vg = verified_garbage::aead::aes_gcm::AesGcm::new(key).unwrap();
    let mut expect = row.size.zeros();
    let tag = rind::aead::Key::new(ours, key)
        .unwrap()
        .seal_in_place_separate_tag(
            rind::aead::Nonce::assume_unique_for_key(NONCE),
            row.aad,
            &mut expect,
        )
        .unwrap();
    let mut ct = row.size.zeros();
    assert_eq!(
        vg.encrypt_in_place(&NONCE, row.aad, &mut ct).unwrap(),
        tag.as_ref()
    );
    assert_eq!(ct, expect);
    Seal::new(vg, row)
}

/// verified-garbage's opening key, after checking it opens what rind sealed.
#[cfg(not(target_arch = "xtensa"))]
fn vg_open(
    key: &[u8],
    ours: &'static rind::aead::Algorithm,
    row: Aead,
) -> Open<(verified_garbage::aead::aes_gcm::AesGcm, [u8; 16])> {
    let vg = verified_garbage::aead::aes_gcm::AesGcm::new(key).unwrap();
    let mut open = Open::new(row, ours, key, |tag| (vg, tag));
    let ((vg, tag), ct, pt) = open.parts();
    pt.copy_from_slice(ct);
    vg.decrypt_in_place(&NONCE, row.aad, pt, tag).unwrap();
    assert!(pt.iter().all(|&x| x == 0));
    open
}

#[cfg(not(target_arch = "xtensa"))]
fn verified_garbage_open(open: &mut Open<(verified_garbage::aead::aes_gcm::AesGcm, [u8; 16])>) {
    let aad = open.aad;
    let ((key, tag), ct, pt) = open.parts();
    pt.copy_from_slice(ct);
    key.decrypt_in_place(&NONCE, aad, pt, tag).unwrap();
}

/// Sealing, then expanding a key and its GHASH table, as each QUIC
/// connection and derived track key pays. Each call drops its key, so the
/// key's wiping is timed too. Every path names its crate from the root,
/// since the key rows' modules take the libraries' names.
macro_rules! seal {
    (
        $len:literal,
        $alg:ident,
        $rustcrypto:ty,
        $test_rustcrypto:ident,
        $libcrux:ident,
        $libcrux_nonce:ident,
        $libcrux_tag:ident,
        $openssl:ident
    ) => {
        const KEY: [u8; $len] = [0; $len];

        pub mod ring {
            use swole::bench;

            use super::*;

            #[bench]
            fn key() {
                black_box(
                    ::ring::aead::UnboundKey::new(&::ring::aead::$alg, black_box(&KEY)).unwrap(),
                );
            }
        }

        pub mod aws_lc_rs {
            use swole::bench;

            use super::*;

            #[bench]
            fn key() {
                black_box(
                    ::aws_lc_rs::aead::UnboundKey::new(&::aws_lc_rs::aead::$alg, black_box(&KEY))
                        .unwrap(),
                );
            }
        }

        pub mod rind {
            use swole::bench;

            use super::*;

            #[bench(setup = dit)]
            fn key(_: &Dit<()>) {
                black_box(::rind::aead::Key::new(&::rind::aead::$alg, black_box(&KEY)).unwrap());
            }
        }

        pub mod verified_garbage {
            use swole::bench;

            use super::*;

            #[bench]
            fn key() {
                black_box(::verified_garbage::aead::aes_gcm::AesGcm::new(black_box(&KEY)).unwrap());
            }
        }

        #[cfg(target_arch = "aarch64")]
        pub mod verified_garbage_dit_held {
            use swole::bench;

            use super::*;

            #[bench]
            fn key(iterations: swole::Iterations) -> std::time::Duration {
                common::vg_dit_held(iterations, || {
                    ::verified_garbage::aead::aes_gcm::AesGcm::new(black_box(&KEY)).unwrap()
                })
            }
        }

        fn ring_seal(row: Aead) -> Seal<::ring::aead::LessSafeKey> {
            let key = ::ring::aead::UnboundKey::new(&::ring::aead::$alg, &KEY).unwrap();
            Seal::new(::ring::aead::LessSafeKey::new(key), row)
        }

        #[bench(args = ROWS, setup = ring_seal)]
        fn ring(s: &mut Seal<::ring::aead::LessSafeKey>) {
            test_ring_aes_gcm(&s.key, &NONCE, s.aad, &mut s.buf);
        }

        fn aws_seal(row: Aead) -> Seal<::aws_lc_rs::aead::LessSafeKey> {
            let key = ::aws_lc_rs::aead::UnboundKey::new(&::aws_lc_rs::aead::$alg, &KEY).unwrap();
            Seal::new(::aws_lc_rs::aead::LessSafeKey::new(key), row)
        }

        #[bench(args = ROWS, setup = aws_seal)]
        fn aws_lc_rs(s: &mut Seal<::aws_lc_rs::aead::LessSafeKey>) {
            test_aws_aes_gcm(&s.key, &NONCE, s.aad, &mut s.buf);
        }

        fn rustcrypto_seal(row: Aead) -> Seal<$rustcrypto> {
            use aes_gcm::KeyInit;
            Seal::new(<$rustcrypto>::new_from_slice(&KEY).unwrap(), row)
        }

        #[bench(args = ROWS, setup = rustcrypto_seal)]
        fn rustcrypto(s: &mut Seal<$rustcrypto>) {
            $test_rustcrypto(&s.key, &NONCE, s.aad, &mut s.buf);
        }

        fn rind_seal(row: Aead) -> Dit<Seal<::rind::aead::Key>> {
            let key = ::rind::aead::Key::new(&::rind::aead::$alg, &KEY).unwrap();
            Dit::hold(Seal::new(key, row))
        }

        #[bench(args = ROWS, setup = rind_seal)]
        fn rind(s: &mut Dit<Seal<::rind::aead::Key>>) {
            let s = &mut **s;
            test_rind_aes_gcm(&s.key, &NONCE, s.aad, &mut s.buf);
        }

        fn verified_garbage_seal(row: Aead) -> Seal<::verified_garbage::aead::aes_gcm::AesGcm> {
            vg_seal(&KEY, &::rind::aead::$alg, row)
        }

        #[bench(args = ROWS, setup = verified_garbage_seal)]
        fn verified_garbage(s: &mut Seal<::verified_garbage::aead::aes_gcm::AesGcm>) -> [u8; 16] {
            s.key.encrypt_in_place(&NONCE, s.aad, &mut s.buf).unwrap()
        }

        #[cfg(target_arch = "aarch64")]
        #[bench(args = ROWS, setup = verified_garbage_seal)]
        fn verified_garbage_dit_held(
            s: &mut Seal<::verified_garbage::aead::aes_gcm::AesGcm>,
            iterations: swole::Iterations,
        ) -> std::time::Duration {
            common::vg_dit_held(iterations, || verified_garbage(s))
        }

        #[cfg(graviola)]
        fn graviola_seal(row: Aead) -> Seal<(::graviola::aead::AesGcm, [u8; 16])> {
            Seal::new((::graviola::aead::AesGcm::new(&KEY), [0; 16]), row)
        }

        #[cfg(graviola)]
        #[bench(args = ROWS, setup = graviola_seal)]
        fn graviola(s: &mut Seal<(::graviola::aead::AesGcm, [u8; 16])>) {
            let (key, tag) = &mut s.key;
            key.encrypt(&NONCE, s.aad, &mut s.buf, tag);
        }

        type Libcrux = (
            ::libcrux_aes::$libcrux,
            ::libcrux_aes::$libcrux_nonce,
            ::libcrux_aes::$libcrux_tag,
            Vec<u8>,
        );

        /// libcrux seals out of place, into a ciphertext buffer of its own.
        fn libcrux_seal(row: Aead) -> Seal<Libcrux> {
            let key = ::libcrux_aes::$libcrux::from(KEY);
            let nonce = ::libcrux_aes::$libcrux_nonce::from(NONCE);
            let tag = ::libcrux_aes::$libcrux_tag::from([0; 16]);
            Seal::new((key, nonce, tag, row.size.zeros()), row)
        }

        #[bench(args = ROWS, setup = libcrux_seal)]
        fn libcrux(s: &mut Seal<Libcrux>) {
            let (key, nonce, tag, ct) = &mut s.key;
            key.encrypt(ct, tag, nonce, s.aad, &s.buf).unwrap();
        }

        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        fn openssl_seal(row: Aead) -> Seal<ossl_aead::Sealer> {
            let cipher = ::openssl::cipher::Cipher::$openssl();
            Seal::new(ossl_aead::Sealer::new(cipher, &KEY), row)
        }

        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        #[bench(args = ROWS, setup = openssl_seal)]
        fn openssl(s: &mut Seal<ossl_aead::Sealer>) -> [u8; 16] {
            s.key.seal(&NONCE, s.aad, &mut s.buf)
        }
    };
}

/// Decrypting and verifying each size's ciphertext, as a receiver pays.
macro_rules! open {
    ($len:literal, $alg:ident) => {
        const KEY: [u8; $len] = [0; $len];

        fn aws_open(row: Aead) -> Open<(aws_lc_rs::aead::LessSafeKey, [u8; 16])> {
            Open::new(row, &rind::aead::$alg, &KEY, |tag| {
                let key = aws_lc_rs::aead::UnboundKey::new(&aws_lc_rs::aead::$alg, &KEY).unwrap();
                (aws_lc_rs::aead::LessSafeKey::new(key), tag)
            })
        }

        #[bench(args = ROWS, setup = aws_open)]
        fn aws_lc_rs(open: &mut Open<(aws_lc_rs::aead::LessSafeKey, [u8; 16])>) {
            let aad = open.aad;
            let ((key, tag), ct, pt) = open.parts();
            pt.copy_from_slice(ct);
            key.open_in_place_separate_tag(
                aws_lc_rs::aead::Nonce::assume_unique_for_key(NONCE),
                aws_lc_rs::aead::Aad::from(aad),
                tag,
                pt,
            )
            .unwrap();
        }

        fn rind_open(row: Aead) -> Dit<Open<(rind::aead::Key, rind::aead::Tag)>> {
            Dit::hold(Open::new(row, &rind::aead::$alg, &KEY, |tag| {
                let key = rind::aead::Key::new(&rind::aead::$alg, &KEY).unwrap();
                (key, rind::aead::Tag::try_from(&tag[..]).unwrap())
            }))
        }

        #[bench(args = ROWS, setup = rind_open)]
        fn rind(open: &mut Dit<Open<(rind::aead::Key, rind::aead::Tag)>>) {
            let aad = open.aad;
            let ((key, tag), ct, pt) = open.parts();
            pt.copy_from_slice(ct);
            key.open_in_place_separate_tag(
                rind::aead::Nonce::assume_unique_for_key(NONCE),
                aad,
                *tag,
                pt,
            )
            .unwrap();
        }

        fn verified_garbage_setup(
            row: Aead,
        ) -> Open<(verified_garbage::aead::aes_gcm::AesGcm, [u8; 16])> {
            vg_open(&KEY, &rind::aead::$alg, row)
        }

        #[bench(args = ROWS, setup = verified_garbage_setup)]
        fn verified_garbage(open: &mut Open<(verified_garbage::aead::aes_gcm::AesGcm, [u8; 16])>) {
            verified_garbage_open(open);
        }

        #[cfg(target_arch = "aarch64")]
        #[bench(args = ROWS, setup = verified_garbage_setup)]
        fn verified_garbage_dit_held(
            open: &mut Open<(verified_garbage::aead::aes_gcm::AesGcm, [u8; 16])>,
            iterations: swole::Iterations,
        ) -> std::time::Duration {
            common::vg_dit_held(iterations, || verified_garbage(open))
        }
    };
}

/// The opening rows of the libraries that offer AES-128 and AES-256 alone.
macro_rules! open_more {
    ($len:literal, $alg:ident, $rustcrypto:ty, $libcrux:ident, $openssl:ident) => {
        fn ring_open(row: Aead) -> Open<(ring::aead::LessSafeKey, ring::aead::Tag)> {
            Open::new(row, &rind::aead::$alg, &KEY, |tag| {
                let key = ring::aead::UnboundKey::new(&ring::aead::$alg, &KEY).unwrap();
                (
                    ring::aead::LessSafeKey::new(key),
                    ring::aead::Tag::try_from(&tag[..]).unwrap(),
                )
            })
        }

        #[bench(args = ROWS, setup = ring_open)]
        fn ring(open: &mut Open<(ring::aead::LessSafeKey, ring::aead::Tag)>) {
            let aad = open.aad;
            let ((key, tag), ct, pt) = open.parts();
            pt.copy_from_slice(ct);
            key.open_in_place_separate_tag(
                ring::aead::Nonce::assume_unique_for_key(NONCE),
                ring::aead::Aad::from(aad),
                *tag,
                pt,
                0..,
            )
            .unwrap();
        }

        type RustCrypto = ($rustcrypto, aes_gcm::aead::Tag<$rustcrypto>);

        fn rustcrypto_open(row: Aead) -> Open<RustCrypto> {
            use aes_gcm::KeyInit;
            Open::new(row, &rind::aead::$alg, &KEY, |tag| {
                (<$rustcrypto>::new_from_slice(&KEY).unwrap(), tag.into())
            })
        }

        #[bench(args = ROWS, setup = rustcrypto_open)]
        fn rustcrypto(open: &mut Open<RustCrypto>) {
            use aes_gcm::AeadInOut;
            let aad = open.aad;
            let ((key, tag), ct, pt) = open.parts();
            pt.copy_from_slice(ct);
            key.decrypt_inout_detached(&NONCE.into(), aad, pt.into(), tag)
                .unwrap();
        }

        #[cfg(graviola)]
        fn graviola_open(row: Aead) -> Open<(graviola::aead::AesGcm, [u8; 16])> {
            Open::new(row, &rind::aead::$alg, &KEY, |tag| {
                (graviola::aead::AesGcm::new(&KEY), tag)
            })
        }

        #[cfg(graviola)]
        #[bench(args = ROWS, setup = graviola_open)]
        fn graviola(open: &mut Open<(graviola::aead::AesGcm, [u8; 16])>) {
            let aad = open.aad;
            let ((key, tag), ct, pt) = open.parts();
            pt.copy_from_slice(ct);
            key.decrypt(&NONCE, aad, pt, tag).unwrap();
        }

        fn libcrux_open(row: Aead) -> Open<[u8; 16]> {
            Open::new(row, &rind::aead::$alg, &KEY, |tag| tag)
        }

        /// libcrux opens out of place, so it needs no copy. Its key is the
        /// bare bytes, so building one in each call costs only the copy.
        #[bench(args = ROWS, setup = libcrux_open)]
        fn libcrux(open: &mut Open<[u8; 16]>) {
            let aad = open.aad;
            let (tag, ct, pt) = open.parts();
            let key = libcrux_aes::$libcrux::from(<[u8; $len]>::try_from(&KEY[..]).unwrap());
            key.decrypt(pt, &NONCE.into(), aad, ct, &(*tag).into())
                .unwrap()
        }

        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        fn openssl_open(row: Aead) -> Open<(ossl_aead::Opener, [u8; 16])> {
            Open::new(row, &rind::aead::$alg, &KEY, |tag| {
                let cipher = openssl::cipher::Cipher::$openssl();
                (ossl_aead::Opener::new(cipher, &KEY), tag)
            })
        }

        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        #[bench(args = ROWS, setup = openssl_open)]
        fn openssl(open: &mut Open<(ossl_aead::Opener, [u8; 16])>) {
            let aad = open.aad;
            let ((key, tag), ct, pt) = open.parts();
            pt.copy_from_slice(ct);
            key.open(&NONCE, aad, tag, pt);
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
mod aes128_gcm {
    use swole::bench;

    use super::*;

    seal!(
        16,
        AES_128_GCM,
        aes_gcm::Aes128Gcm,
        test_rc_aes128_gcm,
        AesGcm128Key,
        AesGcm128Nonce,
        AesGcm128Tag,
        aes_128_gcm
    );
}

#[cfg(not(target_arch = "xtensa"))]
mod aes256_gcm {
    use swole::bench;

    use super::*;

    seal!(
        32,
        AES_256_GCM,
        aes_gcm::Aes256Gcm,
        test_rc_aes256_gcm,
        AesGcm256Key,
        AesGcm256Nonce,
        AesGcm256Tag,
        aes_256_gcm
    );
}

#[cfg(not(target_arch = "xtensa"))]
mod aes128_gcm_open {
    use swole::bench;

    use super::*;

    open!(16, AES_128_GCM);
    open_more!(
        16,
        AES_128_GCM,
        aes_gcm::Aes128Gcm,
        AesGcm128Key,
        aes_128_gcm
    );
}

#[cfg(not(target_arch = "xtensa"))]
mod aes256_gcm_open {
    use swole::bench;

    use super::*;

    open!(32, AES_256_GCM);
    open_more!(
        32,
        AES_256_GCM,
        aes_gcm::Aes256Gcm,
        AesGcm256Key,
        aes_256_gcm
    );
}

/// AES-192-GCM, which only aws-lc-rs of the other libraries offers, both
/// ways: WebCrypto and pyca take 192-bit keys.
#[cfg(not(target_arch = "xtensa"))]
mod aes192_gcm {
    use swole::bench;

    use super::*;

    const KEY: [u8; 24] = [0; 24];

    pub mod aws_lc_rs {
        use swole::bench;

        use super::*;

        #[bench]
        fn key() {
            black_box(
                ::aws_lc_rs::aead::UnboundKey::new(
                    &::aws_lc_rs::aead::AES_192_GCM,
                    black_box(&KEY),
                )
                .unwrap(),
            );
        }
    }

    pub mod rind {
        use swole::bench;

        use super::*;

        #[bench(setup = dit)]
        fn key(_: &Dit<()>) {
            black_box(::rind::aead::Key::new(&::rind::aead::AES_192_GCM, black_box(&KEY)).unwrap());
        }
    }

    pub mod verified_garbage {
        use swole::bench;

        use super::*;

        #[bench]
        fn key() {
            black_box(::verified_garbage::aead::aes_gcm::AesGcm::new(black_box(&KEY)).unwrap());
        }
    }

    #[cfg(target_arch = "aarch64")]
    pub mod verified_garbage_dit_held {
        use swole::bench;

        use super::*;

        #[bench]
        fn key(iterations: swole::Iterations) -> std::time::Duration {
            common::vg_dit_held(iterations, || {
                ::verified_garbage::aead::aes_gcm::AesGcm::new(black_box(&KEY)).unwrap()
            })
        }
    }

    fn aws_seal(row: Aead) -> Seal<::aws_lc_rs::aead::LessSafeKey> {
        let key =
            ::aws_lc_rs::aead::UnboundKey::new(&::aws_lc_rs::aead::AES_192_GCM, &KEY).unwrap();
        Seal::new(::aws_lc_rs::aead::LessSafeKey::new(key), row)
    }

    #[bench(args = ROWS, setup = aws_seal)]
    fn aws_lc_rs(s: &mut Seal<::aws_lc_rs::aead::LessSafeKey>) {
        test_aws_aes_gcm(&s.key, &NONCE, s.aad, &mut s.buf);
    }

    fn rind_seal(row: Aead) -> Dit<Seal<::rind::aead::Key>> {
        let key = ::rind::aead::Key::new(&::rind::aead::AES_192_GCM, &KEY).unwrap();
        Dit::hold(Seal::new(key, row))
    }

    #[bench(args = ROWS, setup = rind_seal)]
    fn rind(s: &mut Dit<Seal<::rind::aead::Key>>) {
        let s = &mut **s;
        test_rind_aes_gcm(&s.key, &NONCE, s.aad, &mut s.buf);
    }

    fn verified_garbage_seal(row: Aead) -> Seal<::verified_garbage::aead::aes_gcm::AesGcm> {
        vg_seal(&KEY, &::rind::aead::AES_192_GCM, row)
    }

    #[bench(args = ROWS, setup = verified_garbage_seal)]
    fn verified_garbage(s: &mut Seal<::verified_garbage::aead::aes_gcm::AesGcm>) -> [u8; 16] {
        s.key.encrypt_in_place(&NONCE, s.aad, &mut s.buf).unwrap()
    }

    #[cfg(target_arch = "aarch64")]
    #[bench(args = ROWS, setup = verified_garbage_seal)]
    fn verified_garbage_dit_held(
        s: &mut Seal<::verified_garbage::aead::aes_gcm::AesGcm>,
        iterations: swole::Iterations,
    ) -> std::time::Duration {
        common::vg_dit_held(iterations, || verified_garbage(s))
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod aes192_gcm_open {
    use swole::bench;

    use super::*;

    open!(24, AES_192_GCM);
}

#[cfg(target_arch = "aarch64")]
#[cfg(not(target_arch = "xtensa"))]
mod dit_per_call {
    use super::*;

    mod aes128_gcm {
        use swole::bench;

        use super::*;

        fn seal(row: Aead) -> Seal<rind::aead::Key> {
            let key = rind::aead::Key::new(&rind::aead::AES_128_GCM, &[0; 16]).unwrap();
            Seal::new(key, row)
        }

        #[bench(args = common::DIT_PER_CALL_AEAD_ROWS, setup = seal)]
        fn rind(s: &mut Seal<rind::aead::Key>) {
            test_rind_aes_gcm(&s.key, &NONCE, s.aad, &mut s.buf);
        }
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
