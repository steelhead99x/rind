#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;
#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
#[cfg(not(target_arch = "xtensa"))]
mod ossl_aead;

#[cfg(not(target_arch = "xtensa"))]
use common::{AEAD_ROWS, Aead, Dit};

#[cfg(not(target_arch = "xtensa"))]
const KEY: [u8; 32] = [0; 32];
#[cfg(not(target_arch = "xtensa"))]
const NONCE: [u8; 12] = [0; 12];

#[cfg(not(target_arch = "xtensa"))]
fn test_ring_chacha(key: &ring::aead::LessSafeKey, nonce: &[u8; 12], aad: &[u8], buf: &mut [u8]) {
    let _tag = key
        .seal_in_place_separate_tag(
            ring::aead::Nonce::assume_unique_for_key(*nonce),
            ring::aead::Aad::from(aad),
            buf,
        )
        .unwrap();
}

#[cfg(not(target_arch = "xtensa"))]
fn test_aws_chacha(
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
fn test_rc_chacha(
    key: &::chacha20poly1305::ChaCha20Poly1305,
    nonce: &[u8; 12],
    aad: &[u8],
    buf: &mut [u8],
) {
    use ::chacha20poly1305::AeadInOut;
    let _tag = key
        .encrypt_inout_detached(nonce.into(), aad, buf.into())
        .unwrap();
}

#[cfg(not(target_arch = "xtensa"))]
fn test_rind_chacha(key: &rind::aead::Key, nonce: &[u8; 12], aad: &[u8], buf: &mut [u8]) {
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

/// A key, with the tag it opens under, and a ciphertext rind sealed. As in
/// `aes_gcm`, each call copies the ciphertext into a buffer a whole number
/// of 4 KiB pages after it, so the copies do not share a page offset.
#[cfg(not(target_arch = "xtensa"))]
struct Open<K> {
    key: K,
    aad: &'static [u8],
    buf: Vec<u8>,
    stride: usize,
}

#[cfg(not(target_arch = "xtensa"))]
impl<K> Open<K> {
    /// Seals `row` with rind, then makes the row's key from the tag.
    fn new(row: Aead, make: impl FnOnce([u8; 16]) -> K) -> Self {
        let stride = row.len().next_multiple_of(4096);
        let mut buf = vec![0; stride + row.len()];
        let tag = rind::aead::Key::new(&rind::aead::CHACHA20_POLY1305, &KEY)
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

#[cfg(not(target_arch = "xtensa"))]
mod chacha20poly1305 {
    use swole::bench;

    use super::*;

    fn ring_seal(row: Aead) -> Seal<ring::aead::LessSafeKey> {
        let key = ring::aead::UnboundKey::new(&ring::aead::CHACHA20_POLY1305, &KEY).unwrap();
        Seal::new(ring::aead::LessSafeKey::new(key), row)
    }

    #[bench(args = AEAD_ROWS, setup = ring_seal)]
    fn ring(s: &mut Seal<ring::aead::LessSafeKey>) {
        test_ring_chacha(&s.key, &NONCE, s.aad, &mut s.buf);
    }

    fn aws_seal(row: Aead) -> Seal<aws_lc_rs::aead::LessSafeKey> {
        let key =
            aws_lc_rs::aead::UnboundKey::new(&aws_lc_rs::aead::CHACHA20_POLY1305, &KEY).unwrap();
        Seal::new(aws_lc_rs::aead::LessSafeKey::new(key), row)
    }

    #[bench(args = AEAD_ROWS, setup = aws_seal)]
    fn aws_lc_rs(s: &mut Seal<aws_lc_rs::aead::LessSafeKey>) {
        test_aws_chacha(&s.key, &NONCE, s.aad, &mut s.buf);
    }

    fn rustcrypto_seal(row: Aead) -> Seal<::chacha20poly1305::ChaCha20Poly1305> {
        use ::chacha20poly1305::KeyInit;
        let key = ::chacha20poly1305::ChaCha20Poly1305::new_from_slice(&KEY).unwrap();
        Seal::new(key, row)
    }

    #[bench(args = AEAD_ROWS, setup = rustcrypto_seal)]
    fn rustcrypto(s: &mut Seal<::chacha20poly1305::ChaCha20Poly1305>) {
        test_rc_chacha(&s.key, &NONCE, s.aad, &mut s.buf);
    }

    fn rind_seal(row: Aead) -> Dit<Seal<rind::aead::Key>> {
        let key = rind::aead::Key::new(&rind::aead::CHACHA20_POLY1305, &KEY).unwrap();
        Dit::hold(Seal::new(key, row))
    }

    #[bench(args = AEAD_ROWS, setup = rind_seal)]
    fn rind(s: &mut Dit<Seal<rind::aead::Key>>) {
        let s = &mut **s;
        test_rind_chacha(&s.key, &NONCE, s.aad, &mut s.buf);
    }

    type Vg = verified_garbage::aead::chacha20poly1305::ChaCha20Poly1305;

    /// verified-garbage's key, after checking its ciphertext and tag match
    /// rind's.
    fn vg_seal(row: Aead) -> Seal<Vg> {
        let key = Vg::new(&KEY);
        let mut expect = row.size.zeros();
        let tag = rind::aead::Key::new(&rind::aead::CHACHA20_POLY1305, &KEY)
            .unwrap()
            .seal_in_place_separate_tag(
                rind::aead::Nonce::assume_unique_for_key(NONCE),
                row.aad,
                &mut expect,
            )
            .unwrap();
        let mut ct = row.size.zeros();
        assert_eq!(
            key.encrypt_in_place(&NONCE, row.aad, &mut ct).unwrap(),
            tag.as_ref()
        );
        assert_eq!(ct, expect);
        Seal::new(key, row)
    }

    #[bench(args = AEAD_ROWS, setup = vg_seal)]
    fn verified_garbage(s: &mut Seal<Vg>) -> [u8; 16] {
        s.key.encrypt_in_place(&NONCE, s.aad, &mut s.buf).unwrap()
    }

    #[cfg(target_arch = "aarch64")]
    #[bench(args = AEAD_ROWS, setup = vg_seal)]
    fn verified_garbage_dit_held(
        s: &mut Seal<Vg>,
        iterations: swole::Iterations,
    ) -> std::time::Duration {
        common::vg_dit_held(iterations, || verified_garbage(s))
    }

    #[cfg(graviola)]
    fn graviola_seal(row: Aead) -> Seal<(graviola::aead::ChaCha20Poly1305, [u8; 16])> {
        Seal::new((graviola::aead::ChaCha20Poly1305::new(KEY), [0; 16]), row)
    }

    #[cfg(graviola)]
    #[bench(args = AEAD_ROWS, setup = graviola_seal)]
    fn graviola(s: &mut Seal<(graviola::aead::ChaCha20Poly1305, [u8; 16])>) {
        let (key, tag) = &mut s.key;
        key.encrypt(&NONCE, s.aad, &mut s.buf, tag);
    }

    /// libcrux seals out of place, into a ciphertext buffer of its own, with
    /// a tag.
    fn libcrux_seal(row: Aead) -> Seal<(Vec<u8>, [u8; 16])> {
        Seal::new((row.size.zeros(), [0; 16]), row)
    }

    #[bench(args = AEAD_ROWS, setup = libcrux_seal)]
    fn libcrux(s: &mut Seal<(Vec<u8>, [u8; 16])>) {
        let (ct, tag) = &mut s.key;
        libcrux_chacha20poly1305::encrypt_detached(&KEY, &s.buf, ct, tag, s.aad, &NONCE).unwrap();
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    fn openssl_seal(row: Aead) -> Seal<ossl_aead::Sealer> {
        let cipher = openssl::cipher::Cipher::chacha20_poly1305();
        Seal::new(ossl_aead::Sealer::new(cipher, &KEY), row)
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(args = AEAD_ROWS, setup = openssl_seal)]
    fn openssl(s: &mut Seal<ossl_aead::Sealer>) -> [u8; 16] {
        s.key.seal(&NONCE, s.aad, &mut s.buf)
    }
}

/// Decrypting and verifying each size's ciphertext, as a receiver pays.
#[cfg(not(target_arch = "xtensa"))]
mod chacha20poly1305_open {
    use swole::bench;

    use super::*;

    fn ring_open(row: Aead) -> Open<(ring::aead::LessSafeKey, ring::aead::Tag)> {
        Open::new(row, |tag| {
            let key = ring::aead::UnboundKey::new(&ring::aead::CHACHA20_POLY1305, &KEY).unwrap();
            let tag = ring::aead::Tag::try_from(&tag[..]).unwrap();
            (ring::aead::LessSafeKey::new(key), tag)
        })
    }

    #[bench(args = AEAD_ROWS, setup = ring_open)]
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

    fn aws_open(row: Aead) -> Open<(aws_lc_rs::aead::LessSafeKey, [u8; 16])> {
        Open::new(row, |tag| {
            let key = aws_lc_rs::aead::UnboundKey::new(&aws_lc_rs::aead::CHACHA20_POLY1305, &KEY)
                .unwrap();
            (aws_lc_rs::aead::LessSafeKey::new(key), tag)
        })
    }

    #[bench(args = AEAD_ROWS, setup = aws_open)]
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

    type RustCrypto = (
        ::chacha20poly1305::ChaCha20Poly1305,
        ::chacha20poly1305::Tag,
    );

    fn rustcrypto_open(row: Aead) -> Open<RustCrypto> {
        use ::chacha20poly1305::KeyInit;
        Open::new(row, |tag| {
            let key = ::chacha20poly1305::ChaCha20Poly1305::new_from_slice(&KEY).unwrap();
            (key, tag.into())
        })
    }

    #[bench(args = AEAD_ROWS, setup = rustcrypto_open)]
    fn rustcrypto(open: &mut Open<RustCrypto>) {
        use ::chacha20poly1305::AeadInOut;
        let aad = open.aad;
        let ((key, tag), ct, pt) = open.parts();
        pt.copy_from_slice(ct);
        key.decrypt_inout_detached(&NONCE.into(), aad, pt.into(), tag)
            .unwrap();
    }

    fn rind_open(row: Aead) -> Dit<Open<(rind::aead::Key, rind::aead::Tag)>> {
        Dit::hold(Open::new(row, |tag| {
            let key = rind::aead::Key::new(&rind::aead::CHACHA20_POLY1305, &KEY).unwrap();
            (key, rind::aead::Tag::try_from(&tag[..]).unwrap())
        }))
    }

    #[bench(args = AEAD_ROWS, setup = rind_open)]
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

    type Vg = verified_garbage::aead::chacha20poly1305::ChaCha20Poly1305;

    /// verified-garbage's key, after checking it opens what rind sealed.
    fn vg_open(row: Aead) -> Open<(Vg, [u8; 16])> {
        let mut open = Open::new(row, |tag| (Vg::new(&KEY), tag));
        let ((key, tag), ct, pt) = open.parts();
        pt.copy_from_slice(ct);
        key.decrypt_in_place(&NONCE, row.aad, pt, tag).unwrap();
        assert!(pt.iter().all(|&x| x == 0));
        open
    }

    #[bench(args = AEAD_ROWS, setup = vg_open)]
    fn verified_garbage(open: &mut Open<(Vg, [u8; 16])>) {
        let aad = open.aad;
        let ((key, tag), ct, pt) = open.parts();
        pt.copy_from_slice(ct);
        key.decrypt_in_place(&NONCE, aad, pt, tag).unwrap();
    }

    #[cfg(target_arch = "aarch64")]
    #[bench(args = AEAD_ROWS, setup = vg_open)]
    fn verified_garbage_dit_held(
        open: &mut Open<(Vg, [u8; 16])>,
        iterations: swole::Iterations,
    ) -> std::time::Duration {
        common::vg_dit_held(iterations, || verified_garbage(open))
    }

    #[cfg(graviola)]
    fn graviola_open(row: Aead) -> Open<(graviola::aead::ChaCha20Poly1305, [u8; 16])> {
        Open::new(row, |tag| (graviola::aead::ChaCha20Poly1305::new(KEY), tag))
    }

    #[cfg(graviola)]
    #[bench(args = AEAD_ROWS, setup = graviola_open)]
    fn graviola(open: &mut Open<(graviola::aead::ChaCha20Poly1305, [u8; 16])>) {
        let aad = open.aad;
        let ((key, tag), ct, pt) = open.parts();
        pt.copy_from_slice(ct);
        key.decrypt(&NONCE, aad, pt, tag).unwrap();
    }

    fn libcrux_open(row: Aead) -> Open<[u8; 16]> {
        Open::new(row, |tag| tag)
    }

    /// libcrux opens out of place, so it needs no copy.
    #[bench(args = AEAD_ROWS, setup = libcrux_open)]
    fn libcrux(open: &mut Open<[u8; 16]>) {
        let aad = open.aad;
        let (tag, ct, pt) = open.parts();
        libcrux_chacha20poly1305::decrypt_detached(&KEY, pt, ct, tag, aad, &NONCE).unwrap();
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    fn openssl_open(row: Aead) -> Open<(ossl_aead::Opener, [u8; 16])> {
        Open::new(row, |tag| {
            let cipher = openssl::cipher::Cipher::chacha20_poly1305();
            (ossl_aead::Opener::new(cipher, &KEY), tag)
        })
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(args = AEAD_ROWS, setup = openssl_open)]
    fn openssl(open: &mut Open<(ossl_aead::Opener, [u8; 16])>) {
        let aad = open.aad;
        let ((key, tag), ct, pt) = open.parts();
        pt.copy_from_slice(ct);
        key.open(&NONCE, aad, tag, pt);
    }
}

#[cfg(target_arch = "aarch64")]
#[cfg(not(target_arch = "xtensa"))]
mod dit_per_call {
    use super::*;

    mod chacha20poly1305 {
        use swole::bench;

        use super::*;

        fn seal(row: Aead) -> Seal<rind::aead::Key> {
            let key = rind::aead::Key::new(&rind::aead::CHACHA20_POLY1305, &KEY).unwrap();
            Seal::new(key, row)
        }

        #[bench(args = common::DIT_PER_CALL_AEAD_ROWS, setup = seal)]
        fn rind(s: &mut Seal<rind::aead::Key>) {
            test_rind_chacha(&s.key, &NONCE, s.aad, &mut s.buf);
        }
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
