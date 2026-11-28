#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use common::{Dit, dit};

#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
#[cfg(not(target_arch = "xtensa"))]
mod ossl {
    //! The openssl crate does not yet wrap ML-KEM keygen/encaps/decaps.

    use std::ptr;

    use foreign_types::ForeignType;
    use openssl::pkey::{HasPrivate, HasPublic, PKey, Private};
    use openssl::pkey_ctx::PkeyCtx;

    pub const CIPHERTEXT_LEN: usize = 1088;
    pub const SECRET_LEN: usize = 32;

    /// ML-KEM requires OpenSSL 3.5 or later at runtime: an older one fails
    /// the row rather than leave it out.
    pub fn require() {
        assert!(
            openssl::version::number() >= 0x3050_0000,
            "openssl's ML-KEM rows need OpenSSL 3.5 or later, not {}",
            openssl::version::version()
        );
    }

    pub fn keygen() -> PKey<Private> {
        unsafe {
            let ctx = openssl_sys::EVP_PKEY_CTX_new_from_name(
                ptr::null_mut(),
                c"ML-KEM-768".as_ptr(),
                ptr::null(),
            );
            assert!(!ctx.is_null());
            let mut ctx = PkeyCtx::<()>::from_ptr(ctx);
            ctx.keygen_init().unwrap();
            ctx.keygen().unwrap()
        }
    }

    pub fn encaps<T: HasPublic>(key: &PKey<T>) -> ([u8; CIPHERTEXT_LEN], [u8; SECRET_LEN]) {
        let ctx = PkeyCtx::new(key).unwrap();
        let mut ciphertext = [0u8; CIPHERTEXT_LEN];
        let mut secret = [0u8; SECRET_LEN];
        let mut ciphertext_len = ciphertext.len();
        let mut secret_len = secret.len();
        unsafe {
            assert_eq!(
                openssl_sys::EVP_PKEY_encapsulate_init(ctx.as_ptr(), ptr::null()),
                1
            );
            assert_eq!(
                openssl_sys::EVP_PKEY_encapsulate(
                    ctx.as_ptr(),
                    ciphertext.as_mut_ptr(),
                    &mut ciphertext_len,
                    secret.as_mut_ptr(),
                    &mut secret_len,
                ),
                1
            );
        }
        assert_eq!(ciphertext_len, CIPHERTEXT_LEN);
        assert_eq!(secret_len, SECRET_LEN);
        (ciphertext, secret)
    }

    pub fn decaps<T: HasPrivate>(key: &PKey<T>, ciphertext: &[u8]) -> [u8; SECRET_LEN] {
        let ctx = PkeyCtx::new(key).unwrap();
        let mut secret = [0u8; SECRET_LEN];
        let mut secret_len = secret.len();
        unsafe {
            assert_eq!(
                openssl_sys::EVP_PKEY_decapsulate_init(ctx.as_ptr(), ptr::null()),
                1
            );
            assert_eq!(
                openssl_sys::EVP_PKEY_decapsulate(
                    ctx.as_ptr(),
                    secret.as_mut_ptr(),
                    &mut secret_len,
                    ciphertext.as_ptr(),
                    ciphertext.len(),
                ),
                1
            );
        }
        assert_eq!(secret_len, SECRET_LEN);
        secret
    }
}

/// A verified-garbage ML-KEM-768 key, which it generates only from a seed:
/// drawn here, as the other libraries draw theirs.
#[cfg(not(target_arch = "xtensa"))]
fn vg_generate() -> verified_garbage::mlkem768::DecapsulationKey768 {
    let mut seed = [0u8; 64];
    getrandom::fill(&mut seed).unwrap();
    verified_garbage::mlkem768::DecapsulationKey768::from_seed(&seed).unwrap()
}

/// Checks that verified-garbage and rind each decapsulate the other's
/// ciphertexts to the secret it encapsulated.
#[cfg(not(target_arch = "xtensa"))]
fn vg_agrees_with_rind() {
    use rind::kem::*;
    use verified_garbage::mlkem768::EncapsulationKey768;

    let ours = DecapsulationKey::<MlKem768>::generate().unwrap();
    let theirs =
        EncapsulationKey768::from_bytes(ours.public_key().as_ref().try_into().unwrap()).unwrap();
    let (secret, ciphertext) = theirs.encapsulate().unwrap();
    let ciphertext = Ciphertext::new(&ciphertext).unwrap();
    assert_eq!(ours.decapsulate(&ciphertext).as_ref(), secret);

    let theirs = vg_generate();
    let ours = EncapsulationKey::<MlKem768>::new(theirs.encapsulation_key().as_bytes()).unwrap();
    let (ciphertext, secret) = ours.encapsulate().unwrap();
    assert_eq!(
        theirs
            .decapsulate(ciphertext.as_ref().try_into().unwrap())
            .unwrap(),
        secret.as_ref()
    );
}

/// A set's key generation against aws-lc-rs, libcrux, and rind.
macro_rules! keygen_rows {
    ($set:ident, $aws:ident, $libcrux:ident) => {
        #[bench]
        fn aws_lc_rs() {
            use aws_lc_rs::kem;
            let decaps = kem::DecapsulationKey::generate(&kem::$aws).unwrap();
            black_box(decaps.encapsulation_key().unwrap());
        }

        #[bench]
        fn libcrux_ml_kem() {
            use libcrux_ml_kem::$libcrux;
            let mut rand = [0u8; 64];
            getrandom::fill(&mut rand).unwrap();
            black_box($libcrux::generate_key_pair(rand).into_parts());
        }

        #[bench(setup = dit)]
        fn rind(_dit: &Dit<()>) {
            use rind::kem::*;
            black_box(DecapsulationKey::<$set>::generate().unwrap());
        }
    };
}

/// A set's encapsulation against aws-lc-rs, libcrux, and rind, decoding the
/// encoded key each time.
macro_rules! encaps_rows {
    ($set:ident, $aws:ident, $libcrux:ident, $public:ident) => {
        fn aws_key() -> Vec<u8> {
            use aws_lc_rs::kem;
            let decaps = kem::DecapsulationKey::generate(&kem::$aws).unwrap();
            decaps
                .encapsulation_key()
                .unwrap()
                .key_bytes()
                .unwrap()
                .as_ref()
                .to_vec()
        }

        #[bench(setup = aws_key)]
        fn aws_lc_rs(encaps_bytes: &[u8]) {
            use aws_lc_rs::kem;
            let encaps = kem::EncapsulationKey::new(&kem::$aws, encaps_bytes).unwrap();
            black_box(encaps.encapsulate().unwrap());
        }

        fn libcrux_key() -> Vec<u8> {
            use libcrux_ml_kem::$libcrux;
            let mut rand = [0u8; 64];
            getrandom::fill(&mut rand).unwrap();
            let (_, encaps) = $libcrux::generate_key_pair(rand).into_parts();
            encaps.as_slice().to_vec()
        }

        #[bench(setup = libcrux_key)]
        fn libcrux_ml_kem(encaps_bytes: &[u8]) {
            use libcrux_ml_kem::$libcrux;
            let encaps = $libcrux::$public::try_from(encaps_bytes).unwrap();
            let mut rand = [0u8; 32];
            getrandom::fill(&mut rand).unwrap();
            black_box($libcrux::encapsulate(&encaps, rand));
        }

        fn rind_key() -> Dit<rind::kem::EncapsulationKey<rind::kem::$set>> {
            use rind::kem::*;
            Dit::hold(
                DecapsulationKey::<$set>::generate()
                    .unwrap()
                    .public_key()
                    .clone(),
            )
        }

        #[bench(setup = rind_key)]
        fn rind(encaps: &Dit<rind::kem::EncapsulationKey<rind::kem::$set>>) {
            use rind::kem::*;
            let encaps = EncapsulationKey::<$set>::new(encaps.as_ref()).unwrap();
            black_box(encaps.encapsulate().unwrap());
        }
    };
}

/// A set's decapsulation against aws-lc-rs, libcrux, and rind, decoding the
/// encoded ciphertext each time.
macro_rules! decaps_rows {
    ($set:ident, $aws:ident, $libcrux:ident, $private:ident, $ciphertext:ident) => {
        fn aws_pair() -> (aws_lc_rs::kem::DecapsulationKey, Vec<u8>) {
            use aws_lc_rs::kem;
            let decaps = kem::DecapsulationKey::generate(&kem::$aws).unwrap();
            let (ciphertext, _secret) = decaps.encapsulation_key().unwrap().encapsulate().unwrap();
            (decaps, ciphertext.as_ref().to_vec())
        }

        #[bench(setup = aws_pair)]
        fn aws_lc_rs((decaps, ciphertext): &(aws_lc_rs::kem::DecapsulationKey, Vec<u8>)) {
            let ciphertext = aws_lc_rs::kem::Ciphertext::from(ciphertext.as_slice());
            black_box(decaps.decapsulate(ciphertext).unwrap());
        }

        fn libcrux_pair() -> (libcrux_ml_kem::$libcrux::$private, Vec<u8>) {
            use libcrux_ml_kem::$libcrux;
            let mut rand = [0u8; 64];
            getrandom::fill(&mut rand).unwrap();
            let (decaps, encaps) = $libcrux::generate_key_pair(rand).into_parts();

            let mut rand = [0u8; 32];
            getrandom::fill(&mut rand).unwrap();
            let (ciphertext, _secret) = $libcrux::encapsulate(&encaps, rand);
            (decaps, ciphertext.as_slice().to_vec())
        }

        #[bench(setup = libcrux_pair)]
        fn libcrux_ml_kem((decaps, ciphertext): &(libcrux_ml_kem::$libcrux::$private, Vec<u8>)) {
            use libcrux_ml_kem::$libcrux;
            let ciphertext = $libcrux::$ciphertext::try_from(ciphertext.as_slice()).unwrap();
            black_box($libcrux::decapsulate(decaps, &ciphertext));
        }

        fn rind_pair() -> Dit<(
            rind::kem::DecapsulationKey<rind::kem::$set>,
            rind::kem::Ciphertext<rind::kem::$set>,
        )> {
            use rind::kem::*;
            let decaps = DecapsulationKey::<$set>::generate().unwrap();
            let (ciphertext, _secret) = decaps.public_key().encapsulate().unwrap();
            Dit::hold((decaps, ciphertext))
        }

        #[bench(setup = rind_pair)]
        fn rind(
            pair: &Dit<(
                rind::kem::DecapsulationKey<rind::kem::$set>,
                rind::kem::Ciphertext<rind::kem::$set>,
            )>,
        ) {
            use rind::kem::*;
            let (decaps, ciphertext) = &**pair;
            let ciphertext = Ciphertext::<$set>::new(ciphertext.as_ref()).unwrap();
            black_box(decaps.decapsulate(&ciphertext));
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
mod mlkem512_keygen {
    use swole::bench;

    use super::*;

    keygen_rows!(MlKem512, ML_KEM_512, mlkem512);
}

#[cfg(not(target_arch = "xtensa"))]
mod mlkem512_encaps {
    use swole::bench;

    use super::*;

    encaps_rows!(MlKem512, ML_KEM_512, mlkem512, MlKem512PublicKey);
}

#[cfg(not(target_arch = "xtensa"))]
mod mlkem512_decaps {
    use swole::bench;

    use super::*;

    decaps_rows!(
        MlKem512,
        ML_KEM_512,
        mlkem512,
        MlKem512PrivateKey,
        MlKem512Ciphertext
    );
}

#[cfg(not(target_arch = "xtensa"))]
mod mlkem1024_keygen {
    use swole::bench;

    use super::*;

    keygen_rows!(MlKem1024, ML_KEM_1024, mlkem1024);
}

#[cfg(not(target_arch = "xtensa"))]
mod mlkem1024_encaps {
    use swole::bench;

    use super::*;

    encaps_rows!(MlKem1024, ML_KEM_1024, mlkem1024, MlKem1024PublicKey);
}

#[cfg(not(target_arch = "xtensa"))]
mod mlkem1024_decaps {
    use swole::bench;

    use super::*;

    decaps_rows!(
        MlKem1024,
        ML_KEM_1024,
        mlkem1024,
        MlKem1024PrivateKey,
        MlKem1024Ciphertext
    );
}

// client first operation
#[cfg(not(target_arch = "xtensa"))]
mod mlkem768_keygen {
    use swole::bench;

    use super::*;

    keygen_rows!(MlKem768, ML_KEM_768, mlkem768);

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(setup = ossl::require)]
    fn openssl(_: &()) {
        let decaps = ossl::keygen();
        black_box(decaps.raw_public_key().unwrap());
    }

    #[bench]
    fn rustcrypto() {
        use ml_kem::{Kem, MlKem768};
        black_box(MlKem768::generate_keypair());
    }

    #[bench(setup = vg_agrees_with_rind)]
    fn verified_garbage(_: &()) {
        black_box(vg_generate());
    }

    #[cfg(graviola)]
    #[bench]
    fn graviola() {
        use graviola::key_agreement::mlkem768::DecapKey;
        black_box(DecapKey::generate().unwrap());
    }
}

// server operation
#[cfg(not(target_arch = "xtensa"))]
mod mlkem768_encaps {
    use swole::bench;

    use super::*;

    encaps_rows!(MlKem768, ML_KEM_768, mlkem768, MlKem768PublicKey);

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    fn openssl_key() -> Vec<u8> {
        ossl::require();
        ossl::keygen().raw_public_key().unwrap()
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(setup = openssl_key)]
    fn openssl(encaps_bytes: &[u8]) {
        use openssl::pkey::{KeyType, PKey};
        let encaps =
            PKey::public_key_from_raw_bytes_ex(None, KeyType::ML_KEM_768, None, encaps_bytes)
                .unwrap();
        black_box(ossl::encaps(&encaps));
    }

    fn rustcrypto_key() -> ml_kem::Key<ml_kem::ml_kem_768::EncapsulationKey> {
        use ml_kem::{Kem, KeyExport, MlKem768};
        let (_decaps, encaps) = MlKem768::generate_keypair();
        encaps.to_bytes()
    }

    #[bench(setup = rustcrypto_key)]
    fn rustcrypto(encaps_bytes: &ml_kem::Key<ml_kem::ml_kem_768::EncapsulationKey>) {
        use ml_kem::{Encapsulate, ml_kem_768::EncapsulationKey};
        let encaps = EncapsulationKey::new(encaps_bytes).unwrap();
        black_box(encaps.encapsulate());
    }

    fn vg_key() -> [u8; 1184] {
        vg_agrees_with_rind();
        *vg_generate().encapsulation_key().as_bytes()
    }

    #[bench(setup = vg_key)]
    fn verified_garbage(encaps: &[u8; 1184]) {
        use verified_garbage::mlkem768::EncapsulationKey768;
        let encaps = EncapsulationKey768::from_bytes(encaps).unwrap();
        black_box(encaps.encapsulate().unwrap());
    }

    #[cfg(graviola)]
    fn graviola_key() -> [u8; 1184] {
        use graviola::key_agreement::mlkem768::DecapKey;
        DecapKey::generate().unwrap().encapsulation_key().as_bytes()
    }

    #[cfg(graviola)]
    #[bench(setup = graviola_key)]
    fn graviola(encaps: &[u8; 1184]) {
        use graviola::key_agreement::mlkem768::EncapKey;
        let encaps = EncapKey::from_bytes(encaps).unwrap();
        black_box(encaps.encaps().unwrap());
    }
}

// client second operation
#[cfg(not(target_arch = "xtensa"))]
mod mlkem768_decaps {
    use swole::bench;

    use super::*;

    decaps_rows!(
        MlKem768,
        ML_KEM_768,
        mlkem768,
        MlKem768PrivateKey,
        MlKem768Ciphertext
    );

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    fn openssl_pair() -> (
        openssl::pkey::PKey<openssl::pkey::Private>,
        [u8; ossl::CIPHERTEXT_LEN],
    ) {
        ossl::require();
        let decaps = ossl::keygen();
        let (ciphertext, _secret) = ossl::encaps(&decaps);
        (decaps, ciphertext)
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(setup = openssl_pair)]
    fn openssl(
        (decaps, ciphertext): &(
            openssl::pkey::PKey<openssl::pkey::Private>,
            [u8; ossl::CIPHERTEXT_LEN],
        ),
    ) {
        black_box(ossl::decaps(decaps, ciphertext));
    }

    fn rustcrypto_pair() -> (ml_kem::ml_kem_768::DecapsulationKey, Vec<u8>) {
        use ml_kem::{Encapsulate, Kem, MlKem768};
        let (decaps, encaps) = MlKem768::generate_keypair();
        let (ciphertext, _secret) = encaps.encapsulate();
        (decaps, ciphertext.as_slice().to_vec())
    }

    #[bench(setup = rustcrypto_pair)]
    fn rustcrypto((decaps, ciphertext): &(ml_kem::ml_kem_768::DecapsulationKey, Vec<u8>)) {
        use ml_kem::Decapsulate;
        black_box(decaps.decapsulate_slice(ciphertext).unwrap());
    }

    fn vg_pair() -> (verified_garbage::mlkem768::DecapsulationKey768, [u8; 1088]) {
        vg_agrees_with_rind();
        let decaps = vg_generate();
        let (_secret, ciphertext) = decaps.encapsulation_key().encapsulate().unwrap();
        (decaps, ciphertext)
    }

    #[bench(setup = vg_pair)]
    fn verified_garbage(
        (decaps, ciphertext): &(verified_garbage::mlkem768::DecapsulationKey768, [u8; 1088]),
    ) {
        black_box(decaps.decapsulate(ciphertext).unwrap());
    }

    /// Decapsulation consumes its key, so each call gets a new key and
    /// ciphertext, made untimed.
    #[cfg(graviola)]
    fn graviola_pair() -> (
        graviola::key_agreement::mlkem768::DecapKey,
        graviola::key_agreement::mlkem768::Ciphertext,
    ) {
        use graviola::key_agreement::mlkem768::DecapKey;
        let decaps = DecapKey::generate().unwrap();
        let (_secret, ciphertext) = decaps.encapsulation_key().encaps().unwrap();
        (decaps, ciphertext)
    }

    #[cfg(graviola)]
    #[bench(setup = graviola_pair)]
    fn graviola(
        (decaps, ciphertext): (
            graviola::key_agreement::mlkem768::DecapKey,
            graviola::key_agreement::mlkem768::Ciphertext,
        ),
    ) {
        black_box(decaps.decaps(&ciphertext));
    }
}

// combined operation: keygen, encaps-encode, encaps-decode, encaps, decaps
#[cfg(not(target_arch = "xtensa"))]
mod mlkem768_combined {
    use swole::bench;

    use super::*;

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(setup = ossl::require)]
    fn openssl(_: &()) {
        use openssl::pkey::{KeyType, PKey};
        let decaps = ossl::keygen();
        let encaps_encoded = decaps.raw_public_key().unwrap();
        let encaps =
            PKey::public_key_from_raw_bytes_ex(None, KeyType::ML_KEM_768, None, &encaps_encoded)
                .unwrap();
        let (ciphertext, _secret) = ossl::encaps(&encaps);
        black_box(ossl::decaps(&decaps, &ciphertext));
    }

    #[bench]
    fn aws_lc_rs() {
        use aws_lc_rs::kem;
        let decaps = kem::DecapsulationKey::generate(&kem::ML_KEM_768).unwrap();
        let encaps_encoded = decaps.encapsulation_key().unwrap().key_bytes().unwrap();
        let encaps = kem::EncapsulationKey::new(&kem::ML_KEM_768, encaps_encoded.as_ref()).unwrap();
        let (ciphertext, _secret) = encaps.encapsulate().unwrap();
        black_box(decaps.decapsulate(ciphertext).unwrap());
    }

    #[bench]
    fn libcrux_ml_kem() {
        use libcrux_ml_kem::mlkem768;
        let mut rand = [0u8; 64];
        getrandom::fill(&mut rand).unwrap();
        let (decaps, encaps) = mlkem768::generate_key_pair(rand).into_parts();
        let encaps_encoded = encaps.as_slice();
        let encaps = mlkem768::MlKem768PublicKey::from(encaps_encoded);

        let mut rand = [0u8; 32];
        getrandom::fill(&mut rand).unwrap();
        let (ciphertext, _secret) = mlkem768::encapsulate(&encaps, rand);
        black_box(mlkem768::decapsulate(&decaps, &ciphertext));
    }

    #[bench]
    fn rustcrypto() {
        use ml_kem::{
            Decapsulate, Encapsulate, Kem, KeyExport, MlKem768, ml_kem_768::EncapsulationKey,
        };
        let (decaps, encaps) = MlKem768::generate_keypair();
        let encaps_encoded = encaps.to_bytes();
        let encaps = EncapsulationKey::new(&encaps_encoded).unwrap();
        let (ciphertext, _secret) = encaps.encapsulate();
        black_box(decaps.decapsulate(&ciphertext));
    }

    #[bench(setup = dit)]
    fn rind(_dit: &Dit<()>) {
        use rind::kem::*;
        let decaps = DecapsulationKey::<MlKem768>::generate().unwrap();
        let encaps_encoded = decaps.public_key();
        let encaps = EncapsulationKey::<MlKem768>::new(encaps_encoded.as_ref()).unwrap();
        let (ciphertext, _secret) = encaps.encapsulate().unwrap();
        let ciphertext = Ciphertext::<MlKem768>::new(ciphertext.as_ref()).unwrap();
        black_box(decaps.decapsulate(&ciphertext));
    }

    #[bench(setup = vg_agrees_with_rind)]
    fn verified_garbage(_: &()) {
        use verified_garbage::mlkem768::EncapsulationKey768;
        let decaps = vg_generate();
        let encaps_encoded = decaps.encapsulation_key().as_bytes();
        let encaps = EncapsulationKey768::from_bytes(encaps_encoded).unwrap();
        let (_secret, ciphertext) = encaps.encapsulate().unwrap();
        black_box(decaps.decapsulate(&ciphertext).unwrap());
    }

    #[cfg(graviola)]
    #[bench]
    fn graviola() {
        use graviola::key_agreement::mlkem768::{DecapKey, EncapKey};
        let decaps = DecapKey::generate().unwrap();
        let encaps = EncapKey::from_bytes(&decaps.encapsulation_key().as_bytes()).unwrap();
        let (_secret, ciphertext) = encaps.encaps().unwrap();
        black_box(decaps.decaps(&ciphertext));
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
