//! HPKE's base mode with DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, and
//! AES-128-GCM, the suite MLS and ECH default to: each side's setup, then
//! one QUIC-datagram-sized message sealed and opened.
mod criterion;
use std::hint::black_box;

use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};

const INFO: &[u8] = b"rind-bench info";
const AAD: &[u8] = b"rind-bench aad";
const MESSAGE: [u8; 1350] = [0x5a; 1350];

type RcKem = hpke::kem::X25519HkdfSha256;
type RcKdf = hpke::kdf::HkdfSha256;
type RcAead = hpke::aead::AesGcm128;

fn rind_suite() -> rind::hpke::Suite {
    rind::hpke::Suite {
        kdf: &rind::hpke::HKDF_SHA256,
        aead: &rind::hpke::AES_128_GCM,
    }
}

fn libcrux_hpke() -> hpke_rs::Hpke<hpke_rs::libcrux::HpkeLibcrux> {
    use hpke_rs::hpke_types::{AeadAlgorithm, KdfAlgorithm, KemAlgorithm};
    hpke_rs::Hpke::new(
        hpke_rs::Mode::Base,
        KemAlgorithm::DhKem25519,
        KdfAlgorithm::HkdfSha256,
        AeadAlgorithm::Aes128Gcm,
    )
}

const AWS_LC_RS: &dyn rustls::crypto::hpke::Hpke =
    rustls::crypto::aws_lc_rs::hpke::DH_KEM_X25519_HKDF_SHA256_AES_128;

// Checks, untimed, that every library speaks the same suite as rind: each
// opens a message rind sealed to it, and rind opens one each sealed to rind.
fn check_interop() {
    use hpke::{Deserializable, Kem, OpModeR, OpModeS, Serializable};
    use rind::hpke::{DHKEM_X25519_HKDF_SHA256, PrivateKey, PublicKey, Recipient, Sender};

    // rind's sender, sealing to another library's public key.
    let rind_seal = |public_key: &[u8]| {
        let public_key = PublicKey::new(&DHKEM_X25519_HKDF_SHA256, public_key).unwrap();
        let (enc, mut sender) = Sender::new(rind_suite(), &public_key, INFO).unwrap();
        let mut ciphertext = MESSAGE.to_vec();
        sender
            .seal_in_place_append_tag(AAD, &mut ciphertext)
            .unwrap();
        (enc.as_ref().to_vec(), ciphertext)
    };
    // rind's recipient, opening what another library sealed to it.
    let private_key = PrivateKey::generate(&DHKEM_X25519_HKDF_SHA256).unwrap();
    let rind_public = private_key.public_key().as_ref().to_vec();
    let rind_open = |enc: &[u8], mut ciphertext: Vec<u8>| {
        let mut recipient = Recipient::new(rind_suite(), &private_key, enc, INFO).unwrap();
        assert_eq!(
            recipient.open_in_place(AAD, &mut ciphertext).unwrap(),
            MESSAGE
        );
    };

    // aws-lc-rs, through rustls.
    let (public_key, private_key) = AWS_LC_RS.generate_key_pair().unwrap();
    let (enc, ciphertext) = rind_seal(&public_key.0);
    let mut opener = AWS_LC_RS
        .setup_opener(
            &rustls::crypto::hpke::EncapsulatedSecret(enc),
            INFO,
            &private_key,
        )
        .unwrap();
    assert_eq!(opener.open(AAD, &ciphertext).unwrap(), MESSAGE);
    let public_key = rustls::crypto::hpke::HpkePublicKey(rind_public.clone());
    let (enc, mut sealer) = AWS_LC_RS.setup_sealer(INFO, &public_key).unwrap();
    rind_open(&enc.0, sealer.seal(AAD, &MESSAGE).unwrap());

    // hpke.
    let (private_key, public_key) = RcKem::gen_keypair();
    let (enc, ciphertext) = rind_seal(&public_key.to_bytes());
    let enc = <RcKem as Kem>::EncappedKey::from_bytes(&enc).unwrap();
    let mut recipient =
        hpke::setup_receiver::<RcAead, RcKdf, RcKem>(&OpModeR::Base, &private_key, &enc, INFO)
            .unwrap();
    assert_eq!(recipient.open(&ciphertext, AAD).unwrap(), MESSAGE);
    let public_key = <RcKem as Kem>::PublicKey::from_bytes(&rind_public).unwrap();
    let (enc, mut sender) =
        hpke::setup_sender::<RcAead, RcKdf, RcKem>(&OpModeS::Base, &public_key, INFO).unwrap();
    rind_open(&enc.to_bytes(), sender.seal(&MESSAGE, AAD).unwrap());

    // hpke-rs.
    let mut hpke = libcrux_hpke();
    let key_pair = hpke.generate_key_pair().unwrap();
    let (enc, ciphertext) = rind_seal(key_pair.public_key().as_slice());
    let mut recipient = hpke
        .setup_receiver(&enc, key_pair.private_key(), INFO, None, None, None)
        .unwrap();
    assert_eq!(recipient.open(AAD, &ciphertext).unwrap(), MESSAGE);
    let public_key = hpke_rs::HpkePublicKey::from(rind_public.as_slice());
    let (enc, mut sender) = hpke
        .setup_sender(&public_key, INFO, None, None, None)
        .unwrap();
    rind_open(&enc, sender.seal(AAD, &MESSAGE).unwrap());
}

// Encapsulate to the recipient's parsed public key and derive the context.
fn setup_sender(c: &mut Criterion) {
    check_interop();

    let mut group = c.benchmark_group("hpke-x25519-setup-sender");
    group.throughput(Throughput::Elements(1));

    group.bench_function("rind", |b| {
        use rind::hpke::{DHKEM_X25519_HKDF_SHA256, PrivateKey, Sender};
        let public_key = PrivateKey::generate(&DHKEM_X25519_HKDF_SHA256)
            .unwrap()
            .public_key();
        b.iter(|| black_box(Sender::new(rind_suite(), &public_key, INFO).unwrap()));
    });

    group.bench_function("aws-lc-rs", |b| {
        let (public_key, _) = AWS_LC_RS.generate_key_pair().unwrap();
        b.iter(|| black_box(AWS_LC_RS.setup_sealer(INFO, &public_key).unwrap()));
    });

    group.bench_function("rustcrypto", |b| {
        use hpke::{Kem, OpModeS};
        let (_, public_key) = RcKem::gen_keypair();
        b.iter(|| {
            black_box(
                hpke::setup_sender::<RcAead, RcKdf, RcKem>(&OpModeS::Base, &public_key, INFO)
                    .unwrap(),
            )
        });
    });

    group.bench_function("libcrux", |b| {
        let mut hpke = libcrux_hpke();
        let key_pair = hpke.generate_key_pair().unwrap();
        b.iter(|| {
            black_box(
                hpke.setup_sender(key_pair.public_key(), INFO, None, None, None)
                    .unwrap(),
            )
        });
    });
}

// Decapsulate the sender's key and derive the same context.
fn setup_recipient(c: &mut Criterion) {
    let mut group = c.benchmark_group("hpke-x25519-setup-recipient");
    group.throughput(Throughput::Elements(1));

    group.bench_function("rind", |b| {
        use rind::hpke::{DHKEM_X25519_HKDF_SHA256, PrivateKey, Recipient, Sender};
        let private_key = PrivateKey::generate(&DHKEM_X25519_HKDF_SHA256).unwrap();
        let (enc, _) = Sender::new(rind_suite(), &private_key.public_key(), INFO).unwrap();
        b.iter(|| {
            black_box(Recipient::new(rind_suite(), &private_key, enc.as_ref(), INFO).unwrap())
        });
    });

    group.bench_function("aws-lc-rs", |b| {
        let (public_key, private_key) = AWS_LC_RS.generate_key_pair().unwrap();
        let (enc, _) = AWS_LC_RS.setup_sealer(INFO, &public_key).unwrap();
        b.iter(|| black_box(AWS_LC_RS.setup_opener(&enc, INFO, &private_key).unwrap()));
    });

    group.bench_function("rustcrypto", |b| {
        use hpke::{Kem, OpModeR, OpModeS};
        let (private_key, public_key) = RcKem::gen_keypair();
        let (enc, _) =
            hpke::setup_sender::<RcAead, RcKdf, RcKem>(&OpModeS::Base, &public_key, INFO).unwrap();
        b.iter(|| {
            black_box(
                hpke::setup_receiver::<RcAead, RcKdf, RcKem>(
                    &OpModeR::Base,
                    &private_key,
                    &enc,
                    INFO,
                )
                .unwrap(),
            )
        });
    });

    group.bench_function("libcrux", |b| {
        let mut hpke = libcrux_hpke();
        let key_pair = hpke.generate_key_pair().unwrap();
        let (enc, _) = hpke
            .setup_sender(key_pair.public_key(), INFO, None, None, None)
            .unwrap();
        b.iter(|| {
            black_box(
                hpke.setup_receiver(&enc, key_pair.private_key(), INFO, None, None, None)
                    .unwrap(),
            )
        });
    });
}

// Seal the next message of an established context. rind and `hpke` seal in
// place into a reused buffer; aws-lc-rs (through rustls) and hpke-rs only
// return a new one.
fn seal(c: &mut Criterion) {
    let mut group = c.benchmark_group("hpke-x25519-aes128-gcm-seal");
    group.throughput(Throughput::Bytes(MESSAGE.len() as u64));

    group.bench_function("rind/1350B", |b| {
        use rind::hpke::{DHKEM_X25519_HKDF_SHA256, PrivateKey, Sender};
        let public_key = PrivateKey::generate(&DHKEM_X25519_HKDF_SHA256)
            .unwrap()
            .public_key();
        let (_, mut sender) = Sender::new(rind_suite(), &public_key, INFO).unwrap();
        let mut buffer = Vec::with_capacity(MESSAGE.len() + 16);
        b.iter(|| {
            buffer.clear();
            buffer.extend_from_slice(&MESSAGE);
            sender.seal_in_place_append_tag(AAD, &mut buffer).unwrap();
            black_box(&buffer);
        });
    });

    group.bench_function("aws-lc-rs/1350B", |b| {
        let (public_key, _) = AWS_LC_RS.generate_key_pair().unwrap();
        let (_, mut sealer) = AWS_LC_RS.setup_sealer(INFO, &public_key).unwrap();
        b.iter(|| black_box(sealer.seal(AAD, &MESSAGE).unwrap()));
    });

    group.bench_function("rustcrypto/1350B", |b| {
        use hpke::{Kem, OpModeS, Serializable};
        let (_, public_key) = RcKem::gen_keypair();
        let (_, mut sender) =
            hpke::setup_sender::<RcAead, RcKdf, RcKem>(&OpModeS::Base, &public_key, INFO).unwrap();
        let mut buffer = Vec::with_capacity(MESSAGE.len() + 16);
        b.iter(|| {
            buffer.clear();
            buffer.extend_from_slice(&MESSAGE);
            let tag = sender
                .seal_inout_detached(buffer.as_mut_slice().into(), AAD)
                .unwrap();
            buffer.extend_from_slice(&tag.to_bytes());
            black_box(&buffer);
        });
    });

    group.bench_function("libcrux/1350B", |b| {
        let mut hpke = libcrux_hpke();
        let key_pair = hpke.generate_key_pair().unwrap();
        let (_, mut sender) = hpke
            .setup_sender(key_pair.public_key(), INFO, None, None, None)
            .unwrap();
        b.iter(|| black_box(sender.seal(AAD, &MESSAGE).unwrap()));
    });
}

// Open a context's first message. A context opens each sequence number once,
// so each iteration gets a fresh context and ciphertext, made and dropped untimed.
fn open(c: &mut Criterion) {
    let mut group = c.benchmark_group("hpke-x25519-aes128-gcm-open");
    group.throughput(Throughput::Bytes(MESSAGE.len() as u64));

    group.bench_function("rind/1350B", |b| {
        use rind::hpke::{DHKEM_X25519_HKDF_SHA256, PrivateKey, Recipient, Sender};
        let private_key = PrivateKey::generate(&DHKEM_X25519_HKDF_SHA256).unwrap();
        let public_key = private_key.public_key();
        b.iter_batched_ref(
            || {
                let (enc, mut sender) = Sender::new(rind_suite(), &public_key, INFO).unwrap();
                let mut ciphertext = MESSAGE.to_vec();
                sender
                    .seal_in_place_append_tag(AAD, &mut ciphertext)
                    .unwrap();
                let recipient =
                    Recipient::new(rind_suite(), &private_key, enc.as_ref(), INFO).unwrap();
                (recipient, ciphertext)
            },
            |(recipient, ciphertext)| {
                black_box(recipient.open_in_place(AAD, ciphertext).unwrap().len());
            },
            BatchSize::SmallInput,
        );
    });

    group.bench_function("aws-lc-rs/1350B", |b| {
        let (public_key, private_key) = AWS_LC_RS.generate_key_pair().unwrap();
        b.iter_batched_ref(
            || {
                let (enc, mut sealer) = AWS_LC_RS.setup_sealer(INFO, &public_key).unwrap();
                let ciphertext = sealer.seal(AAD, &MESSAGE).unwrap();
                let opener = AWS_LC_RS.setup_opener(&enc, INFO, &private_key).unwrap();
                (opener, ciphertext)
            },
            |(opener, ciphertext)| black_box(opener.open(AAD, ciphertext).unwrap()),
            BatchSize::SmallInput,
        );
    });

    group.bench_function("rustcrypto/1350B", |b| {
        use hpke::{Deserializable, Kem, OpModeR, OpModeS, Serializable};
        let (private_key, public_key) = RcKem::gen_keypair();
        b.iter_batched_ref(
            || {
                let (enc, mut sender) =
                    hpke::setup_sender::<RcAead, RcKdf, RcKem>(&OpModeS::Base, &public_key, INFO)
                        .unwrap();
                // Sealed the way the seal row does, so a wrong tag there fails here.
                let mut ciphertext = MESSAGE.to_vec();
                let tag = sender
                    .seal_inout_detached(ciphertext.as_mut_slice().into(), AAD)
                    .unwrap();
                ciphertext.extend_from_slice(&tag.to_bytes());
                let recipient = hpke::setup_receiver::<RcAead, RcKdf, RcKem>(
                    &OpModeR::Base,
                    &private_key,
                    &enc,
                    INFO,
                )
                .unwrap();
                (recipient, ciphertext)
            },
            |(recipient, ciphertext)| {
                let (message, tag) = ciphertext.split_at_mut(MESSAGE.len());
                let tag = hpke::aead::AeadTag::<RcAead>::from_bytes(tag).unwrap();
                recipient
                    .open_inout_detached(message.into(), AAD, &tag)
                    .unwrap();
                black_box(&ciphertext);
            },
            BatchSize::SmallInput,
        );
    });

    group.bench_function("libcrux/1350B", |b| {
        let mut hpke = libcrux_hpke();
        let key_pair = hpke.generate_key_pair().unwrap();
        b.iter_batched_ref(
            || {
                let (enc, mut sender) = hpke
                    .setup_sender(key_pair.public_key(), INFO, None, None, None)
                    .unwrap();
                let ciphertext = sender.seal(AAD, &MESSAGE).unwrap();
                let recipient = hpke
                    .setup_receiver(&enc, key_pair.private_key(), INFO, None, None, None)
                    .unwrap();
                (recipient, ciphertext)
            },
            |(recipient, ciphertext)| black_box(recipient.open(AAD, ciphertext).unwrap()),
            BatchSize::SmallInput,
        );
    });
}

criterion_group!(benches, setup_sender, setup_recipient, seal, open);
criterion_main!(benches);
