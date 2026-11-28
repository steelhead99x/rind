//! HPKE's base mode with DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, and
//! AES-128-GCM, the suite MLS and ECH default to: each side's setup, then
//! one QUIC-datagram-sized message sealed and opened.
#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;
#[cfg(not(target_arch = "xtensa"))]
use std::sync::Once;

#[cfg(not(target_arch = "xtensa"))]
use common::{Dit, Size};

#[cfg(not(target_arch = "xtensa"))]
const INFO: &[u8] = b"rind-bench info";
#[cfg(not(target_arch = "xtensa"))]
const AAD: &[u8] = b"rind-bench aad";
#[cfg(not(target_arch = "xtensa"))]
const MESSAGE: [u8; 1350] = [0x5a; 1350];

/// The message's one size, which the seal and open rows are named by.
#[cfg(not(target_arch = "xtensa"))]
const SIZE: [Size; 1] = [Size::new(MESSAGE.len(), "1350B")];

#[cfg(not(target_arch = "xtensa"))]
type RcKem = hpke::kem::X25519HkdfSha256;
#[cfg(not(target_arch = "xtensa"))]
type RcKdf = hpke::kdf::HkdfSha256;
#[cfg(not(target_arch = "xtensa"))]
type RcAead = hpke::aead::AesGcm128;

#[cfg(not(target_arch = "xtensa"))]
fn rind_suite() -> rind::hpke::Suite {
    rind::hpke::Suite {
        kdf: &rind::hpke::HKDF_SHA256,
        aead: &rind::hpke::AES_128_GCM,
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn libcrux_hpke() -> hpke_rs::Hpke<hpke_rs::libcrux::HpkeLibcrux> {
    use hpke_rs::hpke_types::{AeadAlgorithm, KdfAlgorithm, KemAlgorithm};
    hpke_rs::Hpke::new(
        hpke_rs::Mode::Base,
        KemAlgorithm::DhKem25519,
        KdfAlgorithm::HkdfSha256,
        AeadAlgorithm::Aes128Gcm,
    )
}

#[cfg(not(target_arch = "xtensa"))]
const AWS_LC_RS: &dyn rustls::crypto::hpke::Hpke =
    rustls::crypto::aws_lc_rs::hpke::DH_KEM_X25519_HKDF_SHA256_AES_128;

/// Checks, once a process, that every library speaks the same suite as
/// rind: each opens a message rind sealed to it, and rind opens one each
/// sealed to rind. Every row's setup runs it, so a row never times a library
/// that disagrees.
#[cfg(not(target_arch = "xtensa"))]
fn check_interop() {
    static CHECKED: Once = Once::new();
    CHECKED.call_once(interop);
}

#[cfg(not(target_arch = "xtensa"))]
fn interop() {
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

#[cfg(not(target_arch = "xtensa"))]
fn rind_key() -> rind::hpke::PrivateKey {
    check_interop();
    rind::hpke::PrivateKey::generate(&rind::hpke::DHKEM_X25519_HKDF_SHA256).unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
fn aws_lc_rs_key() -> (
    rustls::crypto::hpke::HpkePublicKey,
    rustls::crypto::hpke::HpkePrivateKey,
) {
    check_interop();
    AWS_LC_RS.generate_key_pair().unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
fn rustcrypto_key() -> (
    <RcKem as hpke::Kem>::PrivateKey,
    <RcKem as hpke::Kem>::PublicKey,
) {
    use hpke::Kem;
    check_interop();
    RcKem::gen_keypair()
}

#[cfg(not(target_arch = "xtensa"))]
fn libcrux_key() -> (
    hpke_rs::Hpke<hpke_rs::libcrux::HpkeLibcrux>,
    hpke_rs::HpkeKeyPair,
) {
    check_interop();
    let mut hpke = libcrux_hpke();
    let key_pair = hpke.generate_key_pair().unwrap();
    (hpke, key_pair)
}

/// Encapsulate to the recipient's parsed public key and derive the context.
#[cfg(not(target_arch = "xtensa"))]
mod hpke_x25519_setup_sender {
    use swole::bench;

    use super::*;

    fn rind_input() -> Dit<rind::hpke::PrivateKey> {
        Dit::hold(rind_key())
    }

    #[bench(setup = rind_input)]
    fn rind(private_key: &Dit<rind::hpke::PrivateKey>) {
        black_box(rind::hpke::Sender::new(rind_suite(), private_key.public_key(), INFO).unwrap());
    }

    fn aws_lc_rs_input() -> rustls::crypto::hpke::HpkePublicKey {
        aws_lc_rs_key().0
    }

    #[bench(setup = aws_lc_rs_input)]
    fn aws_lc_rs(public_key: &rustls::crypto::hpke::HpkePublicKey) {
        black_box(AWS_LC_RS.setup_sealer(INFO, public_key).unwrap());
    }

    fn rustcrypto_input() -> <RcKem as hpke::Kem>::PublicKey {
        rustcrypto_key().1
    }

    #[bench(setup = rustcrypto_input)]
    fn rustcrypto(public_key: &<RcKem as hpke::Kem>::PublicKey) {
        black_box(
            hpke::setup_sender::<RcAead, RcKdf, RcKem>(&hpke::OpModeS::Base, public_key, INFO)
                .unwrap(),
        );
    }

    #[bench(setup = libcrux_key)]
    fn libcrux(
        (hpke, key_pair): &mut (
            hpke_rs::Hpke<hpke_rs::libcrux::HpkeLibcrux>,
            hpke_rs::HpkeKeyPair,
        ),
    ) {
        black_box(
            hpke.setup_sender(key_pair.public_key(), INFO, None, None, None)
                .unwrap(),
        );
    }
}

/// Decapsulate the sender's key and derive the same context.
#[cfg(not(target_arch = "xtensa"))]
mod hpke_x25519_setup_recipient {
    use swole::bench;

    use super::*;

    fn rind_input() -> Dit<(rind::hpke::PrivateKey, rind::hpke::EncapsulatedKey)> {
        let private_key = rind_key();
        let (enc, _) =
            rind::hpke::Sender::new(rind_suite(), private_key.public_key(), INFO).unwrap();
        Dit::hold((private_key, enc))
    }

    #[bench(setup = rind_input)]
    fn rind(input: &Dit<(rind::hpke::PrivateKey, rind::hpke::EncapsulatedKey)>) {
        let (private_key, enc) = &**input;
        black_box(
            rind::hpke::Recipient::new(rind_suite(), private_key, enc.as_ref(), INFO).unwrap(),
        );
    }

    fn aws_lc_rs_input() -> (
        rustls::crypto::hpke::EncapsulatedSecret,
        rustls::crypto::hpke::HpkePrivateKey,
    ) {
        let (public_key, private_key) = aws_lc_rs_key();
        let (enc, _) = AWS_LC_RS.setup_sealer(INFO, &public_key).unwrap();
        (enc, private_key)
    }

    #[bench(setup = aws_lc_rs_input)]
    fn aws_lc_rs(
        (enc, private_key): &(
            rustls::crypto::hpke::EncapsulatedSecret,
            rustls::crypto::hpke::HpkePrivateKey,
        ),
    ) {
        black_box(AWS_LC_RS.setup_opener(enc, INFO, private_key).unwrap());
    }

    fn rustcrypto_input() -> (
        <RcKem as hpke::Kem>::PrivateKey,
        <RcKem as hpke::Kem>::EncappedKey,
    ) {
        let (private_key, public_key) = rustcrypto_key();
        let (enc, _) =
            hpke::setup_sender::<RcAead, RcKdf, RcKem>(&hpke::OpModeS::Base, &public_key, INFO)
                .unwrap();
        (private_key, enc)
    }

    #[bench(setup = rustcrypto_input)]
    fn rustcrypto(
        (private_key, enc): &(
            <RcKem as hpke::Kem>::PrivateKey,
            <RcKem as hpke::Kem>::EncappedKey,
        ),
    ) {
        black_box(
            hpke::setup_receiver::<RcAead, RcKdf, RcKem>(
                &hpke::OpModeR::Base,
                private_key,
                enc,
                INFO,
            )
            .unwrap(),
        );
    }

    type Libcrux = (
        hpke_rs::Hpke<hpke_rs::libcrux::HpkeLibcrux>,
        hpke_rs::HpkeKeyPair,
        Vec<u8>,
    );

    fn libcrux_input() -> Libcrux {
        let (mut hpke, key_pair) = libcrux_key();
        let (enc, _) = hpke
            .setup_sender(key_pair.public_key(), INFO, None, None, None)
            .unwrap();
        (hpke, key_pair, enc)
    }

    #[bench(setup = libcrux_input)]
    fn libcrux((hpke, key_pair, enc): &mut Libcrux) {
        black_box(
            hpke.setup_receiver(enc, key_pair.private_key(), INFO, None, None, None)
                .unwrap(),
        );
    }
}

/// Seal the next message of an established context. rind and `hpke` seal in
/// place into a reused buffer; aws-lc-rs (through rustls) and hpke-rs only
/// return a new one.
#[cfg(not(target_arch = "xtensa"))]
mod hpke_x25519_aes128_gcm_seal {
    use swole::bench;

    use super::*;

    fn buffer() -> Vec<u8> {
        Vec::with_capacity(MESSAGE.len() + 16)
    }

    fn rind_input(_: Size) -> Dit<(rind::hpke::Sender, Vec<u8>)> {
        let private_key = rind_key();
        let (_, sender) =
            rind::hpke::Sender::new(rind_suite(), private_key.public_key(), INFO).unwrap();
        Dit::hold((sender, buffer()))
    }

    #[bench(args = SIZE, setup = rind_input)]
    fn rind(input: &mut Dit<(rind::hpke::Sender, Vec<u8>)>) {
        let (sender, buffer) = &mut **input;
        buffer.clear();
        buffer.extend_from_slice(&MESSAGE);
        sender.seal_in_place_append_tag(AAD, buffer).unwrap();
        black_box(buffer);
    }

    fn aws_lc_rs_input(_: Size) -> Box<dyn rustls::crypto::hpke::HpkeSealer> {
        let (public_key, _) = aws_lc_rs_key();
        AWS_LC_RS.setup_sealer(INFO, &public_key).unwrap().1
    }

    #[bench(args = SIZE, setup = aws_lc_rs_input)]
    fn aws_lc_rs(sealer: &mut Box<dyn rustls::crypto::hpke::HpkeSealer>) {
        black_box(sealer.seal(AAD, &MESSAGE).unwrap());
    }

    type RustCrypto = (hpke::aead::AeadCtxS<RcAead, RcKdf, RcKem>, Vec<u8>);

    fn rustcrypto_input(_: Size) -> RustCrypto {
        let (_, public_key) = rustcrypto_key();
        let (_, sender) =
            hpke::setup_sender::<RcAead, RcKdf, RcKem>(&hpke::OpModeS::Base, &public_key, INFO)
                .unwrap();
        (sender, buffer())
    }

    #[bench(args = SIZE, setup = rustcrypto_input)]
    fn rustcrypto((sender, buffer): &mut RustCrypto) {
        use hpke::Serializable;
        buffer.clear();
        buffer.extend_from_slice(&MESSAGE);
        let tag = sender
            .seal_inout_detached(buffer.as_mut_slice().into(), AAD)
            .unwrap();
        buffer.extend_from_slice(&tag.to_bytes());
        black_box(buffer);
    }

    fn libcrux_input(_: Size) -> hpke_rs::Context<hpke_rs::libcrux::HpkeLibcrux> {
        let (mut hpke, key_pair) = libcrux_key();
        hpke.setup_sender(key_pair.public_key(), INFO, None, None, None)
            .unwrap()
            .1
    }

    #[bench(args = SIZE, setup = libcrux_input)]
    fn libcrux(sender: &mut hpke_rs::Context<hpke_rs::libcrux::HpkeLibcrux>) {
        black_box(sender.seal(AAD, &MESSAGE).unwrap());
    }
}

/// Open a context's first message. A context opens each sequence number
/// once, so each call gets a fresh context and ciphertext, made untimed, and
/// returns them to be dropped untimed too.
#[cfg(not(target_arch = "xtensa"))]
mod hpke_x25519_aes128_gcm_open {
    use swole::bench;

    use super::*;

    type Rind = (rind::cpu::Dit, rind::hpke::Recipient, Vec<u8>);

    /// A recipient and its first ciphertext, with the DIT guard held across
    /// the call that consumes them.
    fn rind_input(_: Size) -> Rind {
        let private_key = rind_key();
        let (enc, mut sender) =
            rind::hpke::Sender::new(rind_suite(), private_key.public_key(), INFO).unwrap();
        let mut ciphertext = MESSAGE.to_vec();
        sender
            .seal_in_place_append_tag(AAD, &mut ciphertext)
            .unwrap();
        let recipient =
            rind::hpke::Recipient::new(rind_suite(), &private_key, enc.as_ref(), INFO).unwrap();
        (rind::cpu::Dit::hold(), recipient, ciphertext)
    }

    #[bench(args = SIZE, setup = rind_input)]
    fn rind((dit, mut recipient, mut ciphertext): Rind) -> impl Sized + use<> {
        let len = recipient.open_in_place(AAD, &mut ciphertext).unwrap().len();
        (len, dit, recipient, ciphertext)
    }

    type AwsLcRs = (Box<dyn rustls::crypto::hpke::HpkeOpener>, Vec<u8>);

    fn aws_lc_rs_input(_: Size) -> AwsLcRs {
        let (public_key, private_key) = aws_lc_rs_key();
        let (enc, mut sealer) = AWS_LC_RS.setup_sealer(INFO, &public_key).unwrap();
        let ciphertext = sealer.seal(AAD, &MESSAGE).unwrap();
        let opener = AWS_LC_RS.setup_opener(&enc, INFO, &private_key).unwrap();
        (opener, ciphertext)
    }

    #[bench(args = SIZE, setup = aws_lc_rs_input)]
    fn aws_lc_rs((mut opener, ciphertext): AwsLcRs) -> impl Sized + use<> {
        (opener.open(AAD, &ciphertext).unwrap(), opener, ciphertext)
    }

    type RustCrypto = (hpke::aead::AeadCtxR<RcAead, RcKdf, RcKem>, Vec<u8>);

    fn rustcrypto_input(_: Size) -> RustCrypto {
        use hpke::Serializable;
        let (private_key, public_key) = rustcrypto_key();
        let (enc, mut sender) =
            hpke::setup_sender::<RcAead, RcKdf, RcKem>(&hpke::OpModeS::Base, &public_key, INFO)
                .unwrap();
        // Sealed the way the seal row does, so a wrong tag there fails here.
        let mut ciphertext = MESSAGE.to_vec();
        let tag = sender
            .seal_inout_detached(ciphertext.as_mut_slice().into(), AAD)
            .unwrap();
        ciphertext.extend_from_slice(&tag.to_bytes());
        let recipient = hpke::setup_receiver::<RcAead, RcKdf, RcKem>(
            &hpke::OpModeR::Base,
            &private_key,
            &enc,
            INFO,
        )
        .unwrap();
        (recipient, ciphertext)
    }

    #[bench(args = SIZE, setup = rustcrypto_input)]
    fn rustcrypto((mut recipient, mut ciphertext): RustCrypto) -> impl Sized + use<> {
        use hpke::Deserializable;
        let (message, tag) = ciphertext.split_at_mut(MESSAGE.len());
        let tag = hpke::aead::AeadTag::<RcAead>::from_bytes(tag).unwrap();
        recipient
            .open_inout_detached(message.into(), AAD, &tag)
            .unwrap();
        (recipient, ciphertext)
    }

    type Libcrux = (hpke_rs::Context<hpke_rs::libcrux::HpkeLibcrux>, Vec<u8>);

    fn libcrux_input(_: Size) -> Libcrux {
        let (mut hpke, key_pair) = libcrux_key();
        let (enc, mut sender) = hpke
            .setup_sender(key_pair.public_key(), INFO, None, None, None)
            .unwrap();
        let ciphertext = sender.seal(AAD, &MESSAGE).unwrap();
        let recipient = hpke
            .setup_receiver(&enc, key_pair.private_key(), INFO, None, None, None)
            .unwrap();
        (recipient, ciphertext)
    }

    #[bench(args = SIZE, setup = libcrux_input)]
    fn libcrux((mut recipient, ciphertext): Libcrux) -> impl Sized + use<> {
        (
            recipient.open(AAD, &ciphertext).unwrap(),
            recipient,
            ciphertext,
        )
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
