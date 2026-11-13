// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ristretto255's tests, which run on every backend.

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use proptest::prelude::*;
use serde::Deserialize;

use super::hash_to_curve::expand_message_xmd;
use super::ristretto255::{Element, Scalar};
use super::sha2::Sha512Context;
use crate::low;
use crate::test::wycheproof;

fn bytes<const N: usize>(hex: &str) -> [u8; N] {
    hex::decode(hex.replace(' ', ""))
        .unwrap()
        .try_into()
        .unwrap()
}

fn scalar(n: u64) -> Scalar {
    let mut b = [0u8; 32];
    b[..8].copy_from_slice(&n.to_le_bytes());
    Scalar::from_canonical_bytes(&b).unwrap()
}

/// RFC 9496 A.1: `[i]G` for `i` in `0..16`.
const MULTIPLES: [&str; 16] = [
    "0000000000000000000000000000000000000000000000000000000000000000",
    "e2f2ae0a6abc4e71a884a961c500515f58e30b6aa582dd8db6a65945e08d2d76",
    "6a493210f7499cd17fecb510ae0cea23a110e8d5b901f8acadd3095c73a3b919",
    "94741f5d5d52755ece4f23f044ee27d5d1ea1e2bd196b462166b16152a9d0259",
    "da80862773358b466ffadfe0b3293ab3d9fd53c5ea6c955358f568322daf6a57",
    "e882b131016b52c1d3337080187cf768423efccbb517bb495ab812c4160ff44e",
    "f64746d3c92b13050ed8d80236a7f0007c3b3f962f5ba793d19a601ebb1df403",
    "44f53520926ec81fbd5a387845beb7df85a96a24ece18738bdcfa6a7822a176d",
    "903293d8f2287ebe10e2374dc1a53e0bc887e592699f02d077d5263cdd55601c",
    "02622ace8f7303a31cafc63f8fc48fdc16e1c8c8d234b2f0d6685282a9076031",
    "20706fd788b2720a1ed2a5dad4952b01f413bcf0e7564de8cdc816689e2db95f",
    "bce83f8ba5dd2fa572864c24ba1810f9522bc6004afe95877ac73241cafdab42",
    "e4549ee16b9aa03099ca208c67adafcafa4c3f3e4e5303de6026e3ca8ff84460",
    "aa52e000df2e16f55fb1032fc33bc42742dad6bd5a8fc0be0167436c5948501f",
    "46376b80f409b29dc2b5f6f0c52591990896e5716f41477cd30085ab7f10301e",
    "e0c418f7c8d9c4cdd7395b93ea124f3ad99021bb681dfc3302a9d99a2e53e64e",
];

#[test]
fn rfc9496_multiples_of_the_generator() {
    let g = Element::mul_base(&scalar(1));
    let mut sum = Element::mul_base(&scalar(0));
    for (i, want) in MULTIPLES.iter().enumerate() {
        let want = bytes::<32>(want);
        let i = scalar(i as u64);
        assert_eq!(sum.to_bytes(), want, "sum");
        assert_eq!(Element::mul_base(&i).to_bytes(), want, "mul_base");
        assert_eq!(g.mul(&i).to_bytes(), want, "mul");
        let decoded = Element::from_bytes(&want).unwrap();
        assert_eq!(decoded.to_bytes(), want, "decode");
        sum = sum.add(&g);
    }
}

#[test]
fn rfc9496_invalid_encodings() {
    for encoding in [
        // Non-canonical field encodings.
        "00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        "f3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        // Negative field elements.
        "0100000000000000000000000000000000000000000000000000000000000000",
        "01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        "ed57ffd8c914fb201471d1c3d245ce3c746fcbe63a3679d51b6a516ebebe0e20",
        "c34c4e1826e5d403b78e246e88aa051c36ccf0aafebffe137d148a2bf9104562",
        "c940e5a4404157cfb1628b108db051a8d439e1a421394ec4ebccb9ec92a8ac78",
        "47cfc5497c53dc8e61c91d17fd626ffb1c49e2bca94eed052281b510b1117a24",
        "f1c6165d33367351b0da8f6e4511010c68174a03b6581212c71c0e1d026c3c72",
        "87260f7a2f12495118360f02c26a470f450dadf34a413d21042b43b9d93e1309",
        // Non-square x^2.
        "26948d35ca62e643e26a83177332e6b6afeb9d08e4268b650f1f5bbd8d81d371",
        "4eac077a713c57b4f4397629a4145982c661f48044dd3f96427d40b147d9742f",
        "de6a7b00deadc788eb6b6c8d20c0ae96c2f2019078fa604fee5b87d6e989ad7b",
        "bcab477be20861e01e4a0e295284146a510150d9817763caf1a6f4b422d67042",
        "2a292df7e32cababbd9de088d1d1abec9fc0440f637ed2fba145094dc14bea08",
        "f4a9e534fc0d216c44b218fa0c42d99635a0127ee2e53c712f70609649fdff22",
        "8268436f8c4126196cf64b3c7ddbda90746a378625f9813dd9b8457077256731",
        "2810e5cbc2cc4d4eece54f61c6f69758e289aa7ab440b3cbeaa21995c2f4232b",
        // Negative x * y value.
        "3eb858e78f5a7254d8c9731174a94f76755fd3941c0ac93735c07ba14579630e",
        "a45fdc55c76448c049a1ab33f17023edfb2be3581e9c7aade8a6125215e04220",
        "d483fe813c6ba647ebbfd3ec41adca1c6130c2beeee9d9bf065c8d151c5f396e",
        "8a2e1d30050198c65a54483123960ccc38aef6848e1ec8f5f780e8523769ba32",
        "32888462f8b486c68ad7dd9610be5192bbeaf3b443951ac1a8118419d9fa097b",
        "227142501b9d4355ccba290404bde41575b037693cef1f438c47f8fbf35d1165",
        "5c37cc491da847cfeb9281d407efc41e15144c876e0170b499a96a22ed31e01e",
        "445425117cb8c90edcbc7c1cc0e74f747f2c1efa5630a967c64f287792a48a4b",
        // s = -1, which causes y = 0.
        "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
    ] {
        assert!(
            Element::from_bytes(&bytes(encoding)).is_none(),
            "{encoding}"
        );
    }
}

#[test]
fn rfc9496_from_uniform_bytes() {
    for (input, output) in [
        (
            "5d1be09e3d0c82fc538112490e35701979d99e06ca3e2b5b54bffe8b4dc772c14d98b696a1bbfb5ca32c436cc61c16563790306c79eaca7705668b47dffe5bb6",
            "3066f82a1a747d45120d1740f14358531a8f04bbffe6a819f86dfe50f44a0a46",
        ),
        (
            "f116b34b8f17ceb56e8732a60d913dd10cce47a6d53bee9204be8b44f6678b270102a56902e2488c46120e9276cfe54638286b9e4b3cdb470b542d46c2068d38",
            "f26e5b6f7d362d2d2a94c5d0e7602cb4773c95a2e5c31a64f133189fa76ed61b",
        ),
        (
            "8422e1bbdaab52938b81fd602effb6f89110e1e57208ad12d9ad767e2e25510c27140775f9337088b982d83d7fcf0b2fa1edffe51952cbe7365e95c86eaf325c",
            "006ccd2a9e6867e6a2c5cea83d3302cc9de128dd2a9a57dd8ee7b9d7ffe02826",
        ),
        (
            "ac22415129b61427bf464e17baee8db65940c233b98afce8d17c57beeb7876c2150d15af1cb1fb824bbd14955f2b57d08d388aab431a391cfc33d5bafb5dbbaf",
            "f8f0c87cf237953c5890aec3998169005dae3eca1fbb04548c635953c817f92a",
        ),
        (
            "165d697a1ef3d5cf3c38565beefcf88c0f282b8e7dbd28544c483432f1cec7675debea8ebb4e5fe7d6f6e5db15f15587ac4d4d4a1de7191e0c1ca6664abcc413",
            "ae81e7dedf20a497e10c304a765c1767a42d6e06029758d2d7e8ef7cc4c41179",
        ),
        (
            "a836e6c9a9ca9f1e8d486273ad56a78c70cf18f0ce10abb1c7172ddd605d7fd2979854f47ae1ccf204a33102095b4200e5befc0465accc263175485f0e17ea5c",
            "e2705652ff9f5e44d3e841bf1c251cf7dddb77d140870d1ab2ed64f1a9ce8628",
        ),
        (
            "2cdc11eaeb95daf01189417cdddbf95952993aa9cb9c640eb5058d09702c74622c9965a697a3b345ec24ee56335b556e677b30e6f90ac77d781064f866a3c982",
            "80bd07262511cdde4863f8a7434cef696750681cb9510eea557088f76d9e5065",
        ),
        // Inputs whose halves are unreduced or carry the top bit, which the
        // map clears.
        (
            "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1200000000000000000000000000000000000000000000000000000000000000",
            "304282791023b73128d277bdcb5c7746ef2eac08dde9f2983379cb8e5ef0517f",
        ),
        (
            "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            "304282791023b73128d277bdcb5c7746ef2eac08dde9f2983379cb8e5ef0517f",
        ),
        (
            "0000000000000000000000000000000000000000000000000000000000000080ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
            "304282791023b73128d277bdcb5c7746ef2eac08dde9f2983379cb8e5ef0517f",
        ),
        (
            "00000000000000000000000000000000000000000000000000000000000000001200000000000000000000000000000000000000000000000000000000000080",
            "304282791023b73128d277bdcb5c7746ef2eac08dde9f2983379cb8e5ef0517f",
        ),
    ] {
        let got = Element::from_uniform_bytes(&bytes(input)).to_bytes();
        assert_eq!(got, bytes(output), "{input}");
    }
}

/// RFC 9497 A.1.1, OPRF(ristretto255, SHA-512)'s blinding, evaluation, and
/// unblinding, and A.1.2's public key.
#[test]
fn rfc9497_oprf() {
    const DST: &[u8] = b"HashToGroup-OPRFV1-\x00-ristretto255-SHA512";
    let sk = Scalar::from_canonical_bytes(&bytes(
        "5ebcea5ee37023ccb9fc2d2019f9d7737be85591ae8652ffa9ef0f4d37063b0e",
    ))
    .unwrap();
    let blind = Scalar::from_canonical_bytes(&bytes(
        "64d37aed22a27f5191de1c1d69fadb899d8862b58eb4220029e036ec4c1f6706",
    ))
    .unwrap();
    for (input, blinded, evaluated, output) in [
        (
            "00",
            "609a0ae68c15a3cf6903766461307e5c8bb2f95e7e6550e1ffa2dc99e412803c",
            "7ec6578ae5120958eb2db1745758ff379e77cb64fe77b0b2d8cc917ea0869c7e",
            "527759c3d9366f277d8c6020418d96bb393ba2afb20ff90df23fb7708264e2f3ab9135e3bd69955851de4b1f9fe8a0973396719b7912ba9ee8aa7d0b5e24bcf6",
        ),
        (
            "5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a",
            "da27ef466870f5f15296299850aa088629945a17d1f5b7f5ff043f76b3c06418",
            "b4cbf5a4f1eeda5a63ce7b77c7d23f461db3fcab0dd28e4e17cecb5c90d02c25",
            "f4a74c9c592497375e796aa837e907b1a045d34306a749db9f34221f7e750cb4f2a6413a6bf6fa5e19ba6348eb673934a722a7ede2e7621306d18951e7cf2c73",
        ),
    ] {
        let input = hex::decode(input).unwrap();
        let mut uniform = [0u8; 64];
        expand_message_xmd::<Sha512Context>(&[&input], DST, &mut uniform).unwrap();
        let point = Element::from_uniform_bytes(&uniform);
        let blinded_element = point.mul(&blind).to_bytes();
        assert_eq!(blinded_element, bytes(blinded));

        let evaluated_element = Element::from_bytes(&blinded_element)
            .unwrap()
            .mul(&sk)
            .to_bytes();
        assert_eq!(evaluated_element, bytes(evaluated));

        let unblinded = Element::from_bytes(&evaluated_element)
            .unwrap()
            .mul(&blind.invert().unwrap())
            .to_bytes();
        let mut h = Sha512Context::new();
        h.update(&u16::try_from(input.len()).unwrap().to_be_bytes());
        h.update(&input);
        h.update(&32u16.to_be_bytes());
        h.update(&unblinded);
        h.update(b"Finalize");
        assert_eq!(h.finish(), bytes::<64>(output));
    }

    let sk = Scalar::from_canonical_bytes(&bytes(
        "e6f73f344b79b379f1a0dd37e07ff62e38d9f71345ce62ae3a9bc60b04ccd909",
    ))
    .unwrap();
    assert_eq!(
        Element::mul_base(&sk).to_bytes(),
        bytes::<32>("c803e2cc6b05fc15064549b5920659ca4a77b2cca6f04f6b357009335476ad4e")
    );
}

#[derive(Deserialize)]
struct ScalarTest {
    #[serde(rename = "tcId")]
    id: usize,
    #[serde(with = "hex::serde")]
    scalar: [u8; 32],
    #[serde(rename = "resultScalar", default, with = "hex::serde")]
    result_scalar: Vec<u8>,
    result: String,
}

#[test]
fn wycheproof_scalar_invert() {
    for test in wycheproof::<ScalarTest>("ristretto255_scalar_invert_test.json") {
        let inverse = Scalar::from_canonical_bytes(&test.scalar)
            .and_then(|s| s.invert())
            .map(|s| s.to_bytes().to_vec());
        match test.result.as_str() {
            "valid" => assert_eq!(inverse, Some(test.result_scalar), "{}", test.id),
            _ => assert_eq!(inverse, None, "{}", test.id),
        }
    }
}

#[test]
fn scalar_bounds() {
    // L, little-endian.
    let mut order = bytes::<32>("edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010");
    assert!(Scalar::from_canonical_bytes(&order).is_none());
    assert!(Scalar::from_canonical_bytes(&[0xff; 32]).is_none());
    order[0] -= 1;
    assert_eq!(
        Scalar::from_canonical_bytes(&order).unwrap().to_bytes(),
        order
    );

    // Zero has no inverse, however it was reached.
    assert!(
        Scalar::from_canonical_bytes(&[0; 32])
            .unwrap()
            .invert()
            .is_none()
    );
    assert!(Scalar::from_uniform_bytes(&[0; 64]).invert().is_none());
}

proptest! {
    // Miri takes four minutes over 64 cases, on the portable backend, where
    // this compares dalek with itself.
    #![proptest_config(ProptestConfig::with_cases(if cfg!(miri) { 4 } else { 64 }))]

    /// Every operation against curve25519-dalek's. On armv7 and the portable
    /// backend, which run dalek's, this checks only the wrapping.
    #[test]
    fn matches_dalek(
        a in any::<[u8; 64]>(),
        b in any::<[u8; 64]>(),
        s in any::<[u8; 64]>(),
        encoding in any::<[u8; 32]>(),
    ) {
        let (pa, pb) = (Element::from_uniform_bytes(&a), Element::from_uniform_bytes(&b));
        let (da, db) = (RistrettoPoint::from_uniform_bytes(&a), RistrettoPoint::from_uniform_bytes(&b));
        let (rs, ds) = (Scalar::from_uniform_bytes(&s), curve25519_dalek::Scalar::from_bytes_mod_order_wide(&s));
        prop_assert_eq!(rs.to_bytes(), ds.to_bytes());

        prop_assert_eq!(pa.to_bytes(), da.compress().to_bytes());
        prop_assert_eq!(pa.add(&pb).to_bytes(), (da + db).compress().to_bytes());
        prop_assert_eq!(pa.mul(&rs).to_bytes(), (da * ds).compress().to_bytes());
        prop_assert_eq!(Element::mul_base(&rs).to_bytes(), RistrettoPoint::mul_base(&ds).compress().to_bytes());
        prop_assert_eq!(rs.mul(&rs).to_bytes(), (ds * ds).to_bytes());
        let inverse = (ds != curve25519_dalek::Scalar::ZERO).then(|| ds.invert().to_bytes());
        prop_assert_eq!(rs.invert().map(|i| i.to_bytes()), inverse);

        // An encoding of an element, and an arbitrary one, which dalek
        // mostly rejects.
        for encoding in [da.compress().to_bytes(), encoding] {
            let ours = Element::from_bytes(&encoding).map(|e| e.to_bytes());
            let theirs = CompressedRistretto(encoding).decompress().map(|e| e.compress().to_bytes());
            prop_assert_eq!(ours, theirs);
        }
    }
}

/// Under `admin/ctgrind`, which marks these inputs secret, checks that no
/// branch or memory index depends on them.
#[test]
fn constant_time() {
    let uniform = low::ct::into_secret([0x5a; 64]);
    let scalar = Scalar::from_uniform_bytes(&low::ct::into_secret([0xa5; 64]));
    let canonical = Scalar::from_canonical_bytes(&low::ct::into_secret(scalar.to_bytes())).unwrap();
    let element = Element::from_uniform_bytes(&uniform);
    let product = element.mul(&canonical);
    let sum = product.add(&Element::mul_base(&scalar));
    let inverse = scalar.invert().unwrap();
    let encoding = low::ct::into_public(sum.mul(&scalar.mul(&inverse)).to_bytes());

    // dalek decodes in constant time only a public encoding.
    #[cfg(not(any(rind_backend = "arm", rind_backend = "portable")))]
    let encoding = low::ct::into_secret(encoding);
    let decoded = Element::from_bytes(&encoding).unwrap();
    assert_eq!(
        low::ct::into_public(decoded.to_bytes()),
        low::ct::into_public(sum.to_bytes())
    );
}
