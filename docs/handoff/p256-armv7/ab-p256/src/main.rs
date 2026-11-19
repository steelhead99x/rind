// usage: ab-p256 <lib: rind|rind2|awslc|ring|openssl> <op: keygen|ecdh|sign|verify|ecdsakeygen> [iters]
use std::hint::black_box;
use std::time::Instant;

const PUB: &[u8; 65] = b"\x04\
\x62\xd5\xbd\x33\x72\xaf\x75\xfe\x85\xa0\x40\x71\x5d\x0f\x50\x24\x28\xe0\x70\x46\x86\x8b\x0b\xfd\xfa\x61\xd7\x31\xaf\xe4\x4f\x26\
\xac\x33\x3a\x93\xa9\xe7\x0a\x81\xcd\x5a\x95\xb5\xbf\x8d\x13\x99\x0e\xb7\x41\xc8\xc3\x88\x72\xb4\xa0\x7d\x27\x5a\x01\x4e\x30\xcf";
const VPUB: &[u8; 65] = b"\x04\
\x29\x27\xb1\x05\x12\xba\xe3\xed\xdc\xfe\x46\x78\x28\x12\x8b\xad\x29\x03\x26\x99\x19\xf7\x08\x60\x69\xc8\xc4\xdf\x6c\x73\x28\x38\
\xc7\x78\x79\x64\xea\xac\x00\xe5\x92\x1f\xb1\x49\x8a\x60\xf4\x60\x67\x66\xb3\xd9\x68\x50\x01\x55\x8d\x1a\x97\x4e\x73\x41\x51\x3e";
const MSG: &[u8] = b"\x31\x32\x33\x34\x30\x30";
const SIG: &[u8; 64] = b"\x2b\xa3\xa8\xbe\x6b\x94\xd5\xec\x80\xa6\xd9\xd1\x19\x0a\x43\x6e\xff\xe5\x0d\x85\xa1\xee\xe8\x59\xb8\xcc\x6a\xf9\xbd\x5c\x2e\x18\x4c\xd6\x0b\x85\x5d\x44\x2f\x5b\x3c\x7b\x11\xeb\x6c\x4e\x0a\xe7\x52\x5f\xe7\x10\xfa\xb9\xaa\x7c\x77\xa6\x7f\x79\xe6\xfa\xdd\x76";

fn run(lib: &str, op: &str) -> Box<dyn FnMut()> {
    match (lib, op) {
        ("rind" | "rind2", "keygen") => Box::new(|| {
            use rind::agreement::*;
            let k = PrivateKey::generate(&ECDH_P256).unwrap();
            black_box(k.public_key());
        }),
        ("rind" | "rind2", "ecdh") => Box::new(|| {
            use rind::agreement::*;
            let k = PrivateKey::generate(&ECDH_P256).unwrap();
            black_box(k.public_key());
            black_box(k.agree(PUB).unwrap());
        }),
        ("rind" | "rind2", "sign") => {
            use rind::ecdsa::{KeyPair, sign};
            let k = KeyPair::generate(&sign::P256_SHA256_FIXED).unwrap();
            Box::new(move || {
                black_box(k.sign(MSG).unwrap());
            })
        }
        ("rind" | "rind2", "verify") => Box::new(|| {
            use rind::ecdsa::{PublicKey, verify};
            PublicKey::new(&verify::P256_SHA256_FIXED, VPUB).unwrap().verify(MSG, SIG).unwrap();
        }),
        ("rind" | "rind2", "ecdsakeygen") => Box::new(|| {
            use rind::ecdsa::{KeyPair, sign};
            let k = KeyPair::generate(&sign::P256_SHA256_FIXED).unwrap();
            black_box(k.public_key().as_ref());
        }),
        ("awslc", "keygen") => Box::new(|| {
            use aws_lc_rs::{agreement, rand};
            let rng = rand::SystemRandom::new();
            let k = agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, &rng).unwrap();
            black_box(k.compute_public_key().unwrap());
        }),
        ("awslc", "ecdh") => Box::new(|| {
            use aws_lc_rs::{agreement, error, rand};
            let rng = rand::SystemRandom::new();
            let k = agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, &rng).unwrap();
            black_box(k.compute_public_key().unwrap());
            let p = agreement::UnparsedPublicKey::new(&agreement::ECDH_P256, PUB);
            agreement::agree_ephemeral(k, p, error::Unspecified, |m| {
                black_box(m);
                Ok(())
            })
            .unwrap();
        }),
        ("awslc", "sign") => {
            use aws_lc_rs::{rand, signature as s};
            let rng = rand::SystemRandom::new();
            let p8 = s::EcdsaKeyPair::generate_pkcs8(&s::ECDSA_P256_SHA256_FIXED_SIGNING, &rng).unwrap();
            let k = s::EcdsaKeyPair::from_pkcs8(&s::ECDSA_P256_SHA256_FIXED_SIGNING, p8.as_ref()).unwrap();
            Box::new(move || {
                black_box(k.sign(&rng, MSG).unwrap());
            })
        }
        ("awslc", "verify") => Box::new(|| {
            use aws_lc_rs::signature as s;
            s::UnparsedPublicKey::new(&s::ECDSA_P256_SHA256_FIXED, VPUB).verify(MSG, SIG).unwrap();
        }),
        ("awslc", "ecdsakeygen") => Box::new(|| {
            use aws_lc_rs::signature::{ECDSA_P256_SHA256_FIXED_SIGNING, EcdsaKeyPair, KeyPair};
            let k = EcdsaKeyPair::generate(&ECDSA_P256_SHA256_FIXED_SIGNING).unwrap();
            black_box(k.public_key().as_ref());
        }),
        ("ring", "keygen") => Box::new(|| {
            use ring::{agreement, rand};
            let rng = rand::SystemRandom::new();
            let k = agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, &rng).unwrap();
            black_box(k.compute_public_key().unwrap());
        }),
        ("ring", "ecdh") => Box::new(|| {
            use ring::{agreement, rand};
            let rng = rand::SystemRandom::new();
            let k = agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, &rng).unwrap();
            black_box(k.compute_public_key().unwrap());
            let p = agreement::UnparsedPublicKey::new(&agreement::ECDH_P256, PUB);
            agreement::agree_ephemeral(k, &p, |m| {
                black_box(m);
            })
            .unwrap();
        }),
        ("ring", "sign") => {
            use ring::{rand, signature as s};
            let rng = rand::SystemRandom::new();
            let p8 = s::EcdsaKeyPair::generate_pkcs8(&s::ECDSA_P256_SHA256_FIXED_SIGNING, &rng).unwrap();
            let k = s::EcdsaKeyPair::from_pkcs8(&s::ECDSA_P256_SHA256_FIXED_SIGNING, p8.as_ref(), &rng).unwrap();
            Box::new(move || {
                black_box(k.sign(&rng, MSG).unwrap());
            })
        }
        ("ring", "verify") => Box::new(|| {
            use ring::signature as s;
            s::UnparsedPublicKey::new(&s::ECDSA_P256_SHA256_FIXED, VPUB).verify(MSG, SIG).unwrap();
        }),
        ("ring", "ecdsakeygen") => Box::new(|| {
            use ring::{rand, signature as s};
            let rng = rand::SystemRandom::new();
            black_box(s::EcdsaKeyPair::generate_pkcs8(&s::ECDSA_P256_SHA256_FIXED_SIGNING, &rng).unwrap());
        }),
        ("openssl", op) => {
            use openssl::bn::{BigNum, BigNumContext};
            use openssl::derive::Deriver;
            use openssl::ec::{EcGroup, EcKey, EcPoint, PointConversionForm};
            use openssl::ecdsa::EcdsaSig;
            use openssl::hash::MessageDigest;
            use openssl::nid::Nid;
            use openssl::pkey::PKey;
            use openssl::sign::{Signer, Verifier};
            let group = EcGroup::from_curve_name(Nid::X9_62_PRIME256V1).unwrap();
            let mut ctx = BigNumContext::new().unwrap();
            let skey = PKey::from_ec_key(EcKey::generate(&group).unwrap()).unwrap();
            let der = EcdsaSig::from_private_components(
                BigNum::from_slice(&SIG[..32]).unwrap(),
                BigNum::from_slice(&SIG[32..]).unwrap(),
            )
            .unwrap()
            .to_der()
            .unwrap();
            let pubkey = |ctx: &mut BigNumContext, group: &EcGroup, b: &[u8]| {
                let pt = EcPoint::from_bytes(group, b, ctx).unwrap();
                PKey::from_ec_key(EcKey::from_public_key(group, &pt).unwrap()).unwrap()
            };
            match op {
                "keygen" | "ecdsakeygen" => Box::new(move || {
                    let k = PKey::from_ec_key(EcKey::generate(&group).unwrap()).unwrap();
                    black_box(k.ec_key().unwrap().public_key().to_bytes(&group, PointConversionForm::UNCOMPRESSED, &mut ctx).unwrap());
                }),
                "ecdh" => Box::new(move || {
                    let k = PKey::from_ec_key(EcKey::generate(&group).unwrap()).unwrap();
                    black_box(k.ec_key().unwrap().public_key().to_bytes(&group, PointConversionForm::UNCOMPRESSED, &mut ctx).unwrap());
                    let peer = pubkey(&mut ctx, &group, PUB);
                    let mut d = Deriver::new(&k).unwrap();
                    d.set_peer(&peer).unwrap();
                    black_box(d.derive_to_vec().unwrap());
                }),
                "sign" => Box::new(move || {
                    let mut s = Signer::new(MessageDigest::sha256(), &skey).unwrap();
                    black_box(s.sign_oneshot_to_vec(MSG).unwrap());
                }),
                "verify" => Box::new(move || {
                    let k = pubkey(&mut ctx, &group, VPUB);
                    let mut v = Verifier::new(MessageDigest::sha256(), &k).unwrap();
                    assert!(v.verify_oneshot(&der, MSG).unwrap());
                }),
                _ => panic!(),
            }
        }
        _ => panic!("bad lib/op"),
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let iters: usize = a.get(3).map(|s| s.parse().unwrap()).unwrap_or(0);
    let mut f = run(&a[1], &a[2]);
    // Warm up, then size the batch so that it lasts about 50 ms.
    for _ in 0..5 { f(); }
    let t = Instant::now();
    let mut n = 0;
    while t.elapsed().as_millis() < 100 { f(); n += 1; }
    let per = t.elapsed().as_nanos() as f64 / n as f64;
    let batch = if iters > 0 { iters } else { ((50e6 / per) as usize).max(1) };
    let mut v = vec![];
    for _ in 0..40 {
        let t = Instant::now();
        for _ in 0..batch { f(); }
        v.push(t.elapsed().as_nanos() as f64 / batch as f64);
    }
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("{} {} median_ns {:.0} min_ns {:.0} p90_ns {:.0}", a[1], a[2], v[20], v[0], v[36]);
}
