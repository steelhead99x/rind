// @generated list of rind-bench's bench files, compiled unchanged as modules.
#![allow(dead_code, unused_imports, unused_macros, clippy::all)]

#[path = "../../rind-bench/benches/aes_gcm.rs"]
pub mod aes_gcm;
#[path = "../../rind-bench/benches/argon2.rs"]
pub mod argon2;
#[path = "../../rind-bench/benches/blind_rsa.rs"]
pub mod blind_rsa;
#[path = "../../rind-bench/benches/chacha20poly1305.rs"]
pub mod chacha20poly1305;
#[path = "../../rind-bench/benches/cipher.rs"]
pub mod cipher;
#[path = "../../rind-bench/benches/ed25519.rs"]
pub mod ed25519;
#[path = "../../rind-bench/benches/hkdf.rs"]
pub mod hkdf;
#[path = "../../rind-bench/benches/hmac.rs"]
pub mod hmac;
#[path = "../../rind-bench/benches/dit_toggle.rs"]
pub mod dit_toggle;
#[path = "../../rind-bench/benches/hpke.rs"]
pub mod hpke;
#[path = "../../rind-bench/benches/jsonwebtoken.rs"]
pub mod jsonwebtoken;
#[path = "../../rind-bench/benches/key_wrap.rs"]
pub mod key_wrap;
#[path = "../../rind-bench/benches/md5.rs"]
pub mod md5;
#[path = "../../rind-bench/benches/mldsa.rs"]
pub mod mldsa;
#[path = "../../rind-bench/benches/mlkem.rs"]
pub mod mlkem;
#[path = "../../rind-bench/benches/oprf.rs"]
pub mod oprf;
#[path = "../../rind-bench/benches/p256.rs"]
pub mod p256;
#[path = "../../rind-bench/benches/p384.rs"]
pub mod p384;
#[path = "../../rind-bench/benches/p521.rs"]
pub mod p521;
#[path = "../../rind-bench/benches/pbkdf2.rs"]
pub mod pbkdf2;
#[path = "../../rind-bench/benches/rsa_gen.rs"]
pub mod rsa_gen;
#[path = "../../rind-bench/benches/rsa_priv.rs"]
pub mod rsa_priv;
#[path = "../../rind-bench/benches/rsa_pub.rs"]
pub mod rsa_pub;
#[path = "../../rind-bench/benches/rustls.rs"]
pub mod rustls;
#[path = "../../rind-bench/benches/sha1.rs"]
pub mod sha1;
#[path = "../../rind-bench/benches/sha2.rs"]
pub mod sha2;
#[path = "../../rind-bench/benches/sha3.rs"]
pub mod sha3;
#[path = "../../rind-bench/benches/slhdsa.rs"]
pub mod slhdsa;
#[path = "../../rind-bench/benches/spake2plus.rs"]
pub mod spake2plus;
#[path = "../../rind-bench/benches/vrf.rs"]
pub mod vrf;
#[path = "../../rind-bench/benches/x25519.rs"]
pub mod x25519;
#[path = "../../rind-bench/benches/xchacha20poly1305.rs"]
pub mod xchacha20poly1305;

/// (bench file, its criterion_main).
pub const FILES: &[(&str, fn())] = &[
    ("aes_gcm", aes_gcm::main),
    ("argon2", argon2::main),
    ("blind_rsa", blind_rsa::main),
    ("chacha20poly1305", chacha20poly1305::main),
    ("cipher", cipher::main),
    ("dit_toggle", dit_toggle::main),
    ("ed25519", ed25519::main),
    ("hkdf", hkdf::main),
    ("hmac", hmac::main),
    ("hpke", hpke::main),
    ("jsonwebtoken", jsonwebtoken::main),
    ("key_wrap", key_wrap::main),
    ("md5", md5::main),
    ("mldsa", mldsa::main),
    ("mlkem", mlkem::main),
    ("oprf", oprf::main),
    ("p256", p256::main),
    ("p384", p384::main),
    ("p521", p521::main),
    ("pbkdf2", pbkdf2::main),
    ("rsa_gen", rsa_gen::main),
    ("rsa_priv", rsa_priv::main),
    ("rsa_pub", rsa_pub::main),
    ("rustls", rustls::main),
    ("sha1", sha1::main),
    ("sha2", sha2::main),
    ("sha3", sha3::main),
    ("slhdsa", slhdsa::main),
    ("spake2plus", spake2plus::main),
    ("vrf", vrf::main),
    ("x25519", x25519::main),
    ("xchacha20poly1305", xchacha20poly1305::main),
];
