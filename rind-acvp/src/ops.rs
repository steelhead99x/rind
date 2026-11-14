// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use std::num::NonZeroU32;

use rind::aead::gcm::{self, TagLength};
use rind::agreement::{ECDH_P256, ECDH_P384, ECDH_P521, PrivateKey};
use rind::cipher::{
    AES_128, AES_192, AES_256, Aes, AesCbcDecryptingKey, AesCbcEncryptingKey, AesCtr, CbcIv,
};
use rind::digest::{self, Algorithm as Hash, Context};
use rind::hmac::{self, Key as HmacKey};
use rind::key_wrap::AesKek;
use rind::pbkdf2::{self, Secret};
use rind::rsa::KeySize;
use rind::signature::sign::{self, MlDsa44, MlDsa65, MlDsa87, MlDsaKeyPair};
use rind::signature::verify;
use rind::signature::{EcdsaKeyPair, Ed25519KeyPair, PublicKey, RsaKeyPair, VerificationAlgorithm};

use crate::protocol::u32_arg;

/// One reply to `acvptool`.
///
/// A secret span is a [`rind::acvp::SecretBuf`], wiped on drop under rind's
/// `wipe` feature. Public spans, such as a hash or a ciphertext, are left
/// alone.
pub struct Reply {
    parts: Vec<Part>,
}

enum Part {
    Public(Vec<u8>),
    Secret(Box<rind::acvp::SecretBuf>),
}

impl Reply {
    fn public_parts(parts: Vec<Vec<u8>>) -> Self {
        Self {
            parts: parts.into_iter().map(Part::Public).collect(),
        }
    }

    /// Borrows each span, secret or not, in order.
    pub fn slices(&self) -> Vec<&[u8]> {
        self.parts
            .iter()
            .map(|part| match part {
                Part::Public(bytes) => bytes.as_slice(),
                Part::Secret(bytes) => bytes.as_slice(),
            })
            .collect()
    }

    /// Whether span `index` is a [`rind::acvp::SecretBuf`] rather than a plain
    /// buffer. A private scalar and a shared secret are.
    pub fn is_secret(&self, index: usize) -> bool {
        matches!(self.parts.get(index), Some(Part::Secret(_)))
    }

    /// Moves the wiping buffer at `index` out. The span stays, empty, so
    /// `Drop` still runs.
    pub fn take_secret(&mut self, index: usize) -> Option<rind::acvp::SecretBuf> {
        match self.parts.get_mut(index) {
            Some(Part::Secret(buf)) => {
                let empty = Box::new(rind::acvp::SecretBuf::from_slice(&[]));
                Some(*std::mem::replace(buf, empty))
            }
            _ => None,
        }
    }
}

impl std::ops::Index<usize> for Reply {
    type Output = [u8];

    fn index(&self, index: usize) -> &Self::Output {
        match &self.parts[index] {
            Part::Public(bytes) => bytes.as_slice(),
            Part::Secret(bytes) => bytes.as_slice(),
        }
    }
}

fn public_reply(parts: Vec<Vec<u8>>) -> Result<Reply, String> {
    Ok(Reply::public_parts(parts))
}

fn with_secret(head: Vec<Vec<u8>>, secret: rind::acvp::SecretBuf) -> Reply {
    let mut parts = Vec::with_capacity(head.len() + 1);
    parts.extend(head.into_iter().map(Part::Public));
    parts.push(Part::Secret(Box::new(secret)));
    Reply { parts }
}

pub fn handle(command: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    if command == "getConfig" {
        return public_reply(vec![CONFIG.as_bytes().to_vec()]);
    }
    if let Some(hash) = hash_alg(command) {
        return hash_oneshot(hash, args);
    }
    if let Some(name) = command.strip_suffix("/MCT") {
        return hash_mct(name, args);
    }
    if let Some(name) = command.strip_suffix("/LDT") {
        return hash_ldt(name, args);
    }
    if let Some(hash) = hmac_alg(command) {
        return hmac(hash, args);
    }
    match command {
        "AES/encrypt" => aes_ecb(true, args),
        "AES/decrypt" => Err("AES-ECB decryption is outside the module".into()),
        "AES-CBC/encrypt" => aes_cbc(true, args),
        "AES-CBC/decrypt" => aes_cbc(false, args),
        "AES-CTR/encrypt" | "AES-CTR/decrypt" => aes_ctr(args),
        "AES-GCM/seal" => gcm_seal(args),
        "AES-GCM/open" => gcm_open(args),
        "AES-KW/seal" => kw_seal(false, args),
        "AES-KW/open" => kw_open(false, args),
        "AES-KWP/seal" => kw_seal(true, args),
        "AES-KWP/open" => kw_open(true, args),
        "PBKDF" => pbkdf(args),
        "ECDSA/keyGen" => ecdsa_keygen(args),
        "ECDSA/keyVer" => ecdsa_keyver(args),
        "ECDSA/sigGen" => ecdsa_siggen(args, false),
        "ECDSA/sigGen/componentTest" => ecdsa_siggen(args, true),
        "ECDSA/sigVer" => ecdsa_sigver(args),
        "EDDSA/ED-25519/keyGen" => ed25519_keygen(),
        "EDDSA/ED-25519/keyVer" => ed25519_keyver(args),
        "EDDSA/ED-25519/sigGen" => ed25519_siggen(args),
        "EDDSA/ED-25519/sigVer" => ed25519_sigver(args),
        "ML-KEM/ML-KEM-768/keyGen" => mlkem_keygen(args),
        "ML-KEM/ML-KEM-768/encap" => mlkem_encap(args),
        "ML-KEM/ML-KEM-768/decap" => mlkem_decap(args),
        "ML-KEM/ML-KEM-768/encapKeyCheck" => mlkem_ek_check(args),
        "ML-KEM/ML-KEM-768/decapKeyCheck" => mlkem_dk_check(args),
        "RSA/signaturePrimitive" => rsa_primitive(args),
        "RSA/decryptionPrimitive" => rsa_decrypt(args, false),
        "RSA/decryptionPrimitive/crt" => rsa_decrypt(args, true),
        _ => other(command, args),
    }
}

fn other(command: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    if let Some(rest) = command.strip_prefix("KDA/HKDF/") {
        return hkdf(rest, args);
    }
    if let Some(rest) = command.strip_prefix("HKDF/") {
        return hkdf_half(rest, args);
    }
    if let Some(rest) = command.strip_prefix("ECDH/") {
        return ecdh(rest, args);
    }
    if let Some(rest) = command.strip_prefix("hmacDRBG") {
        return hmac_drbg(rest, args);
    }
    if let Some(rest) = command.strip_prefix("ML-DSA/") {
        return mldsa(rest, args);
    }
    if let Some(rest) = command.strip_prefix("RSA/sigGen/") {
        return rsa_siggen(rest, args);
    }
    if let Some(rest) = command.strip_prefix("RSA/sigVer/") {
        return rsa_sigver(rest, args);
    }
    Err(format!("unsupported ACVP command {command}"))
}

fn arg(args: &[Vec<u8>], n: usize) -> Result<&[u8], String> {
    args.get(n)
        .map(Vec::as_slice)
        .ok_or_else(|| format!("missing argument {n}"))
}

fn hash_alg(name: &str) -> Option<&'static Hash> {
    Some(match name {
        "SHA-1" => &digest::legacy::SHA1,
        "SHA2-256" => &digest::SHA256,
        "SHA2-384" => &digest::SHA384,
        "SHA2-512" => &digest::SHA512,
        "SHA2-512/256" => &digest::SHA512_256,
        "SHA3-256" => &digest::SHA3_256,
        "SHA3-384" => &digest::SHA3_384,
        "SHA3-512" => &digest::SHA3_512,
        _ => return None,
    })
}

fn hash_oneshot(alg: &'static Hash, args: &[Vec<u8>]) -> Result<Reply, String> {
    let msg = arg(args, 0)?;
    public_reply(vec![digest::digest(alg, msg).as_ref().to_vec()])
}

fn hash_mct(name: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    let alg = hash_alg(name).ok_or_else(|| format!("unsupported hash {name}"))?;
    let seed = arg(args, 0)?.to_vec();
    let out = alg.output_len();
    if seed.len() != out {
        return Err(format!(
            "{name}/MCT seed is {} bytes, not {out}",
            seed.len()
        ));
    }
    let sha3 = name.starts_with("SHA3");
    let mut digest = seed;
    if sha3 {
        for _ in 0..1000 {
            digest = digest::digest(alg, &digest).as_ref().to_vec();
        }
    } else {
        let mut last = [digest.clone(), digest.clone(), digest];
        for _ in 0..1000 {
            let mut msg = Vec::with_capacity(out * 3);
            msg.extend_from_slice(&last[0]);
            msg.extend_from_slice(&last[1]);
            msg.extend_from_slice(&last[2]);
            last = [
                last[1].clone(),
                last[2].clone(),
                digest::digest(alg, &msg).as_ref().to_vec(),
            ];
        }
        digest = last[2].clone();
    }
    public_reply(vec![digest])
}

fn hash_ldt(name: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    let alg = hash_alg(name).ok_or_else(|| format!("unsupported hash {name}"))?;
    let content = arg(args, 0)?;
    let times = u64_arg(arg(args, 1)?)?;
    if content.is_empty() || times == 0 {
        return Err("LDT content is empty".into());
    }
    let full = (times as usize)
        .checked_mul(content.len())
        .filter(|full| *full <= 8 << 30)
        .ok_or_else(|| "LDT message is longer than 8 GiB".to_string())?;
    let _ = full;
    let mut ctx = Context::new(alg);
    for _ in 0..times {
        ctx.update(content);
    }
    public_reply(vec![ctx.finish().as_ref().to_vec()])
}

fn u64_arg(bytes: &[u8]) -> Result<u64, String> {
    let bytes: [u8; 8] = bytes
        .try_into()
        .map_err(|_| "expected an 8-byte length".to_string())?;
    Ok(u64::from_ne_bytes(bytes))
}

fn hmac(alg: &'static hmac::Algorithm, args: &[Vec<u8>]) -> Result<Reply, String> {
    // acvptool passes the message, then the key.
    let msg = arg(args, 0)?;
    let key = arg(args, 1)?;
    public_reply(vec![
        hmac::sign(&HmacKey::new(alg, key), msg).as_ref().to_vec(),
    ])
}

fn hmac_alg(name: &str) -> Option<&'static hmac::Algorithm> {
    Some(match name {
        "HMAC-SHA-1" => &hmac::legacy::HMAC_SHA1,
        "HMAC-SHA2-256" => &hmac::HMAC_SHA256,
        "HMAC-SHA2-384" => &hmac::HMAC_SHA384,
        "HMAC-SHA2-512" => &hmac::HMAC_SHA512,
        _ => return None,
    })
}

fn aes_alg(len: usize) -> Result<&'static rind::cipher::Algorithm, String> {
    match len {
        16 => Ok(&AES_128),
        24 => Ok(&AES_192),
        32 => Ok(&AES_256),
        _ => Err(format!("AES key is {len} bytes")),
    }
}

fn aes_ecb(encrypt: bool, args: &[Vec<u8>]) -> Result<Reply, String> {
    if !encrypt {
        return Err("AES-ECB decryption is outside the module".into());
    }
    let key =
        Aes::new(aes_alg(arg(args, 0)?.len())?, arg(args, 0)?).map_err(|err| err.to_string())?;
    let mut result = arg(args, 1)?.to_vec();
    if result.len() % 16 != 0 {
        return Err("AES-ECB input is not a whole number of blocks".into());
    }
    let iterations = u32_arg(arg(args, 2)?).ok_or("AES iteration count")?;
    if iterations == 0 {
        return Err("AES iteration count is zero".into());
    }
    let mut prev = result.clone();
    for j in 0..iterations {
        if j + 1 == iterations {
            prev.clone_from(&result);
        }
        for block in result.as_chunks_mut::<16>().0 {
            key.encrypt_block(block);
        }
    }
    public_reply(vec![result, prev])
}

fn aes_cbc(encrypt: bool, args: &[Vec<u8>]) -> Result<Reply, String> {
    let key_bytes = arg(args, 0)?;
    let mut input = arg(args, 1)?.to_vec();
    let mut iv = arg(args, 2)?.to_vec();
    let iterations = u32_arg(arg(args, 3)?).ok_or("AES-CBC iteration count")?;
    if input.is_empty() || input.len() % 16 != 0 || iv.len() != 16 || iterations == 0 {
        return Err("AES-CBC input".into());
    }
    let alg = aes_alg(key_bytes.len())?;
    let mut result = vec![0u8; input.len()];
    let mut prev_result = result.clone();
    let mut prev_input = Vec::new();
    let original_iv = iv.clone();
    for j in 0..iterations {
        prev_result.clone_from(&result);
        if j > 0 {
            iv = if encrypt {
                result.clone()
            } else {
                prev_input.clone()
            };
        }
        result.clone_from(&input);
        let iv_bytes: [u8; 16] = iv
            .as_slice()
            .try_into()
            .map_err(|_| "AES-CBC IV is not 16 bytes".to_string())?;
        if encrypt {
            AesCbcEncryptingKey::new(alg, key_bytes)
                .map_err(|err| err.to_string())?
                .encrypt_blocks(CbcIv::assume_unpredictable(iv_bytes), &mut result)
                .map_err(|err| err.to_string())?;
        } else {
            AesCbcDecryptingKey::new(alg, key_bytes)
                .map_err(|err| err.to_string())?
                .decrypt_blocks(&iv_bytes, &mut result)
                .map_err(|err| err.to_string())?;
        }
        if !encrypt {
            prev_input.clone_from(&input);
        }
        if j == 0 {
            input.clone_from(&original_iv);
        } else {
            input.clone_from(&prev_result);
        }
    }
    public_reply(vec![result, prev_result])
}

fn aes_ctr(args: &[Vec<u8>]) -> Result<Reply, String> {
    if u32_arg(arg(args, 3)?) != Some(1) {
        return Err("AES-CTR takes one iteration".into());
    }
    let key = arg(args, 0)?;
    let mut out = arg(args, 1)?.to_vec();
    let counter: [u8; 16] = arg(args, 2)?
        .try_into()
        .map_err(|_| "AES-CTR counter is not 16 bytes".to_string())?;
    AesCtr::new(aes_alg(key.len())?, key, 32)
        .map_err(|err| err.to_string())?
        .apply_keystream(&counter, &mut out)
        .map_err(|err| err.to_string())?;
    public_reply(vec![out])
}

fn tag_length(bytes: usize) -> Result<TagLength, String> {
    Ok(match bytes {
        16 => TagLength::Full,
        15 => TagLength::Truncated120,
        14 => TagLength::Truncated112,
        13 => TagLength::Truncated104,
        12 => TagLength::Truncated96,
        8 => TagLength::Truncated64,
        4 => TagLength::Truncated32,
        _ => return Err(format!("AES-GCM tag is {bytes} bytes")),
    })
}

fn gcm_seal(args: &[Vec<u8>]) -> Result<Reply, String> {
    let tag_bytes = u32_arg(arg(args, 0)?).ok_or("AES-GCM tag length")? as usize;
    let key_bytes = arg(args, 1)?;
    let mut text = arg(args, 2)?.to_vec();
    let nonce = arg(args, 3)?;
    let aad = arg(args, 4)?;
    if nonce.is_empty() {
        return Err(
            "AES-GCM with an internal IV waits on quest/m4/fips/gcm-iv.md; this wrapper seals only a given nonce"
                .into(),
        );
    }
    let key = gcm::Key::new(aes_alg(key_bytes.len())?, key_bytes, tag_length(tag_bytes)?)
        .map_err(|err| err.to_string())?;
    let iv = gcm::Iv::assume_unique_for_key(nonce).map_err(|err| err.to_string())?;
    let tag = key
        .seal_in_place_separate_tag(iv, aad, &mut text)
        .map_err(|err| err.to_string())?;
    text.extend_from_slice(tag.as_ref());
    public_reply(vec![text])
}

fn gcm_open(args: &[Vec<u8>]) -> Result<Reply, String> {
    let tag_bytes = u32_arg(arg(args, 0)?).ok_or("AES-GCM tag length")? as usize;
    let key_bytes = arg(args, 1)?;
    let combined = arg(args, 2)?;
    let nonce = arg(args, 3)?;
    let aad = arg(args, 4)?;
    if combined.len() < tag_bytes {
        return public_reply(vec![vec![0], Vec::new()]);
    }
    let (ct, tag) = combined.split_at(combined.len() - tag_bytes);
    let mut text = ct.to_vec();
    let key = gcm::Key::new(aes_alg(key_bytes.len())?, key_bytes, tag_length(tag_bytes)?)
        .map_err(|err| err.to_string())?;
    let iv = gcm::Iv::assume_unique_for_key(nonce).map_err(|err| err.to_string())?;
    match key.open_in_place_separate_tag(iv, aad, tag, &mut text) {
        Ok(pt) => public_reply(vec![vec![1], pt.to_vec()]),
        Err(_) => public_reply(vec![vec![0], Vec::new()]),
    }
}

fn kw_seal(padded: bool, args: &[Vec<u8>]) -> Result<Reply, String> {
    // acvptool passes dummy, key, plaintext, dummy, dummy.
    let key = arg(args, 1)?;
    let plain = arg(args, 2)?;
    let kek = AesKek::new(aes_alg(key.len())?, key).map_err(|err| err.to_string())?;
    let len = if padded {
        plain.len().next_multiple_of(8) + 8
    } else {
        plain.len() + 8
    };
    let mut wrapped = vec![0u8; len];
    if padded {
        kek.wrap_padded(plain, &mut wrapped)
    } else {
        kek.wrap(plain, &mut wrapped)
    }
    .map_err(|err| err.to_string())?;
    public_reply(vec![wrapped])
}

fn kw_open(padded: bool, args: &[Vec<u8>]) -> Result<Reply, String> {
    let key = arg(args, 1)?;
    let wrapped = arg(args, 2)?;
    let kek = AesKek::new(aes_alg(key.len())?, key).map_err(|err| err.to_string())?;
    if wrapped.len() < 8 {
        return public_reply(vec![vec![0], Vec::new()]);
    }
    let mut plain = vec![0u8; wrapped.len() - 8];
    let opened = if padded {
        // The unpadded length is not known; try every padding the wrap allows.
        kw_open_padded(&kek, wrapped)
    } else {
        kek.unwrap(wrapped, &mut plain)
            .map(|()| plain)
            .map_err(|_| ())
    };
    match opened {
        Ok(plain) => public_reply(vec![vec![1], plain]),
        Err(()) => public_reply(vec![vec![0], Vec::new()]),
    }
}

fn kw_open_padded(kek: &AesKek, wrapped: &[u8]) -> Result<Vec<u8>, ()> {
    // RFC 5649 recovers the length from the first half of the IV. Ask for
    // the maximum and let unwrap_padded report the used prefix.
    let mut plain = vec![0u8; wrapped.len().saturating_sub(8)];
    kek.unwrap_padded(wrapped, &mut plain)
        .map(|got| got.to_vec())
        .map_err(|_| ())
}

fn pbkdf(args: &[Vec<u8>]) -> Result<Reply, String> {
    let password = arg(args, 0)?;
    let salt = arg(args, 1)?;
    let iterations = u32_arg(arg(args, 2)?).ok_or("PBKDF iterations")?;
    let hash = std::str::from_utf8(arg(args, 3)?).map_err(|_| "PBKDF hash name")?;
    let bits = u32_arg(arg(args, 4)?).ok_or("PBKDF length")?;
    if bits % 8 != 0 {
        return Err("PBKDF length is not a whole number of bytes".into());
    }
    let alg = match hash {
        "SHA-1" => &pbkdf2::legacy::PBKDF2_HMAC_SHA1,
        "SHA2-256" => &pbkdf2::PBKDF2_HMAC_SHA256,
        "SHA2-384" => &pbkdf2::PBKDF2_HMAC_SHA384,
        "SHA2-512" => &pbkdf2::PBKDF2_HMAC_SHA512,
        _ => return Err(format!("unsupported PBKDF hash {hash}")),
    };
    let mut out = vec![0u8; (bits / 8) as usize];
    Secret::new(alg, password)
        .derive(
            NonZeroU32::new(iterations).ok_or("PBKDF iterations are zero")?,
            salt,
            &mut out,
        )
        .map_err(|err| err.to_string())?;
    public_reply(vec![out])
}

fn hkdf(hash: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    let key = arg(args, 0)?;
    let salt = arg(args, 1)?;
    let info = arg(args, 2)?;
    let out_len = u32_arg(arg(args, 3)?).ok_or("HKDF length")? as usize;
    let (alg, _) = hkdf_alg(hash)?;
    let mut out = vec![0u8; out_len];
    // Extract and expand return `Result` so rind-fips can refuse an empty
    // salt or info. rind accepts both, and the errors still propagate.
    rind::hkdf::Salt::new(alg, salt)
        .extract(key)
        .map_err(|err| err.to_string())?
        .expand(&[info], out_len)
        .map_err(|err| err.to_string())?
        .fill(&mut out)
        .map_err(|err| err.to_string())?;
    public_reply(vec![out])
}

fn hkdf_half(rest: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    let (hash, op) = rest
        .rsplit_once('/')
        .ok_or_else(|| format!("unsupported HKDF command {rest}"))?;
    let (_alg, hmac_alg) = hkdf_alg(hash)?;
    match op {
        "extract" => {
            let ikm = arg(args, 0)?;
            let salt = arg(args, 1)?;
            let prk = hmac::sign(&HmacKey::new(hmac_alg, salt), ikm);
            public_reply(vec![prk.as_ref().to_vec()])
        }
        "expand" => {
            let out_len = u32_arg(arg(args, 0)?).ok_or("HKDF length")? as usize;
            let prk = arg(args, 1)?;
            let info = arg(args, 2)?;
            public_reply(vec![hkdf_expand(hmac_alg, prk, info, out_len)?])
        }
        _ => Err(format!("unsupported HKDF operation {op}")),
    }
}

fn hkdf_alg(
    name: &str,
) -> Result<(&'static rind::hkdf::Algorithm, &'static hmac::Algorithm), String> {
    Ok(match name {
        "SHA-1" => (&rind::hkdf::legacy::HKDF_SHA1, &hmac::legacy::HMAC_SHA1),
        "SHA2-256" => (&rind::hkdf::HKDF_SHA256, &hmac::HMAC_SHA256),
        "SHA2-384" => (&rind::hkdf::HKDF_SHA384, &hmac::HMAC_SHA384),
        "SHA2-512" => (&rind::hkdf::HKDF_SHA512, &hmac::HMAC_SHA512),
        _ => return Err(format!("unsupported HKDF hash {name}")),
    })
}

/// HKDF-Expand, so a PRK that was not extracted here can still expand.
fn hkdf_expand(
    hmac_alg: &'static hmac::Algorithm,
    prk: &[u8],
    info: &[u8],
    out_len: usize,
) -> Result<Vec<u8>, String> {
    let hash_len = hmac::sign(&HmacKey::new(hmac_alg, prk), &[]).as_ref().len();
    if out_len > 255 * hash_len {
        return Err("HKDF output is too long".into());
    }
    let key = HmacKey::new(hmac_alg, prk);
    let mut out = Vec::with_capacity(out_len);
    let mut prev = Vec::new();
    let mut counter = 1u8;
    while out.len() < out_len {
        let mut msg = Vec::with_capacity(prev.len() + info.len() + 1);
        msg.extend_from_slice(&prev);
        msg.extend_from_slice(info);
        msg.push(counter);
        prev = hmac::sign(&key, &msg).as_ref().to_vec();
        out.extend_from_slice(&prev);
        counter = counter.checked_add(1).ok_or("HKDF counter")?;
    }
    out.truncate(out_len);
    Ok(out)
}

fn ecdh(curve: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    let (alg, field) = match curve {
        "P-256" => (&ECDH_P256, 32),
        "P-384" => (&ECDH_P384, 48),
        "P-521" => (&ECDH_P521, 66),
        _ => return Err(format!("unsupported ECDH curve {curve}")),
    };
    let peer_x = pad(arg(args, 0)?, field)?;
    let peer_y = pad(arg(args, 1)?, field)?;
    let private = arg(args, 2)?;
    let mut peer = Vec::with_capacity(1 + field * 2);
    peer.push(0x04);
    peer.extend_from_slice(&peer_x);
    peer.extend_from_slice(&peer_y);
    let key = if private.is_empty() {
        PrivateKey::generate(alg).map_err(|err| err.to_string())?
    } else {
        let scalar = pad(private, field)?;
        PrivateKey::from_scalar(alg, &scalar).map_err(|err| err.to_string())?
    };
    let point = key.public_key().as_ref();
    if point.len() != 1 + field * 2 || point[0] != 0x04 {
        return Err("ECDH public key".into());
    }
    let agreed = key.agree(&peer).map_err(|err| err.to_string())?;
    let shared = rind::acvp::SecretBuf::from_slice(agreed.as_ref());
    Ok(with_secret(
        vec![point[1..1 + field].to_vec(), point[1 + field..].to_vec()],
        shared,
    ))
}

fn pad(mut bytes: &[u8], len: usize) -> Result<Vec<u8>, String> {
    // ACVP writes a coordinate with a leading zero when its top bit is set.
    while bytes.len() > len && bytes[0] == 0 {
        bytes = &bytes[1..];
    }
    if bytes.len() > len {
        return Err(format!("value is {} bytes, above {len}", bytes.len()));
    }
    let mut out = vec![0u8; len - bytes.len()];
    out.extend_from_slice(bytes);
    Ok(out)
}

fn ecdsa_keygen(args: &[Vec<u8>]) -> Result<Reply, String> {
    let curve = std::str::from_utf8(arg(args, 0)?).map_err(|_| "ECDSA curve")?;
    let alg = ecdsa_signer(curve)?;
    let key = EcdsaKeyPair::generate(alg).map_err(|err| err.to_string())?;
    let (x, y) = split_point(key.public_key().as_ref())?;
    let scalar = rind::acvp::SecretBuf::from_slice(key.to_scalar().as_ref());
    Ok(Reply {
        parts: vec![
            Part::Secret(Box::new(scalar)),
            Part::Public(x),
            Part::Public(y),
        ],
    })
}

fn ecdsa_keyver(args: &[Vec<u8>]) -> Result<Reply, String> {
    let curve = std::str::from_utf8(arg(args, 0)?).map_err(|_| "ECDSA curve")?;
    let Ok(point) = uncompressed(curve, arg(args, 1)?, arg(args, 2)?) else {
        return public_reply(vec![vec![0]]);
    };
    let alg = ecdsa_verifier(curve, "SHA2-256")?;
    let ok = PublicKey::new(alg, &point).is_ok();
    public_reply(vec![vec![u8::from(ok)]])
}

fn ecdsa_siggen(args: &[Vec<u8>], component: bool) -> Result<Reply, String> {
    if component {
        return Err("ECDSA component sigGen is not in the module's capability".into());
    }
    let curve = std::str::from_utf8(arg(args, 0)?).map_err(|_| "ECDSA curve")?;
    let scalar = arg(args, 1)?;
    let hash = std::str::from_utf8(arg(args, 2)?).map_err(|_| "ECDSA hash")?;
    let message = arg(args, 3)?;
    ecdsa_sign(curve, scalar, hash, message)
}

fn x_from_scalar(curve: &str, scalar: &[u8]) -> Result<Vec<u8>, String> {
    let (alg, field) = match curve {
        "P-256" => (&ECDH_P256, 32),
        "P-384" => (&ECDH_P384, 48),
        "P-521" => (&ECDH_P521, 66),
        _ => return Err(format!("unsupported curve {curve}")),
    };
    let key = PrivateKey::from_scalar(alg, &pad(scalar, field)?).map_err(|err| err.to_string())?;
    Ok(key.public_key().as_ref().to_vec())
}

fn ecdsa_sign(curve: &str, scalar: &[u8], hash: &str, message: &[u8]) -> Result<Reply, String> {
    let point = x_from_scalar(curve, scalar)?;
    let alg = ecdsa_signer(curve)?;
    let key = EcdsaKeyPair::from_scalar_and_public_key(alg, scalar, &point)
        .map_err(|err| err.to_string())?;
    let hashed = digest::digest(hash_of(hash)?, message);
    let sig = key.sign_digest(&hashed).map_err(|err| err.to_string())?;
    let sig = sig.as_ref();
    if sig.len() % 2 != 0 {
        return Err("ECDSA signature".into());
    }
    let (r, s) = sig.split_at(sig.len() / 2);
    public_reply(vec![r.to_vec(), s.to_vec()])
}

fn ecdsa_sigver(args: &[Vec<u8>]) -> Result<Reply, String> {
    let curve = std::str::from_utf8(arg(args, 0)?).map_err(|_| "ECDSA curve")?;
    let hash = std::str::from_utf8(arg(args, 1)?).map_err(|_| "ECDSA hash")?;
    let message = arg(args, 2)?;
    let point = uncompressed(curve, arg(args, 3)?, arg(args, 4)?)?;
    let r = arg(args, 5)?;
    let s = arg(args, 6)?;
    let alg = ecdsa_verifier(curve, hash)?;
    let der = ecdsa_der(r, s);
    let ok = PublicKey::new(alg, &point)
        .and_then(|key| key.verify(message, &der))
        .is_ok();
    public_reply(vec![vec![u8::from(ok)]])
}

fn ecdsa_signer(curve: &str) -> Result<&'static rind::signature::EcdsaSigningAlgorithm, String> {
    Ok(match curve {
        "P-256" => &sign::ECDSA_P256_SHA256_FIXED,
        "P-384" => &sign::ECDSA_P384_SHA384_FIXED,
        "P-521" => &sign::ECDSA_P521_SHA512_FIXED,
        _ => return Err(format!("unsupported ECDSA curve {curve}")),
    })
}

fn ecdsa_verifier(curve: &str, hash: &str) -> Result<&'static VerificationAlgorithm, String> {
    Ok(match (curve, hash) {
        ("P-256", "SHA2-256") => &verify::ECDSA_P256_SHA256_ASN1,
        ("P-256", "SHA2-384") => &verify::ECDSA_P256_SHA384_ASN1,
        ("P-256", "SHA2-512") => &verify::ECDSA_P256_SHA512_ASN1,
        ("P-384", "SHA2-256") => &verify::ECDSA_P384_SHA256_ASN1,
        ("P-384", "SHA2-384") => &verify::ECDSA_P384_SHA384_ASN1,
        ("P-384", "SHA2-512") => &verify::ECDSA_P384_SHA512_ASN1,
        ("P-521", "SHA2-256") => &verify::ECDSA_P521_SHA256_ASN1,
        ("P-521", "SHA2-384") => &verify::ECDSA_P521_SHA384_ASN1,
        ("P-521", "SHA2-512") => &verify::ECDSA_P521_SHA512_ASN1,
        _ => return Err(format!("unsupported ECDSA {curve} {hash}")),
    })
}

fn hash_of(name: &str) -> Result<&'static Hash, String> {
    hash_alg(name).ok_or_else(|| format!("unsupported hash {name}"))
}

fn field_len(curve: &str) -> Result<usize, String> {
    Ok(match curve {
        "P-256" => 32,
        "P-384" => 48,
        "P-521" => 66,
        _ => return Err(format!("unsupported curve {curve}")),
    })
}

fn uncompressed(curve: &str, x: &[u8], y: &[u8]) -> Result<Vec<u8>, String> {
    let field = field_len(curve)?;
    let mut point = Vec::with_capacity(1 + field * 2);
    point.push(0x04);
    point.extend(pad(x, field)?);
    point.extend(pad(y, field)?);
    Ok(point)
}

fn split_point(point: &[u8]) -> Result<(Vec<u8>, Vec<u8>), String> {
    if point.first() != Some(&0x04) || point.len() % 2 != 1 {
        return Err("ECDSA point".into());
    }
    let field = point.len() / 2;
    Ok((point[1..1 + field].to_vec(), point[1 + field..].to_vec()))
}

fn ecdsa_der(r: &[u8], s: &[u8]) -> Vec<u8> {
    let r = der_int(r);
    let s = der_int(s);
    let mut body = r;
    body.extend(s);
    der_tl(0x30, &body)
}

fn der_int(bytes: &[u8]) -> Vec<u8> {
    let mut body = bytes.to_vec();
    while body.len() > 1 && body[0] == 0 && body[1] & 0x80 == 0 {
        body.remove(0);
    }
    if body.first().is_some_and(|b| b & 0x80 != 0) {
        body.insert(0, 0);
    }
    der_tl(0x02, &body)
}

fn der_tl(tag: u8, body: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(4 + body.len());
    out.push(tag);
    if body.len() < 128 {
        out.push(body.len() as u8);
    } else if body.len() < 256 {
        out.push(0x81);
        out.push(body.len() as u8);
    } else {
        out.push(0x82);
        out.push((body.len() >> 8) as u8);
        out.push(body.len() as u8);
    }
    out.extend_from_slice(body);
    out
}

fn ed25519_keygen() -> Result<Reply, String> {
    let key = Ed25519KeyPair::generate().map_err(|err| err.to_string())?;
    let seed = rind::acvp::SecretBuf::from_slice(key.to_seed().as_ref());
    Ok(Reply {
        parts: vec![
            Part::Secret(Box::new(seed)),
            Part::Public(key.public_key().as_ref().to_vec()),
        ],
    })
}

fn ed25519_keyver(args: &[Vec<u8>]) -> Result<Reply, String> {
    let ok = PublicKey::new(&verify::ED25519, arg(args, 0)?).is_ok();
    public_reply(vec![vec![u8::from(ok)]])
}

fn ed25519_siggen(args: &[Vec<u8>]) -> Result<Reply, String> {
    let key = Ed25519KeyPair::from_seed(arg(args, 0)?).map_err(|err| err.to_string())?;
    let sig = key.sign(arg(args, 1)?);
    public_reply(vec![sig.as_ref().to_vec()])
}

fn ed25519_sigver(args: &[Vec<u8>]) -> Result<Reply, String> {
    // message, public key, signature. acvptool's order is checked against
    // the call site: command, message, Q, signature when prehash is off.
    let message = arg(args, 0)?;
    let public = arg(args, 1)?;
    let signature = arg(args, 2)?;
    let ok = PublicKey::new(&verify::ED25519, public)
        .and_then(|key| key.verify(message, signature))
        .is_ok();
    public_reply(vec![vec![u8::from(ok)]])
}

fn mlkem_keygen(args: &[Vec<u8>]) -> Result<Reply, String> {
    let d = arg(args, 0)?;
    let z = arg(args, 1)?;
    let mut seed = Vec::with_capacity(64);
    seed.extend_from_slice(d);
    seed.extend_from_slice(z);
    let (ek, dk) = rind::acvp::mlkem768_keygen(&seed).map_err(|err| err.to_string())?;
    Ok(with_secret(vec![ek], dk))
}

fn mlkem_encap(args: &[Vec<u8>]) -> Result<Reply, String> {
    let (ciphertext, secret) =
        rind::acvp::mlkem768_encaps(arg(args, 0)?, arg(args, 1)?).map_err(|err| err.to_string())?;
    Ok(with_secret(vec![ciphertext], secret))
}

fn mlkem_decap(args: &[Vec<u8>]) -> Result<Reply, String> {
    let secret =
        rind::acvp::mlkem768_decaps(arg(args, 0)?, arg(args, 1)?).map_err(|err| err.to_string())?;
    Ok(with_secret(Vec::new(), secret))
}

fn mlkem_ek_check(args: &[Vec<u8>]) -> Result<Reply, String> {
    public_reply(vec![vec![u8::from(rind::acvp::mlkem768_ek_ok(arg(
        args, 0,
    )?))]])
}

fn mlkem_dk_check(args: &[Vec<u8>]) -> Result<Reply, String> {
    public_reply(vec![vec![u8::from(rind::acvp::mlkem768_dk_ok(arg(
        args, 0,
    )?))]])
}

fn mldsa(rest: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    let (set, op) = rest
        .split_once('/')
        .ok_or_else(|| format!("unsupported ML-DSA command {rest}"))?;
    match op {
        "keyGen" => mldsa_keygen(set, arg(args, 0)?),
        "sigGen" => mldsa_siggen(set, args),
        "sigVer" => mldsa_sigver(set, args),
        _ => Err(format!("unsupported ML-DSA operation {op}")),
    }
}

fn mldsa_keygen(set: &str, seed: &[u8]) -> Result<Reply, String> {
    let (pk, sk) = match set {
        "ML-DSA-44" => pair44(seed)?,
        "ML-DSA-65" => pair65(seed)?,
        "ML-DSA-87" => pair87(seed)?,
        _ => return Err(format!("unsupported ML-DSA set {set}")),
    };
    Ok(with_secret(vec![pk], sk))
}

fn pair44(seed: &[u8]) -> Result<(Vec<u8>, rind::acvp::SecretBuf), String> {
    let key = MlDsaKeyPair::<MlDsa44>::from_seed(seed).map_err(|err| err.to_string())?;
    Ok((key.public_key().as_ref().to_vec(), key.expanded_secret()))
}

fn pair65(seed: &[u8]) -> Result<(Vec<u8>, rind::acvp::SecretBuf), String> {
    let key = MlDsaKeyPair::<MlDsa65>::from_seed(seed).map_err(|err| err.to_string())?;
    Ok((key.public_key().as_ref().to_vec(), key.expanded_secret()))
}

fn pair87(seed: &[u8]) -> Result<(Vec<u8>, rind::acvp::SecretBuf), String> {
    let key = MlDsaKeyPair::<MlDsa87>::from_seed(seed).map_err(|err| err.to_string())?;
    Ok((key.public_key().as_ref().to_vec(), key.expanded_secret()))
}

fn mldsa_siggen(set: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    // sk, message, mu, rnd, context, externalMu flag, optional interface.
    let sk = arg(args, 0)?;
    let message = arg(args, 1)?;
    let provided = arg(args, 2).unwrap_or(&[]);
    let rnd = arg(args, 3).unwrap_or(&[]);
    let context = arg(args, 4).unwrap_or(&[]);
    let external_mu = args.get(5).map(Vec::as_slice).unwrap_or(&[]);
    let (mu, internal) = mldsa_mu(
        external_mu,
        context,
        args.get(6).map(Vec::as_slice),
        provided,
    )?;
    let rnd_zeros;
    let rnd = if rnd.is_empty() {
        rnd_zeros = [0u8; 32];
        rnd_zeros.as_slice()
    } else {
        rnd
    };
    let sig = match set {
        "ML-DSA-44" => sign44(sk, message, mu, internal, rnd, context)?,
        "ML-DSA-65" => sign65(sk, message, mu, internal, rnd, context)?,
        "ML-DSA-87" => sign87(sk, message, mu, internal, rnd, context)?,
        _ => return Err(format!("unsupported ML-DSA set {set}")),
    };
    public_reply(vec![sig])
}

/// How ACVP names the message representative.
///
/// A seventh argument, `b"internal"` or `b"external"`, is the group's
/// `signatureInterface`. `acvptool` does not send it. Without it, a `1` flag
/// is the supplied `mu`, a non-empty context is the external interface, an
/// absent flag is external, and a `0` flag with an empty context is the
/// internal interface, which is what aws-lc's module wrapper does.
fn mldsa_mu<'a>(
    external_mu: &'a [u8],
    context: &[u8],
    interface: Option<&'a [u8]>,
    provided: &'a [u8],
) -> Result<(Option<&'a [u8]>, bool), String> {
    if let Some(interface) = interface {
        return match interface {
            b"internal" if external_mu == [1] => Ok((Some(provided), true)),
            b"internal" => Ok((None, true)),
            b"external" => Ok((None, false)),
            _ => Err("ML-DSA signature interface".into()),
        };
    }
    match external_mu {
        [1] => Ok((Some(provided), true)),
        [] => Ok((None, false)),
        [0] if !context.is_empty() => Ok((None, false)),
        [0] => Ok((None, true)),
        _ => Err("ML-DSA externalMu".into()),
    }
}

fn load_mldsa<P: sign::MlDsaParameterSet>(sk: &[u8]) -> Result<MlDsaKeyPair<P>, String>
where
    MlDsaKeyPair<P>: MldsaOps,
{
    if sk.len() == 32 {
        MlDsaKeyPair::<P>::from_seed(sk).map_err(|err| err.to_string())
    } else {
        MlDsaKeyPair::<P>::from_expanded(sk).map_err(|err| err.to_string())
    }
}

trait MldsaOps {
    fn sign_fixed(
        &self,
        context: &[u8],
        message: &[u8],
        mu: Option<&[u8]>,
        internal: bool,
        rnd: &[u8],
    ) -> Result<Vec<u8>, String>;
}

impl<P: sign::MlDsaParameterSet> MldsaOps for MlDsaKeyPair<P> {
    fn sign_fixed(
        &self,
        context: &[u8],
        message: &[u8],
        mu: Option<&[u8]>,
        internal: bool,
        rnd: &[u8],
    ) -> Result<Vec<u8>, String> {
        Ok(self
            .sign_acvp(context, message, mu, internal, rnd)
            .map_err(|err| err.to_string())?
            .as_ref()
            .to_vec())
    }
}

fn sign44(
    sk: &[u8],
    message: &[u8],
    mu: Option<&[u8]>,
    internal: bool,
    rnd: &[u8],
    context: &[u8],
) -> Result<Vec<u8>, String> {
    load_mldsa::<MlDsa44>(sk)?.sign_fixed(context, message, mu, internal, rnd)
}

fn sign65(
    sk: &[u8],
    message: &[u8],
    mu: Option<&[u8]>,
    internal: bool,
    rnd: &[u8],
    context: &[u8],
) -> Result<Vec<u8>, String> {
    load_mldsa::<MlDsa65>(sk)?.sign_fixed(context, message, mu, internal, rnd)
}

fn sign87(
    sk: &[u8],
    message: &[u8],
    mu: Option<&[u8]>,
    internal: bool,
    rnd: &[u8],
    context: &[u8],
) -> Result<Vec<u8>, String> {
    load_mldsa::<MlDsa87>(sk)?.sign_fixed(context, message, mu, internal, rnd)
}

fn mldsa_sigver(set: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    // signature, pk, message, mu, context, externalMu, optional interface.
    let signature = arg(args, 0)?;
    let pk = arg(args, 1)?;
    let message = arg(args, 2)?;
    let provided = arg(args, 3).unwrap_or(&[]);
    let context = arg(args, 4).unwrap_or(&[]);
    let external_mu = args.get(5).map(Vec::as_slice).unwrap_or(&[]);
    let (mu, internal) = mldsa_mu(
        external_mu,
        context,
        args.get(6).map(Vec::as_slice),
        provided,
    )?;
    let ok = match set {
        "ML-DSA-44" => rind::signature::mldsa_verify_acvp::<MlDsa44>(
            pk, message, context, mu, internal, signature,
        ),
        "ML-DSA-65" => rind::signature::mldsa_verify_acvp::<MlDsa65>(
            pk, message, context, mu, internal, signature,
        ),
        "ML-DSA-87" => rind::signature::mldsa_verify_acvp::<MlDsa87>(
            pk, message, context, mu, internal, signature,
        ),
        _ => return Err(format!("unsupported ML-DSA set {set}")),
    }
    .is_ok();
    public_reply(vec![vec![u8::from(ok)]])
}

fn rsa_siggen(rest: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    let (hash, pad) = rest
        .split_once('/')
        .ok_or_else(|| format!("unsupported RSA sigGen {rest}"))?;
    let bits = u32_arg(arg(args, 0)?).ok_or("RSA modulus bits")?;
    let message = arg(args, 1)?;
    let size = match bits {
        2048 => KeySize::Rsa2048,
        3072 => KeySize::Rsa3072,
        4096 => KeySize::Rsa4096,
        6144 => KeySize::Rsa6144,
        8192 => KeySize::Rsa8192,
        _ => return Err(format!("unsupported RSA modulus {bits}")),
    };
    let alg = rsa_sign_alg(hash, pad)?;
    let key = RsaKeyPair::generate(size).map_err(|err| err.to_string())?;
    let signature = key.sign(alg, message).map_err(|err| err.to_string())?;
    let (n, e) = pkcs1_public(key.public_key(alg).as_ref())?;
    public_reply(vec![n, e, signature.as_ref().to_vec()])
}

fn rsa_sigver(rest: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    let (hash, pad) = rest
        .split_once('/')
        .ok_or_else(|| format!("unsupported RSA sigVer {rest}"))?;
    let n = arg(args, 0)?;
    let e = arg(args, 1)?;
    let message = arg(args, 2)?;
    let signature = arg(args, 3)?;
    let alg = rsa_verify_alg(hash, pad)?;
    let der = pkcs1_encode(n, e);
    let ok = PublicKey::new(alg, &der)
        .and_then(|key| key.verify(message, signature))
        .is_ok();
    public_reply(vec![vec![u8::from(ok)]])
}

fn rsa_sign_alg(
    hash: &str,
    pad: &str,
) -> Result<&'static rind::signature::RsaSigningAlgorithm, String> {
    Ok(match (hash, pad) {
        ("SHA2-256", "pkcs1v1.5") => &sign::RSA_PKCS1_SHA256,
        ("SHA2-384", "pkcs1v1.5") => &sign::RSA_PKCS1_SHA384,
        ("SHA2-512", "pkcs1v1.5") => &sign::RSA_PKCS1_SHA512,
        ("SHA2-256", "pss") => &sign::RSA_PSS_SHA256,
        ("SHA2-384", "pss") => &sign::RSA_PSS_SHA384,
        ("SHA2-512", "pss") => &sign::RSA_PSS_SHA512,
        _ => return Err(format!("unsupported RSA signature {hash} {pad}")),
    })
}

fn rsa_verify_alg(
    hash: &str,
    pad: &str,
) -> Result<&'static rind::signature::RsaVerificationAlgorithm, String> {
    Ok(match (hash, pad) {
        ("SHA2-256", "pkcs1v1.5") => &verify::RSA_PKCS1_SHA256,
        ("SHA2-384", "pkcs1v1.5") => &verify::RSA_PKCS1_SHA384,
        ("SHA2-512", "pkcs1v1.5") => &verify::RSA_PKCS1_SHA512,
        ("SHA-1", "pkcs1v1.5") => &verify::legacy::RSA_PKCS1_SHA1,
        ("SHA2-256", "pss") => &verify::RSA_PSS_SHA256,
        ("SHA2-384", "pss") => &verify::RSA_PSS_SHA384,
        ("SHA2-512", "pss") => &verify::RSA_PSS_SHA512,
        _ => return Err(format!("unsupported RSA verification {hash} {pad}")),
    })
}

fn pkcs1_encode(n: &[u8], e: &[u8]) -> Vec<u8> {
    let mut body = der_int(n);
    body.extend(der_int(e));
    der_tl(0x30, &body)
}

fn pkcs1_public(der: &[u8]) -> Result<(Vec<u8>, Vec<u8>), String> {
    let mut der = der;
    let seq = der_read(&mut der, 0x30)?;
    let mut seq = seq.as_slice();
    let n = der_int_bytes(&mut seq)?;
    let e = der_int_bytes(&mut seq)?;
    Ok((n, e))
}

fn der_read(input: &mut &[u8], tag: u8) -> Result<Vec<u8>, String> {
    let (got, rest) = input.split_first().ok_or("DER")?;
    if *got != tag {
        return Err("DER tag".into());
    }
    let (len_byte, rest) = rest.split_first().ok_or("DER length")?;
    let (len, rest) = if len_byte & 0x80 == 0 {
        (*len_byte as usize, rest)
    } else {
        let n = (len_byte & 0x7f) as usize;
        if n == 0 || n > 3 || rest.len() < n {
            return Err("DER length".into());
        }
        let mut len = 0usize;
        for byte in &rest[..n] {
            len = (len << 8) | *byte as usize;
        }
        (len, &rest[n..])
    };
    if rest.len() < len {
        return Err("DER value".into());
    }
    *input = &rest[len..];
    Ok(rest[..len].to_vec())
}

fn der_int_bytes(input: &mut &[u8]) -> Result<Vec<u8>, String> {
    let mut body = der_read(input, 0x02)?;
    if body.first() == Some(&0) {
        body.remove(0);
    }
    if body.is_empty() {
        body.push(0);
    }
    Ok(body)
}

fn rsa_primitive(args: &[Vec<u8>]) -> Result<Reply, String> {
    // signaturePrimitive: d, n, e, message. decryptionPrimitive: ct, d, n, e.
    // Both are base^d mod n. The two orders differ, so tell them apart by
    // which argument is the short public exponent.
    let (base, exp, modulus) = if args.len() >= 4 && args[2].len() <= 8 && args[1].len() > 8 {
        (arg(args, 3)?, arg(args, 0)?, arg(args, 1)?)
    } else if args.len() >= 4 && args[3].len() <= 8 {
        (arg(args, 0)?, arg(args, 1)?, arg(args, 2)?)
    } else {
        return Err("RSA primitive arguments".into());
    };
    rsa_modexp_reply(base, exp, modulus)
}

fn rsa_decrypt(args: &[Vec<u8>], crt: bool) -> Result<Reply, String> {
    // standard: ct, d, n, e. crt: ct, d, dmp1, dmq1, iqmp, p, q, n, e.
    // The plaintext is still ct^d mod n. SP 800-56B rejects 0, 1, and n−1.
    let (base, exp, modulus) = if crt {
        (arg(args, 0)?, arg(args, 1)?, arg(args, 7)?)
    } else {
        (arg(args, 0)?, arg(args, 1)?, arg(args, 2)?)
    };
    if trivial_rsa_ciphertext(base, modulus) {
        return public_reply(vec![vec![0], Vec::new()]);
    }
    rsa_modexp_reply(base, exp, modulus)
}

fn rsa_modexp_reply(base: &[u8], exp: &[u8], modulus: &[u8]) -> Result<Reply, String> {
    match rind::acvp::rsa_modexp(base, exp, modulus) {
        Some(out) => Ok(with_secret(vec![vec![1]], out)),
        None => public_reply(vec![vec![0], Vec::new()]),
    }
}

/// SP 800-56B's decryption primitive refuses a ciphertext of 0, 1, or n−1.
fn trivial_rsa_ciphertext(base: &[u8], modulus: &[u8]) -> bool {
    let base = trim_zeros(base);
    if base.is_empty() || base == [1] {
        return true;
    }
    let modulus = trim_zeros(modulus);
    if base.len() != modulus.len() || modulus.is_empty() {
        return false;
    }
    let mut predecessor = modulus.to_vec();
    for byte in predecessor.iter_mut().rev() {
        if *byte > 0 {
            *byte -= 1;
            break;
        }
        *byte = 0xff;
    }
    base == predecessor
}

fn trim_zeros(bytes: &[u8]) -> &[u8] {
    bytes
        .iter()
        .position(|byte| *byte != 0)
        .map_or(&[], |i| &bytes[i..])
}

fn hmac_drbg(rest: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    let (kind, hash_name) = if let Some(hash) = rest.strip_prefix("-pr/") {
        ("pr", hash)
    } else if let Some(hash) = rest.strip_prefix("-reseed/") {
        ("reseed", hash)
    } else if let Some(hash) = rest.strip_prefix('/') {
        ("generate", hash)
    } else {
        return Err(format!("unsupported DRBG command {rest}"));
    };
    let out_len = u32_arg(arg(args, 0)?).ok_or("DRBG length")? as usize;
    if out_len > MAX_DRBG {
        return Err("DRBG output is too long".into());
    }
    let entropy = arg(args, 1)?;
    let personalisation = arg(args, 2)?;
    let mut out = vec![0u8; out_len];
    let mut drbg = match kind {
        "generate" => {
            let nonce = arg(args, 5)?;
            rind::acvp::AcvpDrbg::new(hash_name, entropy, nonce, personalisation)
        }
        "reseed" | "pr" => {
            let nonce = arg(args, 7)?;
            rind::acvp::AcvpDrbg::new(hash_name, entropy, nonce, personalisation)
        }
        _ => unreachable!(),
    }
    .ok_or_else(|| format!("unsupported DRBG hash {hash_name}"))?;
    match kind {
        "generate" => {
            drbg.generate(&mut out, arg(args, 3)?);
            drbg.generate(&mut out, arg(args, 4)?);
        }
        "reseed" => {
            drbg.reseed(arg(args, 4)?, arg(args, 3)?);
            drbg.generate(&mut out, arg(args, 5)?);
            drbg.generate(&mut out, arg(args, 6)?);
        }
        "pr" => {
            drbg.reseed(arg(args, 4)?, arg(args, 3)?);
            drbg.generate(&mut out, &[]);
            drbg.reseed(arg(args, 6)?, arg(args, 5)?);
            drbg.generate(&mut out, &[]);
        }
        _ => unreachable!(),
    }
    public_reply(vec![out])
}

const MAX_DRBG: usize = 1 << 16;

/// Algorithms `acvptool` knows. A name it does not is refused before any
/// vector is read. RSA key generation is absent: rind has no seeded or
/// candidate-prime FIPS 186-5 key generation, and the quest allows keeping
/// it out of the module. AES-GCM internal IVs wait on their own quest.
const CONFIG: &str = r#"[
  {"algorithm": "SHA-1", "revision": "1.0", "messageLength": [{"min": 0, "max": 65536, "increment": 8}]},
  {"algorithm": "SHA2-256", "revision": "1.0", "messageLength": [{"min": 0, "max": 65536, "increment": 8}]},
  {"algorithm": "SHA2-384", "revision": "1.0", "messageLength": [{"min": 0, "max": 65536, "increment": 8}]},
  {"algorithm": "SHA2-512", "revision": "1.0", "messageLength": [{"min": 0, "max": 65536, "increment": 8}]},
  {"algorithm": "SHA2-512/256", "revision": "1.0", "messageLength": [{"min": 0, "max": 65536, "increment": 8}]},
  {"algorithm": "SHA3-256", "revision": "2.0", "messageLength": [{"min": 0, "max": 65536, "increment": 8}]},
  {"algorithm": "SHA3-384", "revision": "2.0", "messageLength": [{"min": 0, "max": 65536, "increment": 8}]},
  {"algorithm": "SHA3-512", "revision": "2.0", "messageLength": [{"min": 0, "max": 65536, "increment": 8}]},
  {"algorithm": "ACVP-AES-ECB", "revision": "1.0", "direction": ["encrypt"], "keyLen": [128, 192, 256]},
  {"algorithm": "ACVP-AES-CBC", "revision": "1.0", "direction": ["encrypt", "decrypt"], "keyLen": [128, 192, 256]},
  {"algorithm": "ACVP-AES-CTR", "revision": "1.0", "direction": ["encrypt", "decrypt"], "keyLen": [128, 192, 256]},
  {"algorithm": "ACVP-AES-GCM", "revision": "1.0", "direction": ["encrypt", "decrypt"], "keyLen": [128, 192, 256], "tagLen": [128, 120, 112, 104, 96, 64, 32], "ivLen": [96], "ivGen": ["external"]},
  {"algorithm": "ACVP-AES-GMAC", "revision": "1.0", "direction": ["encrypt", "decrypt"], "keyLen": [128, 192, 256], "tagLen": [128, 120, 112, 104, 96, 64, 32], "ivLen": [96], "ivGen": ["external"]},
  {"algorithm": "ACVP-AES-KW", "revision": "1.0", "direction": ["encrypt", "decrypt"], "kwCipher": ["cipher"], "keyLen": [128, 192, 256]},
  {"algorithm": "ACVP-AES-KWP", "revision": "1.0", "direction": ["encrypt", "decrypt"], "kwCipher": ["cipher"], "keyLen": [128, 192, 256]},
  {"algorithm": "HMAC-SHA-1", "revision": "2.0"},
  {"algorithm": "HMAC-SHA2-256", "revision": "2.0"},
  {"algorithm": "HMAC-SHA2-384", "revision": "2.0"},
  {"algorithm": "HMAC-SHA2-512", "revision": "2.0"},
  {"algorithm": "KDA", "mode": "HKDF", "revision": "Sp800-56Cr2"},
  {"algorithm": "PBKDF", "revision": "1.0"},
  {"algorithm": "ECDSA", "mode": "keyGen", "revision": "FIPS186-5", "curve": ["P-256", "P-384", "P-521"], "secretGenerationMode": ["testing candidates"]},
  {"algorithm": "ECDSA", "mode": "keyVer", "revision": "FIPS186-5", "curve": ["P-256", "P-384", "P-521"]},
  {"algorithm": "ECDSA", "mode": "sigGen", "revision": "FIPS186-5", "curve": ["P-256", "P-384", "P-521"]},
  {"algorithm": "ECDSA", "mode": "sigVer", "revision": "FIPS186-5", "curve": ["P-256", "P-384", "P-521"]},
  {"algorithm": "EDDSA", "mode": "keyGen", "revision": "1.0", "curve": ["ED-25519"]},
  {"algorithm": "EDDSA", "mode": "keyVer", "revision": "1.0", "curve": ["ED-25519"]},
  {"algorithm": "EDDSA", "mode": "sigGen", "revision": "1.0", "curve": ["ED-25519"]},
  {"algorithm": "EDDSA", "mode": "sigVer", "revision": "1.0", "curve": ["ED-25519"]},
  {"algorithm": "KAS-ECC-SSC", "revision": "Sp800-56Ar3"},
  {"algorithm": "ML-KEM", "mode": "keyGen", "revision": "FIPS203", "parameterSets": ["ML-KEM-768"]},
  {"algorithm": "ML-KEM", "mode": "encapDecap", "revision": "FIPS203", "parameterSets": ["ML-KEM-768"]},
  {"algorithm": "ML-DSA", "mode": "keyGen", "revision": "FIPS204", "parameterSets": ["ML-DSA-44", "ML-DSA-65", "ML-DSA-87"]},
  {"algorithm": "ML-DSA", "mode": "sigGen", "revision": "FIPS204", "parameterSets": ["ML-DSA-44", "ML-DSA-65", "ML-DSA-87"]},
  {"algorithm": "ML-DSA", "mode": "sigVer", "revision": "FIPS204", "parameterSets": ["ML-DSA-44", "ML-DSA-65", "ML-DSA-87"]},
  {"algorithm": "RSA", "mode": "sigGen", "revision": "FIPS186-5"},
  {"algorithm": "RSA", "mode": "sigVer", "revision": "FIPS186-5"},
  {"algorithm": "RSA", "mode": "signaturePrimitive", "revision": "2.0"},
  {"algorithm": "RSA", "mode": "decryptionPrimitive", "revision": "Sp800-56Br2"},
  {"algorithm": "hmacDRBG", "revision": "1.0", "predResistanceEnabled": [true, false]}
]"#;

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(s: &str) -> Vec<u8> {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
            .collect()
    }

    #[test]
    fn aes_cbc_refuses_a_long_iterated_message() {
        let err = handle(
            "AES-CBC/encrypt",
            &[
                vec![0; 16],
                vec![0; 32],
                vec![0; 16],
                2u32.to_ne_bytes().to_vec(),
            ],
        );
        assert!(err.is_err());
    }

    /// aws-lc's `testmodulewrapper` HMAC_DRBG vector: the second generate
    /// after a reseed, with empty additional input.
    #[test]
    fn hmac_drbg_second_generate() {
        let out_len = (128u32).to_ne_bytes().to_vec();
        let reply = handle(
            "hmacDRBG-reseed/SHA2-256",
            &[
                out_len,
                hex("06032cd5eed33f39265f49ecb142c511da9aff2af71203bffaf34a9ca5bd9c0d"),
                Vec::new(),
                Vec::new(),
                hex("01920a4e669ed3a85ae8a33b35a74ad7fb2a6bb4cf395ce00334a9c9a5a5d552"),
                Vec::new(),
                Vec::new(),
                hex("0e66f71edc43e42a45ad3c6fc6cdc4df"),
            ],
        )
        .unwrap();
        assert_eq!(
            reply[0],
            hex(
                "76fc79fe9b50beccc991a11b5635783a83536add03c157fb30645e611c2898bb2b1bc215000209208cd506cb28da2a51bdb03826aaf2bd2335d576d519160842e7158ad0949d1a9ec3e66ea1b1a064b005de914eac2e9d4f2d72a8616a80225422918250ff66a41bd2f864a6a38cc5b6499dc43f7f2bd09e1e0f8f5885935124"
            )
        );
    }

    /// RFC 5869 A.1. Extract and expand both return `Result` since the FIPS
    /// module landed; this is the chain `KDA/HKDF` runs.
    #[test]
    fn hkdf_sha256_rfc5869_case_1() {
        let reply = handle(
            "KDA/HKDF/SHA2-256",
            &[
                hex("0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b"),
                hex("000102030405060708090a0b0c"),
                hex("f0f1f2f3f4f5f6f7f8f9"),
                42u32.to_ne_bytes().to_vec(),
            ],
        )
        .unwrap();
        assert_eq!(
            reply[0],
            hex(
                "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865"
            )
        );
    }
}
