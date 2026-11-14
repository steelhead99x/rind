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

/// One wrapper session, owning the RSA signing keys reused by its groups.
#[derive(Default)]
pub struct Wrapper {
    rsa_keys: Vec<CachedSigGen>,
}

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

    /// Moves the wiping allocation at `index` out. The span stays empty.
    pub fn take_secret(&mut self, index: usize) -> Option<Box<rind::acvp::SecretBuf>> {
        let slot = self.parts.get_mut(index)?;
        match std::mem::replace(slot, Part::Public(Vec::new())) {
            Part::Secret(buf) => Some(buf),
            public => {
                *slot = public;
                None
            }
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

impl Wrapper {
    /// Runs one operation, retaining only the signing keys its session reuses.
    pub fn handle(&mut self, command: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
        if command == "getConfig" {
            exact_args::<0>(args)?;
            return public_reply(vec![CONFIG.as_bytes().to_vec()]);
        }
        if let Some(hash) = hash_alg(command) {
            return hash_oneshot(hash, exact_args::<1>(args)?);
        }
        if let Some(name) = command.strip_suffix("/MCT") {
            return hash_mct(name, exact_args::<1>(args)?);
        }
        if let Some(name) = command.strip_suffix("/LDT") {
            return hash_ldt(name, exact_args::<2>(args)?);
        }
        if let Some(hash) = hmac_alg(command) {
            return hmac(hash, exact_args::<2>(args)?);
        }
        match command {
            "AES/encrypt" => aes_ecb(true, exact_args::<3>(args)?),
            "AES/decrypt" => Err("AES-ECB decryption is outside the module".into()),
            "AES-CBC/encrypt" => aes_cbc(true, exact_args::<4>(args)?),
            "AES-CBC/decrypt" => aes_cbc(false, exact_args::<4>(args)?),
            "AES-CTR/encrypt" | "AES-CTR/decrypt" => aes_ctr(exact_args::<4>(args)?),
            "AES-GCM/seal" => gcm_seal(exact_args::<5>(args)?),
            "AES-GCM/open" => gcm_open(exact_args::<5>(args)?),
            "AES-KW/seal" => kw_seal(false, exact_args::<5>(args)?),
            "AES-KW/open" => kw_open(false, exact_args::<5>(args)?),
            "AES-KWP/seal" => kw_seal(true, exact_args::<5>(args)?),
            "AES-KWP/open" => kw_open(true, exact_args::<5>(args)?),
            "PBKDF" => pbkdf(exact_args::<5>(args)?),
            "ECDSA/keyGen" => ecdsa_keygen(exact_args::<1>(args)?),
            "ECDSA/keyVer" => ecdsa_keyver(exact_args::<3>(args)?),
            "ECDSA/sigGen" => ecdsa_siggen(exact_args::<4>(args)?, false),
            "ECDSA/sigGen/componentTest" => ecdsa_siggen(exact_args::<4>(args)?, true),
            "ECDSA/sigVer" => ecdsa_sigver(exact_args::<7>(args)?),
            "EDDSA/ED-25519/keyGen" => {
                exact_args::<0>(args)?;
                ed25519_keygen()
            }
            "EDDSA/ED-25519/keyVer" => ed25519_keyver(exact_args::<1>(args)?),
            "EDDSA/ED-25519/sigGen" => ed25519_siggen(exact_args::<2>(args)?),
            "EDDSA/ED-25519/sigVer" => ed25519_sigver(exact_args::<3>(args)?),
            "ML-KEM/ML-KEM-768/keyGen" => mlkem_keygen(exact_args::<2>(args)?),
            "ML-KEM/ML-KEM-768/encap" => mlkem_encap(exact_args::<2>(args)?),
            "ML-KEM/ML-KEM-768/decap" => mlkem_decap(exact_args::<2>(args)?),
            "ML-KEM/ML-KEM-768/encapKeyCheck" => mlkem_ek_check(exact_args::<1>(args)?),
            "ML-KEM/ML-KEM-768/decapKeyCheck" => mlkem_dk_check(exact_args::<1>(args)?),
            "RSA/signaturePrimitive" => rsa_primitive(exact_args::<4>(args)?),
            "RSA/decryptionPrimitive" => rsa_decrypt(exact_args::<4>(args)?, false),
            "RSA/decryptionPrimitive/crt" => rsa_decrypt(exact_args::<9>(args)?, true),
            _ => self.other(command, args),
        }
    }

    fn other(&mut self, command: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
        if let Some(rest) = command.strip_prefix("KDA/HKDF/") {
            return hkdf(rest, exact_args::<4>(args)?);
        }
        if let Some(rest) = command.strip_prefix("HKDF/") {
            return hkdf_half(rest, args);
        }
        if let Some(rest) = command.strip_prefix("ECDH/") {
            return ecdh(rest, exact_args::<3>(args)?);
        }
        if let Some(rest) = command.strip_prefix("hmacDRBG") {
            return hmac_drbg(rest, args);
        }
        if let Some(rest) = command.strip_prefix("ML-DSA/") {
            return mldsa(rest, args);
        }
        if let Some(rest) = command.strip_prefix("RSA/sigGen/") {
            return rsa_siggen(&mut self.rsa_keys, rest, exact_args::<2>(args)?);
        }
        if let Some(rest) = command.strip_prefix("RSA/sigVer/") {
            return rsa_sigver(rest, exact_args::<4>(args)?);
        }
        Err(format!("unsupported ACVP command {command}"))
    }
}

fn arg(args: &[Vec<u8>], n: usize) -> Result<&[u8], String> {
    args.get(n)
        .map(Vec::as_slice)
        .ok_or_else(|| format!("missing argument {n}"))
}

fn exact_args<const N: usize>(args: &[Vec<u8>]) -> Result<&[Vec<u8>; N], String> {
    args.try_into()
        .map_err(|_| format!("expected {N} arguments, got {}", args.len()))
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
    let full = times
        .checked_mul(u64::try_from(content.len()).map_err(|_| "LDT content length")?)
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
    if !matches!(iterations, 1 | 1000) || iterations == 1000 && result.len() != 16 {
        return Err("AES takes one AFT iteration or 1000 single-block MCT iterations".into());
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
    if input.is_empty()
        || input.len() % 16 != 0
        || iv.len() != 16
        || !matches!(iterations, 1 | 1000)
        || iterations == 1000 && input.len() != 16
    {
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
    // aws-lc's wrapper calls AES_ctr128_encrypt, which carries through all 128
    // bits. The sample groups are RFC 3686 and do not carry out of the low 32.
    AesCtr::new(aes_alg(key.len())?, key, 128)
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
    let key = gcm::Key::new(aes_alg(key_bytes.len())?, key_bytes, tag_length(tag_bytes)?)
        .map_err(|err| err.to_string())?;
    let iv = gcm::Iv::assume_unique_for_key(nonce).map_err(|err| err.to_string())?;
    if combined.len() < tag_bytes {
        return public_reply(vec![vec![0], Vec::new()]);
    }
    let (ct, tag) = combined.split_at(combined.len() - tag_bytes);
    let mut text = ct.to_vec();
    match key.open_in_place_separate_tag(iv, aad, tag, &mut text) {
        Ok(pt) => public_reply(vec![vec![1], pt.to_vec()]),
        Err(_) => public_reply(vec![vec![0], Vec::new()]),
    }
}

fn kw_seal(padded: bool, args: &[Vec<u8>]) -> Result<Reply, String> {
    // acvptool passes dummy, key, plaintext, dummy, dummy.
    let key = arg(args, 1)?;
    let plain = arg(args, 2)?;
    if plain.len() > 512 {
        return Err("AES key-wrap payload exceeds the advertised capability".into());
    }
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
    if wrapped.len() > 520 {
        return Err("AES key-wrap payload exceeds the advertised capability".into());
    }
    let kek = AesKek::new(aes_alg(key.len())?, key).map_err(|err| err.to_string())?;
    if wrapped.len() < 8 {
        return public_reply(vec![vec![0], Vec::new()]);
    }
    let mut plain =
        rind::acvp::SecretBuf::zeroed(wrapped.len() - 8).map_err(|err| err.to_string())?;
    let opened = if padded {
        // RFC 5649 authenticates and returns the used prefix. Keep that
        // prefix in the same wiping allocation, including on failure.
        kek.unwrap_padded(wrapped, plain.as_mut_slice())
            .map(|got| got.len())
    } else {
        kek.unwrap(wrapped, plain.as_mut_slice())
            .map(|()| wrapped.len() - 8)
    };
    match opened {
        Ok(len) => {
            plain.truncate(len).map_err(|err| err.to_string())?;
            Ok(with_secret(vec![vec![1]], plain))
        }
        Err(_) => public_reply(vec![vec![0], Vec::new()]),
    }
}

fn pbkdf(args: &[Vec<u8>]) -> Result<Reply, String> {
    let password = arg(args, 0)?;
    let salt = arg(args, 1)?;
    let iterations = u32_arg(arg(args, 2)?).ok_or("PBKDF iterations")?;
    let hash = std::str::from_utf8(arg(args, 3)?).map_err(|_| "PBKDF hash name")?;
    let bits = u32_arg(arg(args, 4)?).ok_or("PBKDF length")?;
    // These are the capability domains advertised by getConfig. Check them
    // before allocating output or accepting iteration work from the prompt.
    if !(112..=4096).contains(&bits)
        || bits % 8 != 0
        || !(1..=10_000).contains(&iterations)
        || !(16..=512).contains(&salt.len())
        || !(8..=128).contains(&password.len())
    {
        return Err("PBKDF parameters are outside the advertised capability".into());
    }
    let alg = match hash {
        "SHA-1" => &pbkdf2::legacy::PBKDF2_HMAC_SHA1,
        "SHA2-256" => &pbkdf2::PBKDF2_HMAC_SHA256,
        "SHA2-384" => &pbkdf2::PBKDF2_HMAC_SHA384,
        "SHA2-512" => &pbkdf2::PBKDF2_HMAC_SHA512,
        _ => return Err(format!("unsupported PBKDF hash {hash}")),
    };
    let mut out =
        rind::acvp::SecretBuf::zeroed((bits / 8) as usize).map_err(|err| err.to_string())?;
    Secret::new(alg, password)
        .derive(
            NonZeroU32::new(iterations).ok_or("PBKDF iterations are zero")?,
            salt,
            out.as_mut_slice(),
        )
        .map_err(|err| err.to_string())?;
    Ok(with_secret(Vec::new(), out))
}

fn hkdf(hash: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    let key = arg(args, 0)?;
    let salt = arg(args, 1)?;
    let info = arg(args, 2)?;
    let out_len = u32_arg(arg(args, 3)?).ok_or("HKDF length")? as usize;
    let (alg, _) = hkdf_alg(hash)?;
    // Extract and expand return `Result` so rind-fips can refuse an empty
    // salt or info. rind accepts both, and the errors still propagate.
    let prk = rind::hkdf::Salt::new(alg, salt)
        .extract(key)
        .map_err(|err| err.to_string())?;
    let info = [info];
    let expanded = prk.expand(&info, out_len).map_err(|err| err.to_string())?;
    let mut out = rind::acvp::SecretBuf::zeroed(out_len).map_err(|err| err.to_string())?;
    expanded
        .fill(out.as_mut_slice())
        .map_err(|err| err.to_string())?;
    Ok(with_secret(Vec::new(), out))
}

fn hkdf_half(rest: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    let (hash, op) = rest
        .rsplit_once('/')
        .ok_or_else(|| format!("unsupported HKDF command {rest}"))?;
    let (alg, hmac_alg) = hkdf_alg(hash)?;
    match op {
        "extract" => {
            exact_args::<2>(args)?;
            let ikm = arg(args, 0)?;
            let salt = arg(args, 1)?;
            let prk = hmac::sign(&HmacKey::new(hmac_alg, salt), ikm);
            Ok(with_secret(
                Vec::new(),
                rind::acvp::SecretBuf::from_slice(prk.as_ref()),
            ))
        }
        "expand" => {
            exact_args::<3>(args)?;
            let out_len = u32_arg(arg(args, 0)?).ok_or("HKDF length")? as usize;
            let prk = arg(args, 1)?;
            let info = arg(args, 2)?;
            Ok(with_secret(
                Vec::new(),
                rind::acvp::hkdf_expand(alg, prk, info, out_len).map_err(|err| err.to_string())?,
            ))
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
        let scalar = pad_secret(private, field)?;
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
    // ACVP writes a public coordinate with a leading zero when its top bit is set.
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

/// A secret scalar at exactly `len` bytes.
///
/// A longer encoding's extra prefix has a public length. Every byte of that
/// prefix is read, and the scalar is rejected when any of them is nonzero.
/// The field bytes themselves are not scanned.
fn pad_secret(bytes: &[u8], len: usize) -> Result<Vec<u8>, String> {
    rind::acvp::field_bytes(bytes, len)
        .ok_or_else(|| format!("value is {} bytes, above {len}", bytes.len()))
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
    let alg = ecdsa_verifier(curve, "SHA2-256")?;
    let Ok(point) = uncompressed(curve, arg(args, 1)?, arg(args, 2)?) else {
        return public_reply(vec![vec![0]]);
    };
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

fn ecdsa_sign(curve: &str, scalar: &[u8], hash: &str, message: &[u8]) -> Result<Reply, String> {
    let (agreement, field) = match curve {
        "P-256" => (&ECDH_P256, 32),
        "P-384" => (&ECDH_P384, 48),
        "P-521" => (&ECDH_P521, 66),
        _ => return Err(format!("unsupported curve {curve}")),
    };
    // Both loaders need the same field-width scalar. The signing loader
    // requires that exact width even when the original encoding was padded.
    let scalar = pad_secret(scalar, field)?;
    let agreement = PrivateKey::from_scalar(agreement, &scalar).map_err(|err| err.to_string())?;
    let alg = ecdsa_signer(curve)?;
    let key =
        EcdsaKeyPair::from_scalar_and_public_key(alg, &scalar, agreement.public_key().as_ref())
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
    let alg = ecdsa_verifier(curve, hash)?;
    let Ok(point) = uncompressed(curve, arg(args, 3)?, arg(args, 4)?) else {
        return public_reply(vec![vec![0]]);
    };
    let r = arg(args, 5)?;
    let s = arg(args, 6)?;
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
    // These integers are public. Find their significant prefix once instead
    // of shifting the whole buffer for each leading zero.
    let bytes = trim_zeros(bytes);
    if bytes.is_empty() {
        return der_tl(0x02, &[0]);
    }
    let mut body = bytes.to_vec();
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
    } else {
        let length = body.len().to_be_bytes();
        let length = trim_zeros(&length);
        out.push(0x80 | length.len() as u8);
        out.extend_from_slice(length);
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
    if d.len() != 32 || z.len() != 32 {
        return Err("ML-KEM keyGen needs 32-byte d and z".into());
    }
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
        "keyGen" => mldsa_keygen(set, &exact_args::<1>(args)?[0]),
        "sigGen" => mldsa_siggen(set, args),
        "sigVer" => mldsa_sigver(set, args),
        _ => Err(format!("unsupported ML-DSA operation {op}")),
    }
}

fn mldsa_keygen(set: &str, seed: &[u8]) -> Result<Reply, String> {
    let (pk, sk) = match set {
        "ML-DSA-44" => mldsa_pair::<MlDsa44>(seed)?,
        "ML-DSA-65" => mldsa_pair::<MlDsa65>(seed)?,
        "ML-DSA-87" => mldsa_pair::<MlDsa87>(seed)?,
        _ => return Err(format!("unsupported ML-DSA set {set}")),
    };
    Ok(with_secret(vec![pk], sk))
}

fn mldsa_pair<P: sign::MlDsaParameterSet>(
    seed: &[u8],
) -> Result<(Vec<u8>, rind::acvp::SecretBuf), String> {
    let key = MlDsaKeyPair::<P>::from_seed(seed).map_err(|err| err.to_string())?;
    Ok((key.public_key().as_ref().to_vec(), key.expanded_secret()))
}

fn mldsa_siggen(set: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    mldsa_args(args)?;
    // sk, message, mu, rnd, context, externalMu flag, optional interface.
    let sk = arg(args, 0)?;
    let message = arg(args, 1)?;
    let provided = arg(args, 2)?;
    let rnd = arg(args, 3)?;
    let context = arg(args, 4)?;
    let external_mu = arg(args, 5)?;
    let (mu, internal) = mldsa_mu(external_mu, args.get(6).map(Vec::as_slice), provided)?;
    let rnd_zeros;
    let rnd = if rnd.is_empty() {
        rnd_zeros = [0u8; 32];
        rnd_zeros.as_slice()
    } else {
        rnd
    };
    let request = MldsaSigning {
        sk,
        message,
        mu,
        internal,
        rnd,
        context,
    };
    let sig = match set {
        "ML-DSA-44" => mldsa_sign::<MlDsa44>(&request)?,
        "ML-DSA-65" => mldsa_sign::<MlDsa65>(&request)?,
        "ML-DSA-87" => mldsa_sign::<MlDsa87>(&request)?,
        _ => return Err(format!("unsupported ML-DSA set {set}")),
    };
    public_reply(vec![sig])
}

/// How ACVP names the message representative.
///
/// A seventh argument, `b"internal"` or `b"external"`, is the group's
/// `signatureInterface`. Without it, acvptool's absent `externalMu` (an
/// empty flag) names the external interface; a present boolean names the
/// internal interface, with `1` selecting a supplied `mu`. Context may be
/// empty on the external interface, so it cannot choose the interface.
fn mldsa_mu<'a>(
    external_mu: &'a [u8],
    interface: Option<&'a [u8]>,
    provided: &'a [u8],
) -> Result<(Option<&'a [u8]>, bool), String> {
    if !matches!(external_mu, [] | [0] | [1]) {
        return Err("ML-DSA externalMu must be absent or one boolean byte".into());
    }
    if let Some(interface) = interface {
        return match interface {
            b"internal" if external_mu == [1] => Ok((Some(provided), true)),
            b"internal" => Ok((None, true)),
            b"external" if external_mu != [1] => Ok((None, false)),
            _ => Err("ML-DSA signature interface".into()),
        };
    }
    match external_mu {
        [] => Ok((None, false)),
        [1] => Ok((Some(provided), true)),
        [0] => Ok((None, true)),
        _ => Err("ML-DSA externalMu".into()),
    }
}

fn mldsa_args(args: &[Vec<u8>]) -> Result<(), String> {
    if (6..=7).contains(&args.len()) {
        Ok(())
    } else {
        Err(format!(
            "ML-DSA needs six arguments and an optional interface, got {}",
            args.len()
        ))
    }
}

fn load_mldsa<P: sign::MlDsaParameterSet>(sk: &[u8]) -> Result<MlDsaKeyPair<P>, String> {
    if sk.len() == 32 {
        MlDsaKeyPair::<P>::from_seed(sk).map_err(|err| err.to_string())
    } else {
        MlDsaKeyPair::<P>::from_expanded(sk).map_err(|err| err.to_string())
    }
}

struct MldsaSigning<'a> {
    sk: &'a [u8],
    message: &'a [u8],
    mu: Option<&'a [u8]>,
    internal: bool,
    rnd: &'a [u8],
    context: &'a [u8],
}

fn mldsa_sign<P: sign::MlDsaParameterSet>(request: &MldsaSigning<'_>) -> Result<Vec<u8>, String> {
    Ok(load_mldsa::<P>(request.sk)?
        .sign_acvp(
            request.context,
            request.message,
            request.mu,
            request.internal,
            request.rnd,
        )
        .map_err(|err| err.to_string())?
        .as_ref()
        .to_vec())
}

fn mldsa_sigver(set: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
    mldsa_args(args)?;
    // signature, pk, message, mu, context, externalMu, optional interface.
    let signature = arg(args, 0)?;
    let pk = arg(args, 1)?;
    let message = arg(args, 2)?;
    let provided = arg(args, 3)?;
    let context = arg(args, 4)?;
    let external_mu = arg(args, 5)?;
    let (mu, internal) = mldsa_mu(external_mu, args.get(6).map(Vec::as_slice), provided)?;
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

/// One generated key per `(bits, hash, pad)` for the session.
///
/// `acvptool` signs every test in a sigGen group with one key and rejects a
/// wrapper that returns a different modulus mid-group. The box keeps private
/// key bytes in one allocation when the cache grows; its key is wiped before
/// that allocation is freed when the session ends, including on an error.
struct CachedSigGen {
    bits: u32,
    hash: String,
    pad: String,
    key: Box<RsaKeyPair>,
}

fn rsa_siggen(keys: &mut Vec<CachedSigGen>, rest: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
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
    if !keys
        .iter()
        .any(|cached| cached.bits == bits && cached.hash == hash && cached.pad == pad)
    {
        let key = RsaKeyPair::generate(size).map_err(|err| err.to_string())?;
        keys.push(CachedSigGen {
            bits,
            hash: hash.to_string(),
            pad: pad.to_string(),
            key: Box::new(key),
        });
    }
    let cached = keys
        .iter()
        .find(|cached| cached.bits == bits && cached.hash == hash && cached.pad == pad)
        .ok_or("RSA sigGen key")?;
    let signature = cached
        .key
        .sign(alg, message)
        .map_err(|err| err.to_string())?;
    let (n, e) = pkcs1_public(cached.key.public_key(alg).as_ref())?;
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
    // Verify the private result with e even when only n, e, and d are given.
    rsa_primitive_reply(rind::acvp::rsa_private(
        arg(args, 3)?,
        arg(args, 0)?,
        arg(args, 1)?,
        arg(args, 2)?,
    ))
}

fn rsa_decrypt(args: &[Vec<u8>], crt: bool) -> Result<Reply, String> {
    // standard: ct, d, n, e. crt: ct, d, dmp1, dmq1, iqmp, p, q, n, e.
    // The plaintext is still ct^d mod n. SP 800-56B rejects 0, 1, and n−1.
    let (base, modulus) = if crt {
        (arg(args, 0)?, arg(args, 7)?)
    } else {
        (arg(args, 0)?, arg(args, 2)?)
    };
    if trivial_rsa_ciphertext(base, modulus) {
        return public_reply(vec![vec![0], Vec::new()]);
    }
    if crt {
        let key = rind::acvp::RsaCrtComponents {
            n: modulus,
            e: arg(args, 8)?,
            d: arg(args, 1)?,
            p: arg(args, 5)?,
            q: arg(args, 6)?,
            dp: arg(args, 2)?,
            dq: arg(args, 3)?,
            iqmp: arg(args, 4)?,
        };
        rsa_primitive_reply(rind::acvp::rsa_crt(base, &key))
    } else {
        rsa_primitive_reply(rind::acvp::rsa_private(
            base,
            arg(args, 1)?,
            modulus,
            arg(args, 3)?,
        ))
    }
}

fn rsa_primitive_reply(output: Option<rind::acvp::SecretBuf>) -> Result<Reply, String> {
    match output {
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
    let entropy = arg(args, 1)?;
    let personalisation = arg(args, 2)?;
    let nonce_at = match kind {
        "generate" => 5,
        "reseed" | "pr" => 7,
        _ => unreachable!(),
    };
    let nonce = arg(args, nonce_at)?;
    if args.len() != nonce_at + 1 {
        return Err("DRBG argument count".into());
    }
    if !drbg_lengths(hash_name, kind, args, out_len) {
        return Err("DRBG input length".into());
    }
    let mut out = vec![0u8; out_len];
    let mut drbg = rind::acvp::AcvpDrbg::new(hash_name, entropy, nonce, personalisation)
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

/// Lengths `getConfig` advertises for `hash`, in bytes. SHA-1's strength is
/// 128 bits, and each SHA-2 hash here is used at 256. The nonce is half of
/// that. Personalization and additional input may be empty. The output cap is
/// SP 800-90A's 2^19 bits for HMAC_DRBG.
fn drbg_lengths(hash: &str, kind: &str, args: &[Vec<u8>], out_len: usize) -> bool {
    let (entropy_min, nonce_min) = match hash {
        "SHA-1" => (16, 8),
        "SHA2-256" | "SHA2-384" | "SHA2-512" => (32, 16),
        _ => return false,
    };
    let within = |index: usize, min: usize| {
        args.get(index)
            .is_some_and(|bytes| (min..=MAX_DRBG).contains(&bytes.len()))
    };
    // generate: entropy, personalisation, two additional inputs, nonce.
    // reseed: those, with the reseed additional input and reseed entropy
    // inserted before the two additional inputs. Prediction resistance uses
    // the same slots; its two entropy inputs are the reseed entropies.
    let (entropies, additionals, nonce_at): (&[_], &[_], _) = match kind {
        "generate" => (&[1], &[2, 3, 4], 5),
        "reseed" => (&[1, 4], &[2, 3, 5, 6], 7),
        "pr" => (&[1, 4, 6], &[2, 3, 5], 7),
        _ => return false,
    };
    (1..=MAX_DRBG).contains(&out_len)
        && entropies.iter().all(|&index| within(index, entropy_min))
        && additionals.iter().all(|&index| within(index, 0))
        && within(nonce_at, nonce_min)
}

/// Algorithms `acvptool` knows. A name it does not is refused before any
/// vector is read. RSA key generation is absent: rind has no seeded or
/// candidate-prime FIPS 186-5 key generation, and the quest allows keeping
/// it out of the module. AES-GCM internal IVs wait on their own quest.
// The registration follows the subset understood by the pinned acvptool.
// See UPSTREAM.md, "acvptool expects older sample formats", for adaptations.
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
  {
    "algorithm": "ACVP-AES-CTR",
    "revision": "1.0",
    "direction": ["encrypt", "decrypt"],
    "keyLen": [128, 192, 256],
    "payloadLen": [{"min": 8, "max": 128, "increment": 8}],
    "incrementalCounter": true,
    "overflowCounter": true,
    "performCounterTests": true
  },
  {
    "algorithm": "ACVP-AES-GCM",
    "revision": "1.0",
    "direction": ["encrypt", "decrypt"],
    "keyLen": [128, 192, 256],
    "tagLen": [128, 120, 112, 104, 96, 64, 32],
    "ivLen": [96],
    "ivGen": "external",
    "aadLen": [{"min": 0, "max": 65536, "increment": 8}],
    "payloadLen": [{"min": 0, "max": 65536, "increment": 8}]
  },
  {
    "algorithm": "ACVP-AES-GMAC",
    "revision": "1.0",
    "direction": ["encrypt", "decrypt"],
    "keyLen": [128, 192, 256],
    "tagLen": [128, 120, 112, 104, 96, 64, 32],
    "ivLen": [96],
    "ivGen": "external",
    "aadLen": [{"min": 0, "max": 65536, "increment": 8}]
  },
  {
    "algorithm": "ACVP-AES-KW",
    "revision": "1.0",
    "direction": ["encrypt", "decrypt"],
    "kwCipher": ["cipher"],
    "keyLen": [128, 192, 256],
    "payloadLen": [{"min": 128, "max": 4096, "increment": 64}]
  },
  {
    "algorithm": "ACVP-AES-KWP",
    "revision": "1.0",
    "direction": ["encrypt", "decrypt"],
    "kwCipher": ["cipher"],
    "keyLen": [128, 192, 256],
    "payloadLen": [{"min": 8, "max": 4096, "increment": 8}]
  },
  {
    "algorithm": "HMAC-SHA-1",
    "revision": "1.0",
    "keyLen": [{"min": 8, "max": 524288, "increment": 8}],
    "macLen": [{"min": 32, "max": 160, "increment": 8}]
  },
  {
    "algorithm": "HMAC-SHA2-256",
    "revision": "1.0",
    "keyLen": [{"min": 8, "max": 524288, "increment": 8}],
    "macLen": [{"min": 32, "max": 256, "increment": 8}]
  },
  {
    "algorithm": "HMAC-SHA2-384",
    "revision": "1.0",
    "keyLen": [{"min": 8, "max": 524288, "increment": 8}],
    "macLen": [{"min": 32, "max": 384, "increment": 8}]
  },
  {
    "algorithm": "HMAC-SHA2-512",
    "revision": "1.0",
    "keyLen": [{"min": 8, "max": 524288, "increment": 8}],
    "macLen": [{"min": 32, "max": 512, "increment": 8}]
  },
  {
    "algorithm": "KDA",
    "mode": "HKDF",
    "revision": "Sp800-56Cr2",
    "fixedInfoPattern": "uPartyInfo||vPartyInfo||l",
    "encoding": ["concatenation"],
    "hmacAlg": ["SHA-1", "SHA2-256", "SHA2-384", "SHA2-512"],
    "macSaltMethods": ["default", "random"],
    "l": 2048,
    "z": [{"min": 224, "max": 65536, "increment": 8}],
    "usesHybridSharedSecret": false,
    "performMultiExpansionTests": true
  },
  {
    "algorithm": "PBKDF",
    "revision": "1.0",
    "capabilities": [
      {
        "iterationCount": [{"min": 1, "max": 10000, "increment": 1}],
        "keyLen": [{"min": 112, "max": 4096, "increment": 8}],
        "passwordLen": [{"min": 8, "max": 128, "increment": 1}],
        "saltLen": [{"min": 128, "max": 4096, "increment": 8}],
        "hmacAlg": ["SHA-1", "SHA2-256", "SHA2-384", "SHA2-512"]
      }
    ]
  },
  {
    "algorithm": "ECDSA",
    "mode": "keyGen",
    "revision": "FIPS186-5",
    "curve": ["P-256", "P-384", "P-521"],
    "secretGenerationMode": ["testing candidates"]
  },
  {"algorithm": "ECDSA", "mode": "keyVer", "revision": "FIPS186-5", "curve": ["P-256", "P-384", "P-521"]},
  {
    "algorithm": "ECDSA",
    "mode": "sigGen",
    "revision": "FIPS186-5",
    "capabilities": [{"curve": ["P-256", "P-384", "P-521"], "hashAlg": ["SHA2-256", "SHA2-384", "SHA2-512"]}],
    "componentTest": false
  },
  {
    "algorithm": "ECDSA",
    "mode": "sigVer",
    "revision": "FIPS186-5",
    "capabilities": [{"curve": ["P-256", "P-384", "P-521"], "hashAlg": ["SHA2-256", "SHA2-384", "SHA2-512"]}]
  },
  {"algorithm": "EDDSA", "mode": "keyGen", "revision": "1.0", "curve": ["ED-25519"]},
  {"algorithm": "EDDSA", "mode": "keyVer", "revision": "1.0", "curve": ["ED-25519"]},
  {"algorithm": "EDDSA", "mode": "sigGen", "revision": "1.0", "curve": ["ED-25519"], "pure": true, "preHash": false},
  {"algorithm": "EDDSA", "mode": "sigVer", "revision": "1.0", "curve": ["ED-25519"], "pure": true, "preHash": false},
  {
    "algorithm": "KAS-ECC-SSC",
    "revision": "Sp800-56Ar3",
    "scheme": {
      "ephemeralUnified": {"kasRole": ["initiator", "responder"]},
      "staticUnified": {"kasRole": ["initiator", "responder"]},
      "onePassDh": {"kasRole": ["initiator", "responder"]}
    },
    "domainParameterGenerationMethods": ["P-256", "P-384", "P-521"]
  },
  {"algorithm": "ML-KEM", "mode": "keyGen", "revision": "FIPS203", "parameterSets": ["ML-KEM-768"]},
  {
    "algorithm": "ML-KEM",
    "mode": "encapDecap",
    "revision": "FIPS203-tr1",
    "parameterSets": ["ML-KEM-768"],
    "functions": ["encapsulation", "decapsulation", "encapsulationKeyCheck", "decapsulationKeyCheck"],
    "keyFormats": ["expanded"]
  },
  {
    "algorithm": "ML-DSA",
    "mode": "keyGen",
    "revision": "FIPS204",
    "parameterSets": ["ML-DSA-44", "ML-DSA-65", "ML-DSA-87"]
  },
  {
    "algorithm": "ML-DSA",
    "mode": "sigGen",
    "revision": "FIPS204-tr1",
    "capabilities": [
      {
        "parameterSets": ["ML-DSA-44", "ML-DSA-65", "ML-DSA-87"],
        "messageLength": [{"min": 8, "max": 65536, "increment": 8}],
        "contextLength": [{"min": 0, "max": 2040, "increment": 8}]
      }
    ],
    "signatureInterfaces": ["internal", "external"],
    "externalMu": [true, false],
    "deterministic": [true, false],
    "keyFormats": ["expanded"],
    "preHash": ["pure"]
  },
  {
    "algorithm": "ML-DSA",
    "mode": "sigVer",
    "revision": "FIPS204",
    "capabilities": [
      {
        "parameterSets": ["ML-DSA-44", "ML-DSA-65", "ML-DSA-87"],
        "messageLength": [{"min": 8, "max": 65536, "increment": 8}],
        "contextLength": [{"min": 0, "max": 2040, "increment": 8}]
      }
    ],
    "signatureInterfaces": ["internal", "external"],
    "externalMu": [true, false],
    "preHash": ["pure"]
  },
  {
    "algorithm": "RSA",
    "mode": "sigGen",
    "revision": "FIPS186-5",
    "capabilities": [
      {
        "sigType": "pkcs1v1.5",
        "properties": [
          {"modulo": 2048, "hashPair": [{"hashAlg": "SHA2-256"}, {"hashAlg": "SHA2-384"}, {"hashAlg": "SHA2-512"}]},
          {"modulo": 3072, "hashPair": [{"hashAlg": "SHA2-256"}, {"hashAlg": "SHA2-384"}, {"hashAlg": "SHA2-512"}]},
          {"modulo": 4096, "hashPair": [{"hashAlg": "SHA2-256"}, {"hashAlg": "SHA2-384"}, {"hashAlg": "SHA2-512"}]}
        ]
      },
      {
        "sigType": "pss",
        "properties": [
          {
            "modulo": 2048,
            "maskFunction": ["mgf1"],
            "hashPair": [
              {"hashAlg": "SHA2-256", "saltLen": 32},
              {"hashAlg": "SHA2-384", "saltLen": 48},
              {"hashAlg": "SHA2-512", "saltLen": 64}
            ]
          },
          {
            "modulo": 3072,
            "maskFunction": ["mgf1"],
            "hashPair": [
              {"hashAlg": "SHA2-256", "saltLen": 32},
              {"hashAlg": "SHA2-384", "saltLen": 48},
              {"hashAlg": "SHA2-512", "saltLen": 64}
            ]
          },
          {
            "modulo": 4096,
            "maskFunction": ["mgf1"],
            "hashPair": [
              {"hashAlg": "SHA2-256", "saltLen": 32},
              {"hashAlg": "SHA2-384", "saltLen": 48},
              {"hashAlg": "SHA2-512", "saltLen": 64}
            ]
          }
        ]
      }
    ]
  },
  {
    "algorithm": "RSA",
    "mode": "sigVer",
    "revision": "FIPS186-5",
    "capabilities": [
      {
        "sigType": "pkcs1v1.5",
        "properties": [
          {"modulo": 2048, "hashPair": [{"hashAlg": "SHA2-256"}, {"hashAlg": "SHA2-384"}, {"hashAlg": "SHA2-512"}]},
          {"modulo": 3072, "hashPair": [{"hashAlg": "SHA2-256"}, {"hashAlg": "SHA2-384"}, {"hashAlg": "SHA2-512"}]},
          {"modulo": 4096, "hashPair": [{"hashAlg": "SHA2-256"}, {"hashAlg": "SHA2-384"}, {"hashAlg": "SHA2-512"}]}
        ]
      },
      {
        "sigType": "pss",
        "properties": [
          {
            "modulo": 2048,
            "maskFunction": ["mgf1"],
            "hashPair": [
              {"hashAlg": "SHA2-256", "saltLen": 32},
              {"hashAlg": "SHA2-384", "saltLen": 48},
              {"hashAlg": "SHA2-512", "saltLen": 64}
            ]
          },
          {
            "modulo": 3072,
            "maskFunction": ["mgf1"],
            "hashPair": [
              {"hashAlg": "SHA2-256", "saltLen": 32},
              {"hashAlg": "SHA2-384", "saltLen": 48},
              {"hashAlg": "SHA2-512", "saltLen": 64}
            ]
          },
          {
            "modulo": 4096,
            "maskFunction": ["mgf1"],
            "hashPair": [
              {"hashAlg": "SHA2-256", "saltLen": 32},
              {"hashAlg": "SHA2-384", "saltLen": 48},
              {"hashAlg": "SHA2-512", "saltLen": 64}
            ]
          }
        ]
      }
    ],
    "pubExpMode": "fixed",
    "fixedPubExp": "010001"
  },
  {
    "algorithm": "RSA",
    "mode": "signaturePrimitive",
    "revision": "2.0",
    "pubExpMode": "fixed",
    "keyFormat": ["standard"],
    "modulo": [2048, 3072, 4096],
    "fixedPubExp": "010001"
  },
  {
    "algorithm": "RSA",
    "mode": "decryptionPrimitive",
    "revision": "Sp800-56Br2",
    "pubExpMode": "random",
    "keyFormat": ["standard", "crt"],
    "modulo": [2048, 3072, 4096]
  },
  {
    "algorithm": "hmacDRBG",
    "revision": "1.0",
    "predResistanceEnabled": [true, false],
    "reseedImplemented": true,
    "capabilities": [
      {
        "mode": "SHA-1",
        "derFuncEnabled": false,
        "entropyInputLen": [{"min": 128, "max": 65536, "increment": 8}],
        "nonceLen": [{"min": 64, "max": 65536, "increment": 8}],
        "persoStringLen": [0, {"min": 128, "max": 65536, "increment": 8}],
        "additionalInputLen": [0, {"min": 128, "max": 65536, "increment": 8}],
        "returnedBitsLen": 1024
      },
      {
        "mode": "SHA2-256",
        "derFuncEnabled": false,
        "entropyInputLen": [{"min": 256, "max": 65536, "increment": 8}],
        "nonceLen": [{"min": 128, "max": 65536, "increment": 8}],
        "persoStringLen": [0, {"min": 256, "max": 65536, "increment": 8}],
        "additionalInputLen": [0, {"min": 256, "max": 65536, "increment": 8}],
        "returnedBitsLen": 1024
      },
      {
        "mode": "SHA2-384",
        "derFuncEnabled": false,
        "entropyInputLen": [{"min": 256, "max": 65536, "increment": 8}],
        "nonceLen": [{"min": 128, "max": 65536, "increment": 8}],
        "persoStringLen": [0, {"min": 256, "max": 65536, "increment": 8}],
        "additionalInputLen": [0, {"min": 256, "max": 65536, "increment": 8}],
        "returnedBitsLen": 1024
      },
      {
        "mode": "SHA2-512",
        "derFuncEnabled": false,
        "entropyInputLen": [{"min": 256, "max": 65536, "increment": 8}],
        "nonceLen": [{"min": 128, "max": 65536, "increment": 8}],
        "persoStringLen": [0, {"min": 256, "max": 65536, "increment": 8}],
        "additionalInputLen": [0, {"min": 256, "max": 65536, "increment": 8}],
        "returnedBitsLen": 1024
      }
    ]
  }
]"#;

#[cfg(test)]
mod tests {
    use super::*;

    fn handle(command: &str, args: &[Vec<u8>]) -> Result<Reply, String> {
        let reply = Wrapper::default().handle(command, args)?;
        // The handler keeps keys secret. Only this answer-checking harness
        // makes its completed output public before comparing vector bytes.
        for part in reply.slices() {
            crabgrind::memcheck::mark_memory(
                part.as_ptr().cast(),
                part.len(),
                crabgrind::memcheck::MemState::Defined,
            )
            .unwrap();
        }
        Ok(reply)
    }

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

    /// `acvptool` signs a sigGen group with one key. A second call for the
    /// same modulus, hash, and padding returns that key, not a new one.
    #[test]
    fn rsa_siggen_reuses_the_group_key() {
        let mut wrapper = Wrapper::default();
        let mut handle = |command: &str, args: &[Vec<u8>]| wrapper.handle(command, args);
        let bits = 2048u32.to_ne_bytes().to_vec();
        let message = b"acvp".to_vec();
        let first = handle(
            "RSA/sigGen/SHA2-256/pkcs1v1.5",
            &[bits.clone(), message.clone()],
        )
        .unwrap();
        let second = handle("RSA/sigGen/SHA2-256/pkcs1v1.5", &[bits, message]).unwrap();
        assert_eq!(first[0], second[0], "n");
        assert_eq!(first[1], second[1], "e");
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

    /// A large-data test hashes `content` repeated `times` times. The sample
    /// groups are multi-gigabyte, so this is a short stand-in for that call.
    #[test]
    fn sha256_ldt_repeats_the_content() {
        let once = handle("SHA2-256", &[b"abcabcabc".to_vec()]).unwrap();
        let repeated = handle(
            "SHA2-256/LDT",
            &[b"abc".to_vec(), 3u64.to_ne_bytes().to_vec()],
        )
        .unwrap();
        assert_eq!(once[0], repeated[0]);
    }

    /// A coordinate that is still too long after a leading zero is a failed
    /// verification, not a dead wrapper.
    #[test]
    fn ecdsa_sigver_rejects_a_long_coordinate() {
        let mut qx = vec![0x80];
        qx.resize(33, 0);
        let reply = handle(
            "ECDSA/sigVer",
            &[
                b"P-256".to_vec(),
                b"SHA2-256".to_vec(),
                b"message".to_vec(),
                qx,
                vec![1; 32],
                vec![1; 32],
                vec![1; 32],
            ],
        )
        .unwrap();
        assert_eq!(reply[0], [0]);
    }

    /// The counter carries out of the low 32 bits, as AES_ctr128_encrypt does.
    #[test]
    fn aes_ctr_carries_into_the_high_bits() {
        let key = vec![0x11; 16];
        let mut counter = vec![0u8; 16];
        counter[12..].fill(0xff);
        let reply = handle(
            "AES-CTR/encrypt",
            &[
                key.clone(),
                vec![0; 32],
                counter.clone(),
                1u32.to_ne_bytes().to_vec(),
            ],
        )
        .unwrap();
        let block: [u8; 16] = counter.as_slice().try_into().unwrap();
        let mut full = vec![0u8; 32];
        rind::cipher::AesCtr::new(&rind::cipher::AES_128, &key, 128)
            .unwrap()
            .apply_keystream(&block, &mut full)
            .unwrap();
        assert_eq!(reply[0], full);
        let mut low = vec![0u8; 32];
        rind::cipher::AesCtr::new(&rind::cipher::AES_128, &key, 32)
            .unwrap()
            .apply_keystream(&block, &mut low)
            .unwrap();
        assert_ne!(reply[0], low);
    }

    #[test]
    fn rsa_signature_primitive_has_fixed_argument_order() {
        let reply = handle(
            "RSA/signaturePrimitive",
            &[vec![5], vec![13], vec![5], vec![2]],
        )
        .unwrap();
        assert_eq!(reply[0], [1]);
        assert_eq!(reply[1], [6]);
    }

    #[test]
    fn work_parameters_are_bounded_before_the_operation() {
        for iterations in [0u32, 2, 1001, u32::MAX] {
            let count = iterations.to_ne_bytes().to_vec();
            assert!(handle("AES/encrypt", &[vec![0; 16], vec![0; 16], count.clone()]).is_err());
            assert!(
                handle(
                    "AES-CBC/encrypt",
                    &[vec![0; 16], vec![0; 16], vec![0; 16], count]
                )
                .is_err()
            );
        }
        assert!(
            handle(
                "AES/encrypt",
                &[vec![0; 16], vec![0; 32], 1000u32.to_ne_bytes().to_vec()]
            )
            .is_err()
        );
        assert!(
            handle(
                "AES-CBC/encrypt",
                &[
                    vec![0; 16],
                    vec![0; 32],
                    vec![0; 16],
                    1000u32.to_ne_bytes().to_vec()
                ]
            )
            .is_err()
        );
        for (iterations, bits) in [
            (0u32, 128u32),
            (10_001, 128),
            (u32::MAX, 128),
            (1, 0),
            (1, 113),
            (1, 4104),
            (1, !7u32),
        ] {
            assert!(
                handle(
                    "PBKDF",
                    &[
                        b"password".to_vec(),
                        vec![0; 16],
                        iterations.to_ne_bytes().to_vec(),
                        b"SHA2-256".to_vec(),
                        bits.to_ne_bytes().to_vec()
                    ]
                )
                .is_err()
            );
        }
        assert!(
            handle(
                "SHA2-256/LDT",
                &[vec![0; 3], (1u64 << 32).to_ne_bytes().to_vec()]
            )
            .is_err()
        );
    }

    #[test]
    fn mlkem_keygen_requires_two_seed_halves() {
        for (d, z) in [(0, 64), (31, 33), (33, 31), (64, 0)] {
            assert!(
                handle("ML-KEM/ML-KEM-768/keyGen", &[vec![0x11; d], vec![0x22; z]]).is_err(),
                "d={d}, z={z}"
            );
        }
        assert!(
            handle(
                "ML-KEM/ML-KEM-768/keyGen",
                &[vec![0x11; 32], vec![0x22; 32]]
            )
            .is_ok()
        );
    }

    #[test]
    fn der_length_preserves_a_large_public_integer() {
        let integer = vec![0x7f; 1 << 16];
        let encoded = der_int(&integer);
        assert_eq!(&encoded[..5], &[0x02, 0x83, 0x01, 0x00, 0x00]);
        assert_eq!(&encoded[5..], integer);
    }

    #[test]
    fn hkdf_expand_reaches_the_last_counter_block() {
        for (hash, bytes) in [
            ("SHA-1", 20),
            ("SHA2-256", 32),
            ("SHA2-384", 48),
            ("SHA2-512", 64),
        ] {
            let key = b"input key material".to_vec();
            let salt = b"salt".to_vec();
            let info = b"info".to_vec();
            let prk = handle(
                &format!("HKDF/{hash}/extract"),
                &[key.clone(), salt.clone()],
            )
            .unwrap();
            for len in [0u32, 1, 254 * bytes, 254 * bytes + 1, 255 * bytes] {
                let length = len.to_ne_bytes().to_vec();
                let whole = handle(
                    &format!("KDA/HKDF/{hash}"),
                    &[key.clone(), salt.clone(), info.clone(), length.clone()],
                )
                .unwrap();
                let expanded = handle(
                    &format!("HKDF/{hash}/expand"),
                    &[length, prk[0].to_vec(), info.clone()],
                )
                .unwrap();
                assert_eq!(expanded[0], whole[0], "{hash}: {len}");
            }
            let length = (255 * bytes + 1u32).to_ne_bytes().to_vec();
            assert!(
                handle(
                    &format!("HKDF/{hash}/expand"),
                    &[length.clone(), prk[0].to_vec(), info.clone()]
                )
                .is_err()
            );
            assert!(handle(&format!("KDA/HKDF/{hash}"), &[key, salt, info, length]).is_err());
        }
    }

    #[test]
    fn drbg_config_names_lengths_and_refuses_a_short_nonce() {
        let reply = handle("getConfig", &[]).unwrap();
        let config: serde_json::Value = serde_json::from_slice(&reply[0]).unwrap();
        let drbg = config
            .as_array()
            .unwrap()
            .iter()
            .find(|item| item["algorithm"] == "hmacDRBG")
            .unwrap();
        assert_eq!(drbg["reseedImplemented"], true);
        let modes: Vec<_> = drbg["capabilities"]
            .as_array()
            .unwrap()
            .iter()
            .map(|item| item["mode"].as_str().unwrap())
            .collect();
        assert_eq!(modes, ["SHA-1", "SHA2-256", "SHA2-384", "SHA2-512"]);
        let err = handle(
            "hmacDRBG/SHA2-256",
            &[
                16u32.to_ne_bytes().to_vec(),
                vec![0x5a; 32],
                Vec::new(),
                Vec::new(),
                Vec::new(),
                vec![0; 8],
            ],
        );
        assert!(err.is_err());
    }
}
