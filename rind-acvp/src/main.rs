// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! `rind-acvp`: answers ACVP test sets for rind's FIPS module, as the module
//! wrapper of aws-lc's `acvptool` (`util/fipstools/acvp`).
//!
//! `acvptool` sends each request on stdin, and reads each reply on stdout,
//! in one framing: a little-endian `u32` count, that many `u32` lengths, then
//! the byte strings. A request's first string names the command, as
//! `acvptool`'s `subprocess` package spells it; the rest are its arguments.
//! A failed or unknown command ends the process with an error, which
//! `acvptool` reports.
//!
//! Every answer comes from the module, through `rind-fips`'s API, but for
//! the deterministic forms of the randomized services, which only the
//! module's ACVP build offers (`rind_fips::acvp`).

use std::collections::HashMap;
use std::error::Error;
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::num::NonZeroU32;
use std::process::ExitCode;

use rind_fips::acvp::{self, MlDsaMessage};
use rind_fips::aead::{self, RandomizedNonceKey, gcm};
use rind_fips::agreement;
use rind_fips::cipher::{self, AesCbcDecryptingKey, AesCbcEncryptingKey, AesCtr, CbcIv};
use rind_fips::digest;
use rind_fips::hkdf;
use rind_fips::hmac;
use rind_fips::kem;
use rind_fips::key_wrap::{self, AesKek, Mode};
use rind_fips::ml_dsa::{MlDsa44, MlDsa65, MlDsa87, ParameterSet};
use rind_fips::pbkdf2;
use rind_fips::rsa::{KeySize, PublicKeyComponents};
use rind_fips::{ecdsa, ed25519, rsa};

/// The capabilities rind's module registers, which `getConfig` returns.
const CONFIG: &str = include_str!("config.json");

/// The most arguments a request takes: RSA's CRT decryption primitive, the
/// most `acvptool` sends, takes nine.
const MAX_ARGS: usize = 16;

/// The most bytes a request carries. `acvptool`'s largest are 64 KiB
/// messages; a large-data hash test sends its pattern and a count.
const MAX_REQUEST_LEN: usize = 16 << 20;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

/// A reply: the byte strings it carries.
type Reply = Vec<Vec<u8>>;

fn main() -> ExitCode {
    let mut input = BufReader::new(io::stdin().lock());
    let mut output = BufWriter::new(io::stdout().lock());
    let mut wrapper = Wrapper::default();
    loop {
        let request = match read_request(&mut input) {
            Ok(Some(request)) => request,
            Ok(None) => return ExitCode::SUCCESS,
            Err(error) => {
                eprintln!("rind-acvp: cannot read a request: {error}");
                return ExitCode::FAILURE;
            }
        };
        let (command, args) = request.split_first().expect("a request names its command");
        let command = String::from_utf8_lossy(command);
        let reply = wrapper.handle(&command, args).and_then(|reply| {
            write_reply(&mut output, &reply)?;
            Ok(output.flush()?)
        });
        if let Err(error) = reply {
            eprintln!("rind-acvp: {command}: {error}");
            return ExitCode::FAILURE;
        }
    }
}

/// The next request, or `None` at the end of the input.
fn read_request(input: &mut impl Read) -> Result<Option<Vec<Vec<u8>>>> {
    let mut word = [0u8; 4];
    // The input ends cleanly only before a request's first byte; a request
    // cut short anywhere after it is an error.
    loop {
        match input.read(&mut word[..1]) {
            Ok(0) => return Ok(None),
            Ok(_) => break,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return Err(error.into()),
        }
    }
    input.read_exact(&mut word[1..])?;
    let count = u32::from_le_bytes(word) as usize;
    if count == 0 || count > MAX_ARGS + 1 {
        return Err(format!("a request of {count} strings").into());
    }
    let mut lens = Vec::with_capacity(count);
    let mut total = 0usize;
    for _ in 0..count {
        input.read_exact(&mut word)?;
        let len = u32::from_le_bytes(word) as usize;
        total = total.saturating_add(len);
        lens.push(len);
    }
    if total > MAX_REQUEST_LEN {
        return Err(format!("a request of {total} bytes").into());
    }
    let mut request = Vec::with_capacity(count);
    for len in lens {
        let mut arg = vec![0; len];
        input.read_exact(&mut arg)?;
        request.push(arg);
    }
    Ok(Some(request))
}

fn write_reply(output: &mut impl Write, reply: &[Vec<u8>]) -> io::Result<()> {
    output.write_all(&(reply.len() as u32).to_le_bytes())?;
    for arg in reply {
        output.write_all(&(arg.len() as u32).to_le_bytes())?;
    }
    for arg in reply {
        output.write_all(arg)?;
    }
    Ok(())
}

/// What one request leaves for later ones: the keys `acvptool` asks to sign
/// with after it asked for them to be generated.
#[derive(Default)]
struct Wrapper {
    /// ECDSA keys from `ECDSA/keyGen`, by curve and private scalar, which
    /// `ECDSA/sigGen` names.
    ecdsa: HashMap<(String, Vec<u8>), ecdsa::KeyPair>,
    /// The RSA key of each modulus size `RSA/sigGen` signs with, which
    /// every test of a group must share.
    rsa: HashMap<u32, rsa::KeyPair>,
}

impl Wrapper {
    fn handle(&mut self, command: &str, args: &[Vec<u8>]) -> Result<Reply> {
        // SHA-512/256's name has a slash of its own.
        let command = command.replace("SHA2-512/256", SHA512_256);
        let parts: Vec<&str> = command.split('/').collect();
        match parts.as_slice() {
            ["getConfig"] => Ok(vec![CONFIG.as_bytes().to_vec()]),
            [name] if hash(name).is_ok() => {
                let [message] = take(args)?;
                Ok(vec![digest::digest(hash(name)?, message).as_ref().to_vec()])
            }
            [name, "MCT"] => hash_mct(hash(name)?, name.starts_with("SHA3"), args),
            [name, "LDT"] => hash_ldt(hash(name)?, args),
            [name] if name.starts_with("HMAC-") => {
                let [message, key] = take(args)?;
                let key = hmac::Key::new(hmac_algorithm(&name[5..])?, key);
                Ok(vec![hmac::sign(&key, message).as_ref().to_vec()])
            }
            ["AES", "encrypt"] => aes_ecb(args),
            ["AES-CBC", direction] => aes_cbc(encrypting(direction)?, args),
            ["AES-CTR", direction] => {
                encrypting(direction)?;
                aes_ctr(args)
            }
            ["AES-GCM", "seal"] => aes_gcm_seal(args),
            ["AES-GCM", "open"] => aes_gcm_open(args),
            ["AES-KW", "seal"] => aes_kw_seal(Mode::Kw, args),
            ["AES-KW", "open"] => aes_kw_open(Mode::Kw, args),
            ["AES-KWP", "seal"] => aes_kw_seal(Mode::Kwp, args),
            ["AES-KWP", "open"] => aes_kw_open(Mode::Kwp, args),
            ["KDA", "HKDF", name] => hkdf_kda(name, args),
            ["PBKDF"] => pbkdf(args),
            ["hmacDRBG-pr", "SHA2-512"] => drbg(args),
            ["ECDSA", "keyGen"] => self.ecdsa_key_gen(args),
            ["ECDSA", "keyVer"] => ecdsa_key_ver(args),
            ["ECDSA", "sigGen"] => self.ecdsa_sig_gen(args),
            ["ECDSA", "sigVer"] => ecdsa_sig_ver(args),
            ["EDDSA", "ED-25519", operation] => ed25519(operation, args),
            ["RSA", "keyGen"] => rsa_key_gen(args),
            ["RSA", "sigGen", hash, scheme] => self.rsa_sig_gen(hash, scheme, args),
            ["RSA", "sigVer", hash, scheme] => rsa_sig_ver(hash, scheme, args),
            ["ECDH", curve] => ecdh(curve, args),
            ["ML-KEM", set, operation] => ml_kem(set, operation, args),
            ["ML-DSA", "ML-DSA-44", operation] => ml_dsa::<MlDsa44>(operation, args),
            ["ML-DSA", "ML-DSA-65", operation] => ml_dsa::<MlDsa65>(operation, args),
            ["ML-DSA", "ML-DSA-87", operation] => ml_dsa::<MlDsa87>(operation, args),
            _ => Err("not a command rind's module registers".into()),
        }
    }

    /// `ECDSA/keyGen`: curve, to the private scalar and the public point's
    /// coordinates.
    fn ecdsa_key_gen(&mut self, args: &[Vec<u8>]) -> Result<Reply> {
        let [name] = take(args)?;
        let curve = Curve::named(name)?;
        let key = ecdsa::KeyPair::generate(curve.signing)?;
        let d = key.to_scalar().as_ref().to_vec();
        let (x, y) = curve.coordinates(key.public_key().as_ref())?;
        self.ecdsa.insert((curve.name.to_owned(), d.clone()), key);
        Ok(vec![d, x, y])
    }

    /// `ECDSA/sigGen`: curve, a private scalar from `ECDSA/keyGen`, hash,
    /// and message, to the signature's `r` and `s`.
    fn ecdsa_sig_gen(&mut self, args: &[Vec<u8>]) -> Result<Reply> {
        let [name, d, hash_name, message] = take(args)?;
        let curve = Curve::named(name)?;
        if utf8(hash_name)? != curve.hash {
            return Err("ECDSA signs with only the curve's own hash".into());
        }
        let key = self
            .ecdsa
            .get(&(curve.name.to_owned(), d.to_vec()))
            .ok_or("a private key ECDSA/keyGen did not generate")?;
        let signature = key.sign(message)?;
        let (r, s) = signature.as_ref().split_at(curve.len);
        Ok(vec![r.to_vec(), s.to_vec()])
    }

    /// `RSA/sigGen/<hash>/<scheme>`: modulus size and message, to the
    /// modulus, the public exponent, and the signature, under one key for
    /// each modulus size.
    fn rsa_sig_gen(&mut self, hash: &str, scheme: &str, args: &[Vec<u8>]) -> Result<Reply> {
        let [bits, message] = take(args)?;
        let algorithm = rsa_signing(hash, scheme)?;
        let bits = u32_le(bits)?;
        let key = match self.rsa.entry(bits) {
            std::collections::hash_map::Entry::Occupied(entry) => entry.into_mut(),
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(rsa::KeyPair::generate(rsa_size(bits)?)?)
            }
        };
        let signature = key.sign(algorithm, message)?;
        let pkcs8 = key.to_pkcs8();
        let private = RsaPrivateKey::parse(pkcs8.as_ref())?;
        Ok(vec![
            private.n.to_vec(),
            private.e.to_vec(),
            signature.as_ref().to_vec(),
        ])
    }
}

/// `args` as exactly `N` byte strings.
fn take<const N: usize>(args: &[Vec<u8>]) -> Result<[&[u8]; N]> {
    let args: Vec<&[u8]> = args.iter().map(Vec::as_slice).collect();
    args.try_into()
        .map_err(|args: Vec<&[u8]>| format!("{} arguments, not {N}", args.len()).into())
}

fn utf8(bytes: &[u8]) -> Result<&str> {
    Ok(core::str::from_utf8(bytes)?)
}

/// A little-endian `u32`, as `acvptool` sends counts and lengths.
fn u32_le(bytes: &[u8]) -> Result<u32> {
    Ok(u32::from_le_bytes(bytes.try_into()?))
}

/// A boolean reply: one byte, 1 for true.
fn flag(value: bool) -> Vec<u8> {
    vec![u8::from(value)]
}

/// `bytes` as a big-endian integer of exactly `len` bytes, or `None` if it
/// does not fit.
fn fixed(bytes: &[u8], len: usize) -> Option<Vec<u8>> {
    let start = bytes.iter().position(|&b| b != 0).unwrap_or(bytes.len());
    let bytes = &bytes[start..];
    let pad = len.checked_sub(bytes.len())?;
    let mut out = vec![0; pad];
    out.extend_from_slice(bytes);
    Some(out)
}

/// `bytes` without leading zero bytes.
fn minimal(bytes: &[u8]) -> &[u8] {
    let start = bytes.iter().position(|&b| b != 0).unwrap_or(bytes.len());
    &bytes[start..]
}

// Hashes and HMAC.

/// `SHA2-512/256` in a command, which splits at its other slashes.
const SHA512_256: &str = "SHA2-512_256";

fn hash(name: &str) -> Result<&'static digest::Algorithm> {
    Ok(match name {
        "SHA2-256" => &digest::SHA256,
        "SHA2-384" => &digest::SHA384,
        "SHA2-512" => &digest::SHA512,
        SHA512_256 => &digest::SHA512_256,
        "SHA3-256" => &digest::SHA3_256,
        "SHA3-384" => &digest::SHA3_384,
        "SHA3-512" => &digest::SHA3_512,
        _ => return Err(format!("no hash {name}").into()),
    })
}

fn hmac_algorithm(name: &str) -> Result<&'static hmac::Algorithm> {
    Ok(match name {
        "SHA-1" => &hmac::legacy::HMAC_SHA1,
        "SHA2-256" => &hmac::HMAC_SHA256,
        "SHA2-384" => &hmac::HMAC_SHA384,
        "SHA2-512" => &hmac::HMAC_SHA512,
        _ => return Err(format!("no HMAC over {name}").into()),
    })
}

/// `<hash>/MCT`: one outer iteration of the hash's Monte Carlo test, 1000
/// hashes from `seed`: SHA-2's standard test hashes the last three digests
/// together, and SHA-3's hashes the last alone.
fn hash_mct(algorithm: &'static digest::Algorithm, sha3: bool, args: &[Vec<u8>]) -> Result<Reply> {
    let [seed] = take(args)?;
    if seed.len() != algorithm.output_len() {
        return Err("a seed not the digest's length".into());
    }
    if sha3 {
        let mut md = seed.to_vec();
        for _ in 0..1000 {
            md = digest::digest(algorithm, &md).as_ref().to_vec();
        }
        return Ok(vec![md]);
    }
    let mut mds = [seed.to_vec(), seed.to_vec(), seed.to_vec()];
    for _ in 0..1000 {
        let mut ctx = digest::Context::new(algorithm);
        for md in &mds {
            ctx.update(md);
        }
        let md = ctx.finish().as_ref().to_vec();
        mds = [mds[1].clone(), mds[2].clone(), md];
    }
    let [.., md] = mds;
    Ok(vec![md])
}

/// `<hash>/LDT`: the hash of `content` repeated a native-endian `u64` of
/// times, gigabytes in all, streamed in large updates.
fn hash_ldt(algorithm: &'static digest::Algorithm, args: &[Vec<u8>]) -> Result<Reply> {
    let [content, times] = take(args)?;
    let times = u64::from_ne_bytes(times.try_into()?);
    if content.is_empty() {
        return Err("an empty large-data pattern".into());
    }
    // The registration's largest test is 8 GiB.
    if times
        .checked_mul(content.len() as u64)
        .is_none_or(|len| len > 8 << 30)
    {
        return Err("a large-data message over 8 GiB".into());
    }
    let per_chunk = ((1 << 20) / content.len()).max(1);
    let chunk = content.repeat(per_chunk);
    let mut ctx = digest::Context::new(algorithm);
    for _ in 0..times / per_chunk as u64 {
        ctx.update(&chunk);
    }
    for _ in 0..times % per_chunk as u64 {
        ctx.update(content);
    }
    Ok(vec![ctx.finish().as_ref().to_vec()])
}

// AES.

fn aes(key: &[u8]) -> Result<&'static cipher::Algorithm> {
    Ok(match key.len() {
        16 => &cipher::AES_128,
        24 => &cipher::AES_192,
        32 => &cipher::AES_256,
        len => return Err(format!("an AES key of {len} bytes").into()),
    })
}

fn encrypting(direction: &str) -> Result<bool> {
    match direction {
        "encrypt" => Ok(true),
        "decrypt" => Ok(false),
        _ => Err(format!("no direction {direction}").into()),
    }
}

/// An AES request's iteration count: 1 for a known-answer test, or the
/// Monte Carlo test's 1000, the only counts `acvptool` sends for AES.
fn aes_iterations(bytes: &[u8]) -> Result<u32> {
    match u32_le(bytes)? {
        iterations @ (1 | 1000) => Ok(iterations),
        iterations => Err(format!("{iterations} AES iterations, not 1 or 1000").into()),
    }
}

/// `AES/encrypt`: key, blocks, and iterations, to the blocks encrypted that
/// many times, and the blocks before the last, as aws-lc's wrapper runs the
/// Monte Carlo test's inner loop. The module's block cipher only encrypts.
fn aes_ecb(args: &[Vec<u8>]) -> Result<Reply> {
    let [key, input, iterations] = take(args)?;
    let aes = cipher::Aes::new(aes(key)?, key)?;
    if input.len() % 16 != 0 {
        return Err("a partial block".into());
    }
    let mut result = input.to_vec();
    let mut prev = Vec::new();
    let iterations = aes_iterations(iterations)?;
    for j in 0..iterations {
        if j + 1 == iterations {
            prev = result.clone();
        }
        for block in result.as_chunks_mut::<16>().0 {
            aes.encrypt_block(block);
        }
    }
    Ok(vec![result, prev])
}

/// `AES-CBC/encrypt` and `AES-CBC/decrypt`: key, blocks, IV, and
/// iterations, to the result and the result before it, chaining each
/// iteration into the next as aws-lc's wrapper runs the Monte Carlo test's
/// inner loop.
fn aes_cbc(encrypt: bool, args: &[Vec<u8>]) -> Result<Reply> {
    let [key, input, iv, iterations] = take(args)?;
    let algorithm = aes(key)?;
    if input.is_empty() || input.len() % 16 != 0 {
        return Err("not whole blocks".into());
    }
    let mut iv: [u8; 16] = iv.try_into()?;
    let encrypting = AesCbcEncryptingKey::new(algorithm, key)?;
    let decrypting = AesCbcDecryptingKey::new(algorithm, key)?;
    let mut input = input.to_vec();
    let mut result = vec![0; input.len()];
    let mut prev_result = Vec::new();
    let mut prev_input = Vec::new();
    for j in 0..aes_iterations(iterations)? {
        prev_result = result.clone();
        if j > 0 {
            let chained = if encrypt { &result } else { &prev_input };
            iv.copy_from_slice(&chained[..16]);
        }
        let mut out = input.clone();
        if encrypt {
            encrypting.encrypt_blocks(CbcIv::assume_unpredictable(iv), &mut out)?;
        } else {
            decrypting.decrypt_blocks(&iv, &mut out)?;
            prev_input = input.clone();
        }
        result = out;
        input = if j == 0 {
            iv.to_vec()
        } else {
            prev_result.clone()
        };
    }
    Ok(vec![result, prev_result])
}

/// `AES-CTR/encrypt` and `AES-CTR/decrypt`: key, input, initial counter
/// block, and one iteration, to the output, with a 128-bit counter.
fn aes_ctr(args: &[Vec<u8>]) -> Result<Reply> {
    let [key, input, iv, _] = take(args)?;
    let ctr = AesCtr::new(aes(key)?, key, 128)?;
    let mut out = input.to_vec();
    ctr.apply_keystream(iv.try_into()?, &mut out)?;
    Ok(vec![out])
}

/// `AES-GCM/seal`: tag length, key, plaintext, an empty nonce, and AAD, to
/// the ciphertext, tag, and the 12-byte IV the module generated, in one
/// string. The module seals only under IVs it generates (IG C.H), with
/// full tags, so a nonce `acvptool` supplies or a shorter tag is an error.
fn aes_gcm_seal(args: &[Vec<u8>]) -> Result<Reply> {
    let [tag_len, key, plaintext, nonce, aad] = take(args)?;
    if u32_le(tag_len)? != 16 {
        return Err("a sealing tag of other than 16 bytes".into());
    }
    if !nonce.is_empty() {
        return Err("a sealing nonce: the module generates the IV".into());
    }
    let algorithm = match key.len() {
        16 => &aead::AES_128_GCM,
        24 => &aead::AES_192_GCM,
        32 => &aead::AES_256_GCM,
        len => return Err(format!("an AES key of {len} bytes").into()),
    };
    let key = RandomizedNonceKey::new(algorithm, key)?;
    let mut out = plaintext.to_vec();
    let (iv, tag) = key.seal_in_place_separate_tag(aad, &mut out)?;
    out.extend_from_slice(tag.as_ref());
    out.extend_from_slice(iv.as_ref());
    Ok(vec![out])
}

/// `AES-GCM/open`: tag length, key, ciphertext and tag, IV, and AAD, to
/// whether it opened, and the plaintext. The module only opens with an IV
/// it is given: it seals with IVs it generates.
fn aes_gcm_open(args: &[Vec<u8>]) -> Result<Reply> {
    let [tag_len, key, sealed, iv, aad] = take(args)?;
    let algorithm = aes(key)?;
    let tag_len = match u32_le(tag_len)? {
        16 => gcm::TagLength::Full,
        15 => gcm::TagLength::Truncated120,
        14 => gcm::TagLength::Truncated112,
        13 => gcm::TagLength::Truncated104,
        12 => gcm::TagLength::Truncated96,
        8 => gcm::TagLength::Truncated64,
        4 => gcm::TagLength::Truncated32,
        len => return Err(format!("a tag of {len} bytes").into()),
    };
    let key = gcm::Key::new(algorithm, key, tag_len)?;
    let mut in_out = sealed.to_vec();
    Ok(
        match key.open_in_place(gcm::Iv::assume_unique_for_key(iv)?, aad, &mut in_out) {
            Ok(plaintext) => vec![flag(true), plaintext.to_vec()],
            Err(_) => vec![flag(false), Vec::new()],
        },
    )
}

fn kek(key: &[u8]) -> Result<AesKek> {
    let algorithm = match key.len() {
        16 => &key_wrap::AES_128,
        24 => &key_wrap::AES_192,
        32 => &key_wrap::AES_256,
        len => return Err(format!("an AES key of {len} bytes").into()),
    };
    Ok(AesKek::new(algorithm, key)?)
}

/// `AES-KW/seal` and `AES-KWP/seal`: an unused tag length, key, key data,
/// and unused IV and AAD, to the wrapped key.
fn aes_kw_seal(mode: Mode, args: &[Vec<u8>]) -> Result<Reply> {
    let [_, key, input, _, _] = take(args)?;
    let mut out = vec![0; input.len().div_ceil(8) * 8 + 8];
    kek(key)?.wrap_key(mode, input, &mut out)?;
    Ok(vec![out])
}

/// `AES-KW/open` and `AES-KWP/open`: as for sealing, to whether it
/// unwrapped, and the key data.
fn aes_kw_open(mode: Mode, args: &[Vec<u8>]) -> Result<Reply> {
    let [_, key, wrapped, _, _] = take(args)?;
    let kek = kek(key)?;
    let mut out = vec![0; wrapped.len().saturating_sub(8)];
    Ok(match kek.unwrap_key(mode, wrapped, &mut out) {
        Ok(key) => vec![flag(true), key.to_vec()],
        Err(_) => vec![flag(false), Vec::new()],
    })
}

// Key derivation.

/// `KDA/HKDF/<hash>`: shared secret, salt, fixed info, and output length in
/// bytes, to the derived key: SP 800-56C's one-step extract and expand.
fn hkdf_kda(name: &str, args: &[Vec<u8>]) -> Result<Reply> {
    let [z, salt, info, len] = take(args)?;
    let (algorithm, hash_len) = match name {
        "SHA2-256" => (&hkdf::HKDF_SHA256, 32),
        "SHA2-384" => (&hkdf::HKDF_SHA384, 48),
        "SHA2-512" => (&hkdf::HKDF_SHA512, 64),
        _ => return Err(format!("no HKDF over {name}").into()),
    };
    // HKDF expands to at most 255 hash outputs: refuse more before
    // allocating for them.
    let len = u32_le(len)? as usize;
    if len > 255 * hash_len {
        return Err(format!("{len} bytes of HKDF over {name}").into());
    }
    let prk = hkdf::Salt::new(algorithm, salt).extract(z)?;
    let mut out = vec![0; len];
    prk.fill(&[info], &mut out)?;
    Ok(vec![out])
}

/// `PBKDF`: password, salt, iterations, HMAC's hash, and key length in
/// bits, to the derived key.
fn pbkdf(args: &[Vec<u8>]) -> Result<Reply> {
    let [password, salt, iterations, name, bits] = take(args)?;
    let algorithm = match utf8(name)? {
        "SHA-1" => &pbkdf2::legacy::PBKDF2_HMAC_SHA1,
        "SHA2-256" => &pbkdf2::PBKDF2_HMAC_SHA256,
        "SHA2-384" => &pbkdf2::PBKDF2_HMAC_SHA384,
        "SHA2-512" => &pbkdf2::PBKDF2_HMAC_SHA512,
        name => return Err(format!("no PBKDF2 over {name}").into()),
    };
    // The registration's bounds: 1000 to 10000 iterations, and a key of
    // 112 to 4096 bits in whole bytes.
    let iterations = u32_le(iterations)?;
    let bits = u32_le(bits)?;
    if !(1000..=10000).contains(&iterations) || !(112..=4096).contains(&bits) || bits % 8 != 0 {
        return Err(format!("PBKDF of {iterations} iterations to {bits} bits").into());
    }
    let iterations = NonZeroU32::new(iterations).ok_or("no iterations")?;
    let mut out = vec![0; bits as usize / 8];
    pbkdf2::Secret::new(algorithm, password).derive(iterations, salt, &mut out)?;
    Ok(vec![out])
}

/// `hmacDRBG-pr/SHA2-512`: output length, entropy, personalization, each
/// generate's additional input and entropy, and nonce, to the second
/// generate's output.
fn drbg(args: &[Vec<u8>]) -> Result<Reply> {
    let [
        len,
        entropy,
        personalization,
        ad1,
        entropy1,
        ad2,
        entropy2,
        nonce,
    ] = take(args)?;
    // SP 800-90A's HMAC_DRBG returns at most 2^19 bits a request.
    let len = u32::from_ne_bytes(len.try_into()?) as usize;
    if len > 1 << 16 {
        return Err("a DRBG request over 2^19 bits".into());
    }
    let mut out = vec![0; len];
    acvp::drbg(
        entropy,
        nonce,
        personalization,
        [
            acvp::Generate {
                additional_input: ad1,
                entropy: entropy1,
            },
            acvp::Generate {
                additional_input: ad2,
                entropy: entropy2,
            },
        ],
        &mut out,
    )?;
    Ok(vec![out])
}

// Elliptic curves.

/// A NIST curve, and the algorithms the module offers on it.
struct Curve {
    name: &'static str,
    /// A field element's and a scalar's length.
    len: usize,
    /// The hash the module signs with on this curve.
    hash: &'static str,
    signing: &'static ecdsa::SigningAlgorithm,
    ecdh: &'static agreement::Algorithm,
}

impl Curve {
    fn named(name: &[u8]) -> Result<Self> {
        Ok(match utf8(name)? {
            "P-256" => Self {
                name: "P-256",
                len: 32,
                hash: "SHA2-256",
                signing: &ecdsa::sign::P256_SHA256_FIXED,
                ecdh: &agreement::ECDH_P256,
            },
            "P-384" => Self {
                name: "P-384",
                len: 48,
                hash: "SHA2-384",
                signing: &ecdsa::sign::P384_SHA384_FIXED,
                ecdh: &agreement::ECDH_P384,
            },
            "P-521" => Self {
                name: "P-521",
                len: 66,
                hash: "SHA2-512",
                signing: &ecdsa::sign::P521_SHA512_FIXED,
                ecdh: &agreement::ECDH_P521,
            },
            name => return Err(format!("no curve {name}").into()),
        })
    }

    /// The ASN.1 verification algorithm with hash `name`.
    fn verification(&self, hash: &[u8]) -> Result<&'static ecdsa::VerificationAlgorithm> {
        Ok(match (self.name, utf8(hash)?) {
            ("P-256", "SHA2-256") => &ecdsa::verify::P256_SHA256_ASN1,
            ("P-256", "SHA2-384") => &ecdsa::verify::P256_SHA384_ASN1,
            ("P-256", "SHA2-512") => &ecdsa::verify::P256_SHA512_ASN1,
            ("P-384", "SHA2-256") => &ecdsa::verify::P384_SHA256_ASN1,
            ("P-384", "SHA2-384") => &ecdsa::verify::P384_SHA384_ASN1,
            ("P-384", "SHA2-512") => &ecdsa::verify::P384_SHA512_ASN1,
            ("P-521", "SHA2-256") => &ecdsa::verify::P521_SHA256_ASN1,
            ("P-521", "SHA2-384") => &ecdsa::verify::P521_SHA384_ASN1,
            ("P-521", "SHA2-512") => &ecdsa::verify::P521_SHA512_ASN1,
            (curve, hash) => return Err(format!("no ECDSA on {curve} with {hash}").into()),
        })
    }

    /// The uncompressed point `(x, y)`, or `None` if a coordinate does not
    /// fit a field element.
    fn point(&self, x: &[u8], y: &[u8]) -> Option<Vec<u8>> {
        let mut point = vec![4];
        point.extend(fixed(x, self.len)?);
        point.extend(fixed(y, self.len)?);
        Some(point)
    }

    /// The coordinates of uncompressed point `point`.
    fn coordinates(&self, point: &[u8]) -> Result<(Vec<u8>, Vec<u8>)> {
        match point.split_first() {
            Some((4, xy)) if xy.len() == 2 * self.len => {
                let (x, y) = xy.split_at(self.len);
                Ok((x.to_vec(), y.to_vec()))
            }
            _ => Err("a point not uncompressed".into()),
        }
    }
}

/// `ECDSA/keyVer`: curve and a public point's coordinates, to whether the
/// module takes it as a public key.
fn ecdsa_key_ver(args: &[Vec<u8>]) -> Result<Reply> {
    let [name, x, y] = take(args)?;
    let curve = Curve::named(name)?;
    let algorithm = curve.verification(curve.hash.as_bytes())?;
    let valid = curve
        .point(x, y)
        .is_some_and(|point| ecdsa::PublicKey::new(algorithm, &point).is_ok());
    Ok(vec![flag(valid)])
}

/// `ECDSA/sigVer`: curve, hash, message, public point, `r`, and `s`, to
/// whether the signature verifies.
fn ecdsa_sig_ver(args: &[Vec<u8>]) -> Result<Reply> {
    let [name, hash, message, x, y, r, s] = take(args)?;
    let curve = Curve::named(name)?;
    let algorithm = curve.verification(hash)?;
    let valid = curve.point(x, y).is_some_and(|point| {
        ecdsa::PublicKey::new(algorithm, &point)
            .and_then(|key| key.verify(message, &der_signature(r, s)))
            .is_ok()
    });
    Ok(vec![flag(valid)])
}

/// The DER `Ecdsa-Sig-Value` of `r` and `s`.
fn der_signature(r: &[u8], s: &[u8]) -> Vec<u8> {
    fn integer(value: &[u8]) -> Vec<u8> {
        let value = minimal(value);
        let mut content = Vec::new();
        if value.first().is_none_or(|&b| b & 0x80 != 0) {
            content.push(0);
        }
        content.extend_from_slice(value);
        let mut out = vec![2];
        out.extend(der_len(content.len()));
        out.extend(content);
        out
    }
    let content = [integer(r), integer(s)].concat();
    let mut out = vec![0x30];
    out.extend(der_len(content.len()));
    out.extend(content);
    out
}

fn der_len(len: usize) -> Vec<u8> {
    if len < 0x80 {
        return vec![len as u8];
    }
    let bytes = len.to_be_bytes();
    let bytes = minimal(&bytes);
    let mut out = vec![0x80 | bytes.len() as u8];
    out.extend_from_slice(bytes);
    out
}

/// `ECDH/<curve>`: the peer's public point, and a private scalar or none to
/// generate one, to this side's public point and the shared secret.
fn ecdh(name: &str, args: &[Vec<u8>]) -> Result<Reply> {
    let [peer_x, peer_y, scalar] = take(args)?;
    let curve = Curve::named(name.as_bytes())?;
    let key = if scalar.is_empty() {
        agreement::PrivateKey::generate(curve.ecdh)?
    } else {
        let scalar = fixed(scalar, curve.len).ok_or("a scalar longer than the order")?;
        agreement::PrivateKey::from_scalar(curve.ecdh, &scalar)?
    };
    let (x, y) = curve.coordinates(key.public_key().as_ref())?;
    let peer = curve
        .point(peer_x, peer_y)
        .ok_or("a peer coordinate longer than a field element")?;
    let z = key.agree(&peer)?;
    Ok(vec![x, y, z.as_ref().to_vec()])
}

/// `EDDSA/ED-25519/<operation>`, pure Ed25519 only.
fn ed25519(operation: &str, args: &[Vec<u8>]) -> Result<Reply> {
    match operation {
        // To the seed and the public key.
        "keyGen" => {
            take::<0>(args)?;
            let key = ed25519::KeyPair::generate()?;
            Ok(vec![
                key.to_seed().as_ref().to_vec(),
                key.public_key().as_ref().to_vec(),
            ])
        }
        // A public key, to whether the module takes it.
        "keyVer" => {
            let [q] = take(args)?;
            Ok(vec![flag(ed25519::PublicKey::new(q).is_ok())])
        }
        // A seed and message, to the signature.
        "sigGen" => {
            let [seed, message] = take(args)?;
            let key = ed25519::KeyPair::from_seed(seed)?;
            Ok(vec![key.sign(message).as_ref().to_vec()])
        }
        // Message, public key, and signature, to whether it verifies.
        "sigVer" => {
            let [message, q, signature] = take(args)?;
            let valid = ed25519::PublicKey::new(q)
                .and_then(|key| key.verify(message, signature))
                .is_ok();
            Ok(vec![flag(valid)])
        }
        _ => Err("not an operation rind's module registers".into()),
    }
}

// RSA.

fn rsa_size(bits: u32) -> Result<KeySize> {
    Ok(match bits {
        2048 => KeySize::Rsa2048,
        3072 => KeySize::Rsa3072,
        4096 => KeySize::Rsa4096,
        6144 => KeySize::Rsa6144,
        8192 => KeySize::Rsa8192,
        _ => return Err(format!("no {bits}-bit RSA keys").into()),
    })
}

fn rsa_signing(hash: &str, scheme: &str) -> Result<&'static rsa::SigningAlgorithm> {
    Ok(match (scheme, hash) {
        ("pkcs1v1.5", "SHA2-256") => &rsa::sign::PKCS1_SHA256,
        ("pkcs1v1.5", "SHA2-384") => &rsa::sign::PKCS1_SHA384,
        ("pkcs1v1.5", "SHA2-512") => &rsa::sign::PKCS1_SHA512,
        ("pss", "SHA2-256") => &rsa::sign::PSS_SHA256,
        ("pss", "SHA2-384") => &rsa::sign::PSS_SHA384,
        ("pss", "SHA2-512") => &rsa::sign::PSS_SHA512,
        _ => return Err(format!("no RSA {scheme} signing with {hash}").into()),
    })
}

/// The verification algorithm of `scheme` with `hash` for a modulus of
/// `bits`: the legacy ones for 1024-bit keys, and SHA-1, which only verify.
fn rsa_verification(
    hash: &str,
    scheme: &str,
    bits: usize,
) -> Result<&'static rsa::VerificationAlgorithm> {
    use rsa::verify::{self, legacy};
    Ok(match (scheme, hash, bits == 1024) {
        ("pkcs1v1.5", "SHA-1", true) => &legacy::PKCS1_1024_SHA1,
        ("pkcs1v1.5", "SHA2-256", true) => &legacy::PKCS1_1024_SHA256,
        ("pkcs1v1.5", "SHA2-512", true) => &legacy::PKCS1_1024_SHA512,
        ("pkcs1v1.5", "SHA-1", false) => &legacy::PKCS1_SHA1,
        ("pkcs1v1.5", "SHA2-256", false) => &verify::PKCS1_SHA256,
        ("pkcs1v1.5", "SHA2-384", false) => &verify::PKCS1_SHA384,
        ("pkcs1v1.5", "SHA2-512", false) => &verify::PKCS1_SHA512,
        ("pss", "SHA2-256", false) => &verify::PSS_SHA256,
        ("pss", "SHA2-384", false) => &verify::PSS_SHA384,
        ("pss", "SHA2-512", false) => &verify::PSS_SHA512,
        _ => return Err(format!("no RSA {scheme} verification with {hash} at {bits} bits").into()),
    })
}

/// `RSA/keyGen`: modulus size, to the public exponent, the primes, the
/// modulus, and the private exponent.
fn rsa_key_gen(args: &[Vec<u8>]) -> Result<Reply> {
    let [bits] = take(args)?;
    let key = rsa::KeyPair::generate(rsa_size(u32_le(bits)?)?)?;
    let pkcs8 = key.to_pkcs8();
    let private = RsaPrivateKey::parse(pkcs8.as_ref())?;
    Ok([private.e, private.p, private.q, private.n, private.d]
        .map(<[u8]>::to_vec)
        .into())
}

/// `RSA/sigVer/<hash>/<scheme>`: modulus, public exponent, message, and
/// signature, to whether it verifies.
fn rsa_sig_ver(hash: &str, scheme: &str, args: &[Vec<u8>]) -> Result<Reply> {
    let [n, e, message, signature] = take(args)?;
    let (n, e) = (minimal(n), minimal(e));
    let bits = n
        .first()
        .map_or(0, |b| n.len() * 8 - b.leading_zeros() as usize);
    let algorithm = rsa_verification(hash, scheme, bits)?;
    let valid = rsa::PublicKey::from_components(&PublicKeyComponents { n, e })
        .and_then(|key| key.verify(algorithm, message, signature))
        .is_ok();
    Ok(vec![flag(valid)])
}

/// The integers of a PKCS#8 RSA private key, as `RsaKeyPair::to_pkcs8`
/// encodes it: RFC 8017's `RSAPrivateKey` in RFC 5208's `PrivateKeyInfo`.
struct RsaPrivateKey<'a> {
    n: &'a [u8],
    e: &'a [u8],
    d: &'a [u8],
    p: &'a [u8],
    q: &'a [u8],
}

impl<'a> RsaPrivateKey<'a> {
    fn parse(pkcs8: &'a [u8]) -> Result<Self> {
        let mut info = Der(Der(pkcs8).next(0x30)?);
        info.next(0x02)?;
        info.next(0x30)?;
        let mut key = Der(Der(info.next(0x04)?).next(0x30)?);
        key.next(0x02)?;
        let [n, e, d, p, q] = [(); 5].map(|()| key.next(0x02).map(minimal));
        Ok(Self {
            n: n?,
            e: e?,
            d: d?,
            p: p?,
            q: q?,
        })
    }
}

/// A cursor over DER elements.
struct Der<'a>(&'a [u8]);

impl<'a> Der<'a> {
    /// The contents of the next element, which must have tag `tag`.
    fn next(&mut self, tag: u8) -> Result<&'a [u8]> {
        let [found, first, rest @ ..] = self.0 else {
            return Err("truncated DER".into());
        };
        if *found != tag {
            return Err("unexpected DER".into());
        }
        let (len, rest) = match *first {
            len @ 0..=0x7f => (len as usize, rest),
            0x81..=0x84 => {
                let (bytes, rest) = rest
                    .split_at_checked((first & 0x7f) as usize)
                    .ok_or("truncated DER")?;
                let len = bytes.iter().fold(0usize, |len, &b| len << 8 | b as usize);
                (len, rest)
            }
            _ => return Err("unexpected DER".into()),
        };
        let (contents, rest) = rest.split_at_checked(len).ok_or("truncated DER")?;
        self.0 = rest;
        Ok(contents)
    }
}

// ML-KEM and ML-DSA, whose deterministic forms the ACVP build offers.

/// `ML-KEM/<set>/<operation>`.
fn ml_kem(set: &str, operation: &str, args: &[Vec<u8>]) -> Result<Reply> {
    match set {
        "ML-KEM-512" => ml_kem_set::<kem::MlKem512>(operation, args),
        "ML-KEM-768" => ml_kem_set::<kem::MlKem768>(operation, args),
        "ML-KEM-1024" => ml_kem_set::<kem::MlKem1024>(operation, args),
        _ => Err(format!("no {set}").into()),
    }
}

fn ml_kem_set<A: kem::Algorithm>(operation: &str, args: &[Vec<u8>]) -> Result<Reply> {
    match operation {
        // Seeds `d` and `z`, to the encapsulation and decapsulation keys.
        "keyGen" => {
            let [d, z] = take(args)?;
            let (ek, dk) = acvp::ml_kem_key_gen::<A>(d, z)?;
            Ok(vec![ek, dk])
        }
        // An encapsulation key and message `m`, to the ciphertext and the
        // shared secret.
        "encap" => {
            let [ek, m] = take(args)?;
            let (ciphertext, secret) = acvp::ml_kem_encap::<A>(ek, m)?;
            Ok(vec![ciphertext, secret])
        }
        // A decapsulation key and ciphertext, to the shared secret.
        "decap" => {
            let [dk, ciphertext] = take(args)?;
            Ok(vec![acvp::ml_kem_decap::<A>(dk, ciphertext)?])
        }
        // A key, to whether it passes FIPS 203's input check.
        "encapKeyCheck" => {
            let [ek] = take(args)?;
            let valid = acvp::ml_kem_check_encapsulation_key::<A>(ek).is_ok();
            Ok(vec![flag(valid)])
        }
        "decapKeyCheck" => {
            let [dk] = take(args)?;
            let valid = acvp::ml_kem_check_decapsulation_key::<A>(dk).is_ok();
            Ok(vec![flag(valid)])
        }
        _ => Err("not an operation rind's module registers".into()),
    }
}

/// What an ML-DSA request signs or verifies: with no `externalMu` flag,
/// the external interface's message under a context; with it false, the
/// internal interface's `M'`; with it true, `mu`.
fn ml_dsa_message<'a>(
    message: &'a [u8],
    mu: &'a [u8],
    context: &'a [u8],
    external_mu: &[u8],
) -> Result<MlDsaMessage<'a>> {
    match external_mu {
        [] => Ok(MlDsaMessage::External { context, message }),
        [0] => Ok(MlDsaMessage::Internal(message)),
        [1] => Ok(MlDsaMessage::Mu(mu)),
        _ => Err("an externalMu flag not one byte of 0 or 1".into()),
    }
}

/// `ML-DSA/<set>/<operation>`.
fn ml_dsa<P: ParameterSet>(operation: &str, args: &[Vec<u8>]) -> Result<Reply> {
    match operation {
        // A seed, to the public key and the expanded private key.
        "keyGen" => {
            let [seed] = take(args)?;
            let (pk, sk) = acvp::ml_dsa_key_gen::<P>(seed)?;
            Ok(vec![pk, sk])
        }
        // An expanded private key, message, `mu`, `rnd`, context, and
        // `externalMu` flag, to the signature; an empty `rnd` signs
        // deterministically, with zeros.
        "sigGen" => {
            let [sk, message, mu, rnd, context, external_mu] = take(args)?;
            let message = ml_dsa_message(message, mu, context, external_mu)?;
            let rnd = if rnd.is_empty() { &[0; 32][..] } else { rnd };
            Ok(vec![acvp::ml_dsa_sign::<P>(sk, message, rnd)?])
        }
        // A signature, public key, message, `mu`, context, and `externalMu`
        // flag, to whether it verifies.
        "sigVer" => {
            let [signature, pk, message, mu, context, external_mu] = take(args)?;
            let message = ml_dsa_message(message, mu, context, external_mu)?;
            let valid = acvp::ml_dsa_verify::<P>(pk, message, signature).is_ok();
            Ok(vec![flag(valid)])
        }
        _ => Err("not an operation rind's module registers".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::{aes_gcm_seal, read_request};

    #[test]
    fn input_ends_only_between_requests() {
        assert!(read_request(&mut &[][..]).unwrap().is_none());
        for len in 1..4 {
            assert!(read_request(&mut &[1, 0, 0, 0][..len]).is_err());
        }
        // One string, "ab", then a request cut short in its lengths.
        let input = [1, 0, 0, 0, 2, 0, 0, 0, b'a', b'b', 1, 0, 0, 0, 2];
        let mut input = &input[..];
        assert_eq!(
            read_request(&mut input).unwrap(),
            Some(vec![b"ab".to_vec()])
        );
        assert!(read_request(&mut input).is_err());
    }

    /// The two guards `acvptool`'s configuration never reaches: a shorter
    /// tag, and a nonce it supplies, are both refused; the valid call seals.
    #[test]
    fn gcm_seal_refuses_a_tag_or_nonce_it_is_not_configured_for() {
        let seal = |tag_len: u32, nonce: &[u8]| {
            aes_gcm_seal(&[
                tag_len.to_le_bytes().to_vec(),
                vec![7; 32],
                b"plaintext".to_vec(),
                nonce.to_vec(),
                b"aad".to_vec(),
            ])
        };
        // Ciphertext, 16-byte tag, then the 12-byte IV.
        assert_eq!(seal(16, &[]).unwrap()[0].len(), 9 + 16 + 12);
        let tag = seal(15, &[]).unwrap_err().to_string();
        assert!(tag.contains("tag of other than 16 bytes"), "{tag}");
        let nonce = seal(16, &[0; 12]).unwrap_err().to_string();
        assert!(nonce.contains("module generates the IV"), "{nonce}");
    }
}
