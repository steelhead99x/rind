//! The tests: each spec on its published vectors, then on random inputs
//! against rind.

use std::collections::BTreeMap;
use std::num::NonZeroU32;

use serde_json::Value;

use crate::From::{Rind, Vector};
use crate::{Run, hex, trim, unhex};

/// A section's name and its tests.
pub type Section = (&'static str, fn(&mut Run));

/// The sections, each run on its own thread, the slowest first.
pub const SECTIONS: &[Section] = &[
    ("mlkem1024", |run| {
        mlkem::<rind::kem::MlKem1024>(run, "1024")
    }),
    ("sha2", sha2),
    ("mlkem768", |run| mlkem::<rind::kem::MlKem768>(run, "768")),
    ("ed25519", ed25519),
    ("kdfs", kdfs),
    ("mlkem512", |run| mlkem::<rind::kem::MlKem512>(run, "512")),
    ("sha3", sha3),
    ("ecdsa", ecdsa),
    ("nist", nist),
    ("aes_modes", aes_modes),
    ("rsa", rsa),
    ("gcm", gcm),
    ("aes", aes),
    ("macs", macs),
    ("chacha", chacha),
    ("x25519", x25519),
];

/// The lowercase hex of a hex or quoted string, as the server reads it.
fn h(s: &str) -> String {
    hex(&unhex(s))
}

/// The words of a request.
fn w(words: &[&String]) -> Vec<String> {
    words.iter().map(|s| s.to_string()).collect()
}

/// `words` as the `&[&str]` `Run::check` takes.
fn r(words: &[String]) -> Vec<&str> {
    words.iter().map(String::as_str).collect()
}

// ## Vector files

/// A FileTest or CAVP record: its fields, and the bracketed section headers
/// above it, `[key = value]` by key and the rest, such as CAVP's curve and
/// its method under it, in order.
struct Record {
    section: BTreeMap<String, String>,
    headers: Vec<String>,
    fields: Vec<(String, String)>,
}

impl Record {
    fn get(&self, key: &str) -> Option<&str> {
        self.fields
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v.as_str())
    }

    fn s(&self, key: &str) -> &str {
        self.get(key)
            .unwrap_or_else(|| panic!("spec-tests: no {key} in {:?}", self.fields))
    }

    fn h(&self, key: &str) -> String {
        h(self.s(key))
    }

    fn bytes(&self, key: &str) -> Vec<u8> {
        unhex(self.s(key))
    }

    fn n(&self, key: &str) -> usize {
        self.s(key)
            .trim()
            .parse()
            .unwrap_or_else(|_| panic!("spec-tests: {key} is not a number"))
    }

    fn sect(&self, key: &str) -> &str {
        self.section.get(key).map(String::as_str).unwrap_or("")
    }

    /// The curve a header names, as `[P-256]` or `[P-256,SHA-256]` do, and
    /// the hash after it, if any.
    fn curve(&self) -> Option<(&'static Curve, Option<&str>)> {
        self.headers.iter().find_map(|h| {
            let (c, hash) = match h.split_once(',') {
                Some((c, hash)) => (c, Some(hash)),
                None => (h.as_str(), None),
            };
            curve(c).map(|c| (c, hash))
        })
    }
}

/// The records of a FileTest (`Key = value` or `KEY: value`) or CAVP
/// response file, sampled.
fn records(run: &mut Run, rel: &str) -> Vec<Record> {
    run.source(rel);
    let path = run.path(rel);
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("spec-tests: {}: {e}", path.display()));
    let mut out = Vec::new();
    let mut section = BTreeMap::new();
    let mut headers: Vec<String> = Vec::new();
    // Whether a record followed the last header, so the next starts a new
    // block of unkeyed headers.
    let mut recorded = false;
    let mut fields: Vec<(String, String)> = Vec::new();
    let mut flush = |fields: &mut Vec<(String, String)>,
                     section: &BTreeMap<String, String>,
                     headers: &[String],
                     recorded: &mut bool| {
        if !fields.is_empty() {
            out.push(Record {
                section: section.clone(),
                headers: headers.to_vec(),
                fields: std::mem::take(fields),
            });
            *recorded = true;
        }
    };
    for line in text.lines() {
        let line = line.trim_end_matches('\r');
        if line.starts_with('#') {
            continue;
        }
        if line.trim().is_empty() {
            flush(&mut fields, &section, &headers, &mut recorded);
            continue;
        }
        if let Some(header) = line
            .trim()
            .strip_prefix('[')
            .and_then(|l| l.strip_suffix(']'))
        {
            flush(&mut fields, &section, &headers, &mut recorded);
            if recorded {
                headers.clear();
                recorded = false;
            }
            match header.split_once('=') {
                Some((k, v)) => {
                    section.insert(k.trim().to_owned(), v.trim().to_owned());
                }
                None => headers.push(header.trim().to_owned()),
            }
            continue;
        }
        let at = match (line.find('='), line.find(':')) {
            (Some(a), Some(b)) => a.min(b),
            (Some(a), None) | (None, Some(a)) => a,
            (None, None) => continue,
        };
        fields.push((
            line[..at].trim().to_owned(),
            line[at + 1..].trim().to_owned(),
        ));
    }
    flush(&mut fields, &section, &headers, &mut recorded);
    run.sample(out)
}

/// The groups and tests of a Wycheproof file, sampled.
fn wycheproof(run: &mut Run, name: &str) -> Vec<(Value, Value)> {
    run.source(&format!("wycheproof/{name}"));
    let path = run.path(&format!("wycheproof/testvectors_v1/{name}.json"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("spec-tests: {}: {e}", path.display()));
    let json: Value = serde_json::from_str(&text).unwrap();
    let mut out = Vec::new();
    for group in json["testGroups"].as_array().unwrap() {
        let mut g = group.clone();
        g.as_object_mut().unwrap().remove("tests");
        for test in group["tests"].as_array().unwrap() {
            out.push((g.clone(), test.clone()));
        }
    }
    run.sample(out)
}

fn js<'a>(v: &'a Value, key: &str) -> &'a str {
    v[key]
        .as_str()
        .unwrap_or_else(|| panic!("spec-tests: no {key} in {v}"))
}

fn jh(v: &Value, key: &str) -> String {
    h(js(v, key))
}

fn jn(v: &Value, key: &str) -> u64 {
    v[key]
        .as_u64()
        .unwrap_or_else(|| panic!("spec-tests: no {key} in {v}"))
}

/// Whether an AEAD `-open` reply is a refusal: a message token, then the
/// status `0`, and nothing else.
fn refused(got: &str) -> bool {
    matches!(got.split(' ').collect::<Vec<_>>()[..], [_, "0"])
}

fn valid(t: &Value) -> bool {
    js(t, "result") == "valid"
}

fn label(file: &str, t: &Value) -> String {
    format!("{file} #{}", t["tcId"])
}

/// Checks the server's verdict on a case whose expected result is `want`, a
/// Wycheproof result: `acceptable` takes either.
fn verdict(run: &mut Run, label: &str, words: &[&str], want: &str, refused: &[&str]) {
    let got = run.ask(Vector, words);
    let accepted = got == "1";
    let ok = match want {
        "valid" => accepted,
        "invalid" => !accepted && (got == "0" || refused.contains(&got.as_str())),
        "acceptable" => got == "1" || got == "0" || refused.contains(&got.as_str()),
        _ => panic!("spec-tests: {label}: no Wycheproof result {want:?}"),
    };
    if !ok {
        run.fail(format!(
            "{label}: {}\n  spec: {got}\n  want: {want}",
            trim(words)
        ));
    }
}

// ## Digests

const SHA2: &[(&str, &str, &rind::digest::Algorithm)] = &[
    ("SHA256", "sha256", &rind::digest::SHA256),
    ("SHA384", "sha384", &rind::digest::SHA384),
    ("SHA512", "sha512", &rind::digest::SHA512),
    ("SHA512_256", "sha512_256", &rind::digest::SHA512_256),
];

const SHA3: &[(&str, &str, &rind::digest::Algorithm)] = &[
    ("SHA3_256", "sha3_256", &rind::digest::SHA3_256),
    ("SHA3_384", "sha3_384", &rind::digest::SHA3_384),
    ("SHA3_512", "sha3_512", &rind::digest::SHA3_512),
];

/// Whether s2n-bignum's SHA-2 runs on a vector of `len` bytes. Its
/// schedule, `sha256_msg_schedule` and `sha512_msg_schedule` as HOL Light
/// defines them, recurses without sharing, so a block costs SHA-256 some 25
/// ms and SHA-512 most of a second. `S2nSha256` and `S2nSha512` prove each
/// equal to FIPS 180-4's spec, which runs on every message: this runs the
/// s2n form on two blocks of SHA-256, and on one of SHA-512, every such
/// vector with `full` and otherwise the first, which `ran` counts, beside the
/// random messages of that length it always runs on.
fn s2n_runs(run: &Run, op: &str, len: usize, ran: usize) -> bool {
    if op == "sha256" {
        len < 120
    } else {
        len < 112 && (run.full || ran == 0)
    }
}

fn sha2(run: &mut Run) {
    // CAVP's byte-aligned messages, through the spec and its s2n-bignum form.
    for (file, op, _) in SHA2 {
        let mut ran = 0;
        for kind in ["ShortMsg", "LongMsg"] {
            let rel = format!("cavp/sha2/{file}{kind}.rsp");
            for rec in records(run, &rel) {
                let len = rec.n("Len");
                if len % 8 != 0 {
                    continue;
                }
                let m = &rec.bytes("Msg")[..len / 8];
                let md = rec.h("MD");
                run.check(Vector, &rel, &[op, &hex(m)], &md);
                if s2n_runs(run, op, m.len(), ran) {
                    run.check(Vector, &rel, &[&format!("{op}-s2n"), &hex(m)], &md);
                    ran += 1;
                }
            }
        }
    }
    // RFC 3174's, as CAVP has no SHA-1 file here.
    run.source("RFC 3174");
    for (m, md) in [
        ("616263", "a9993e364706816aba3e25717850c26c9cd0d89d"),
        (
            "6162636462636465636465666465666765666768666768696768696a68696a6b696a6b6c6a6b6c6d6b6c6d6e6c6d6e6f6d6e6f706e6f7071",
            "84983e441c3bd26ebaae4aa1f95129e5e54670f1",
        ),
    ] {
        run.check(Vector, "RFC 3174", &["sha1", m], md);
    }
    let algs: Vec<(&str, &rind::digest::Algorithm)> = SHA2
        .iter()
        .map(|(_, op, alg)| (*op, *alg))
        .chain([("sha1", &rind::digest::legacy::SHA1)])
        .collect();
    random_digests(run, &algs);
}

fn sha3(run: &mut Run) {
    for (file, op, _) in SHA3 {
        for kind in ["ShortMsg", "LongMsg"] {
            let rel = format!("cavp/sha3/{file}{kind}.rsp");
            for rec in records(run, &rel) {
                let len = rec.n("Len");
                if len % 8 != 0 {
                    continue;
                }
                let m = hex(&rec.bytes("Msg")[..len / 8]);
                let md = rec.h("MD");
                run.check(Vector, &rel, &[op, &m], &md);
                if *op == "sha3_256" {
                    run.check(Vector, &rel, &["sha3_256-symcrypt", &m], &md);
                }
            }
        }
    }
    for (file, op) in [("SHAKE128", "shake128"), ("SHAKE256", "shake256")] {
        for kind in ["ShortMsg", "LongMsg", "VariableOut"] {
            let rel = format!("cavp/sha3/{file}{kind}.rsp");
            for rec in records(run, &rel) {
                let (len, out) = match kind {
                    "VariableOut" => (
                        rec.sect("Input Length").parse().unwrap(),
                        rec.n("Outputlen"),
                    ),
                    _ => (rec.n("Len"), rec.sect("Outputlen").parse().unwrap()),
                };
                if len % 8 != 0 || out % 8 != 0 {
                    continue;
                }
                let m = hex(&rec.bytes("Msg")[..len / 8]);
                let n = (out / 8).to_string();
                let want = rec.h("Output");
                run.check(Vector, &rel, &[op, &m, &n], &want);
                if op == "shake128" {
                    run.check(Vector, &rel, &["shake128-symcrypt", &m, &n], &want);
                }
            }
        }
    }
    let algs: Vec<(&str, &rind::digest::Algorithm)> =
        SHA3.iter().map(|(_, op, alg)| (*op, *alg)).collect();
    random_digests(run, &algs);
}

fn random_digests(run: &mut Run, algs: &[(&str, &'static rind::digest::Algorithm)]) {
    for &(op, alg) in algs {
        for _ in 0..run.random {
            let m = run.rng.message(1000);
            let want = hex(rind::digest::digest(alg, &m).as_ref());
            run.check(Rind, "random", &[op, &hex(&m)], &want);
            if SHA2.iter().any(|(_, o, _)| *o == op) {
                // A message s2n-bignum's form runs on, as `s2n_runs` bounds.
                let m = &m[..m.len().min(if op == "sha256" { 119 } else { 111 })];
                let want = hex(rind::digest::digest(alg, m).as_ref());
                run.check(Rind, "random", &[&format!("{op}-s2n"), &hex(m)], &want);
            }
        }
    }
}

// ## MACs

fn hmac_alg(op: &str) -> &'static rind::hmac::Algorithm {
    match op {
        "sha1" => &rind::hmac::legacy::HMAC_SHA1,
        "sha256" => &rind::hmac::HMAC_SHA256,
        "sha384" => &rind::hmac::HMAC_SHA384,
        _ => &rind::hmac::HMAC_SHA512,
    }
}

const HASHES: &[&str] = &["sha1", "sha256", "sha384", "sha512"];

/// A hash's request name from its Wycheproof, CAVP, or FileTest name.
fn hash_name(s: &str) -> Option<&'static str> {
    match s.to_ascii_uppercase().replace('-', "").as_str() {
        "SHA1" => Some("sha1"),
        "SHA256" => Some("sha256"),
        "SHA384" => Some("sha384"),
        "SHA512" => Some("sha512"),
        _ => None,
    }
}

/// A hash's output length in bytes, by its request name.
fn hash_len(op: &str) -> usize {
    match op {
        "sha1" => 20,
        "sha256" => 32,
        "sha384" => 48,
        _ => 64,
    }
}

fn macs(run: &mut Run) {
    // HMAC: CAVP, with tags truncated to Tlen.
    let rel = "cavp/hmac/HMAC.rsp";
    for rec in records(run, rel) {
        let op = match rec.sect("L") {
            "20" => "sha1",
            "32" => "sha256",
            "48" => "sha384",
            "64" => "sha512",
            _ => continue,
        };
        let (k, m) = (rec.h("Key"), rec.h("Msg"));
        let got = run.ask(Vector, &["hmac", op, &k, &m]);
        let tag = rec.h("Mac");
        // The whole tag, of which a vector may give a prefix.
        if got.len() != 2 * hash_len(op) || !got.starts_with(&tag) {
            run.fail(format!(
                "{rel} {}: hmac {op} {k} {m}\n  spec: {got}\n  want: {tag}...",
                rec.s("Count")
            ));
        }
    }
    for op in HASHES {
        let file = format!("hmac_{op}_test");
        for (g, t) in wycheproof(run, &file) {
            let size = jn(&g, "tagSize") as usize / 8;
            let (k, m) = (jh(&t, "key"), jh(&t, "msg"));
            let got = run.ask(Vector, &["hmac", op, &k, &m]);
            let tag = jh(&t, "tag");
            let matches =
                got.len() == 2 * hash_len(op) && got[..2 * size] == tag && tag.len() == 2 * size;
            if matches != valid(&t) {
                run.fail(format!(
                    "{}: hmac {op} {k} {m}\n  spec: {got}\n  want: {tag} {}",
                    label(&file, &t),
                    js(&t, "result")
                ));
            }
        }
    }
    let rel = "aws-lc/crypto/hmac_extra/hmac_tests.txt";
    for rec in records(run, rel) {
        let Some(op) = hash_name(rec.s("HMAC")) else {
            continue;
        };
        run.check(
            Vector,
            rel,
            &["hmac", op, &rec.h("Key"), &rec.h("Input")],
            &rec.h("Output"),
        );
    }
    for op in HASHES {
        for _ in 0..run.random {
            let k = run.rng.message(200);
            let m = run.rng.message(1000);
            let want = hex(rind::hmac::sign(&rind::hmac::Key::new(hmac_alg(op), &k), &m).as_ref());
            run.check(Rind, "random", &["hmac", op, &hex(&k), &hex(&m)], &want);
        }
    }

    // Poly1305, alone only in vectors: rind runs it inside ChaCha20-Poly1305.
    let rel = "aws-lc/crypto/poly1305/poly1305_tests.txt";
    for rec in records(run, rel) {
        let (k, m, mac) = (rec.h("Key"), rec.h("Input"), rec.h("MAC"));
        run.check(Vector, rel, &["poly1305", &k, &m], &mac);
        run.check(Vector, rel, &["poly1305-s2n", &k, &m], &mac);
    }
}

// ## KDFs

fn kdfs(run: &mut Run) {
    for op in HASHES {
        let file = format!("hkdf_{op}_test");
        for (_, t) in wycheproof(run, &file) {
            // An invalid case asks for more than 255 blocks, which the spec
            // does not bound and the server refuses.
            let size = jn(&t, "size").to_string();
            run.check(
                Vector,
                &label(&file, &t),
                &[
                    "hkdf",
                    op,
                    &jh(&t, "ikm"),
                    &jh(&t, "salt"),
                    &jh(&t, "info"),
                    &size,
                ],
                &if valid(&t) {
                    jh(&t, "okm")
                } else {
                    "none".to_owned()
                },
            );
        }
        let alg = match *op {
            "sha1" => &rind::hkdf::legacy::HKDF_SHA1,
            "sha256" => &rind::hkdf::HKDF_SHA256,
            "sha384" => &rind::hkdf::HKDF_SHA384,
            _ => &rind::hkdf::HKDF_SHA512,
        };
        for _ in 0..run.random {
            let ikm = run.rng.message(100);
            let salt = run.rng.message(100);
            let info = run.rng.message(100);
            let mut okm = vec![0; 1 + run.rng.below(300)];
            rind::hkdf::Salt::new(alg, &salt)
                .extract(&ikm)
                .and_then(|prk| prk.fill(&[&info], &mut okm))
                .unwrap();
            let len = okm.len().to_string();
            run.check(
                Rind,
                "random",
                &["hkdf", op, &hex(&ikm), &hex(&salt), &hex(&info), &len],
                &hex(&okm),
            );
        }
    }

    // PBKDF2's vectors iterate HMAC 4096 times, mostly, which the spec takes
    // some seconds over: without `full`, each file runs four of them, and
    // with it every vector but RFC 6070's 2^24 iterations, which would take
    // hours.
    for op in HASHES {
        let file = format!("pbkdf2_hmac{op}_test");
        let cases: Vec<_> = wycheproof(run, &file)
            .into_iter()
            .filter(|(_, t)| valid(t) && jn(t, "iterationCount") <= 100_000)
            .collect();
        for (_, t) in run.sample_n(cases, 4) {
            let c = jn(&t, "iterationCount");
            run.check(
                Vector,
                &label(&file, &t),
                &[
                    "pbkdf2",
                    op,
                    &jh(&t, "password"),
                    &jh(&t, "salt"),
                    &c.to_string(),
                    &jn(&t, "dkLen").to_string(),
                ],
                &jh(&t, "dk"),
            );
        }
        let alg = match *op {
            "sha1" => &rind::pbkdf2::legacy::PBKDF2_HMAC_SHA1,
            "sha256" => &rind::pbkdf2::PBKDF2_HMAC_SHA256,
            "sha384" => &rind::pbkdf2::PBKDF2_HMAC_SHA384,
            _ => &rind::pbkdf2::PBKDF2_HMAC_SHA512,
        };
        for _ in 0..run.random {
            let pw = run.rng.message(100);
            let salt = run.rng.message(100);
            let c = 1 + run.rng.below(20) as u32;
            let mut dk = vec![0; 1 + run.rng.below(150)];
            rind::pbkdf2::Secret::new(alg, &pw)
                .derive(NonZeroU32::new(c).unwrap(), &salt, &mut dk)
                .unwrap();
            let len = dk.len().to_string();
            run.check(
                Rind,
                "random",
                &["pbkdf2", op, &hex(&pw), &hex(&salt), &c.to_string(), &len],
                &hex(&dk),
            );
        }
    }
}

// ## ChaCha20, Poly1305, and their AEADs

/// Checks an AEAD's seal and open on a vector: a valid case seals to its
/// ciphertext and tag and opens to its message, and an invalid one fails to
/// open.
#[allow(clippy::too_many_arguments)]
fn aead_vector(
    run: &mut Run,
    label: &str,
    op: &str,
    k: &str,
    n: &str,
    a: &str,
    m: &str,
    c: &str,
    t: &str,
    ok: bool,
) {
    let seal = format!("{op}-seal");
    let open = format!("{op}-open");
    if ok {
        run.check(Vector, label, &[&seal, k, n, a, m], &format!("{c} {t}"));
        run.check(Vector, label, &[&open, k, n, a, c, t], &format!("{m} 1"));
    } else {
        let got = run.ask(Vector, &[&open, k, n, a, c, t]);
        if !refused(&got) {
            run.fail(format!(
                "{label}: {open} {k} {n} {a} {c} {t}\n  spec: {got}\n  want: refused"
            ));
        }
    }
}

/// Checks an AEAD on rind's sealing: the spec seals the same, opens it, and
/// refuses it with a flipped bit.
#[allow(clippy::too_many_arguments)]
fn aead_random(
    run: &mut Run,
    op: &str,
    k: &[u8],
    n: &[u8],
    a: &[u8],
    m: &[u8],
    c: &[u8],
    t: &[u8],
) {
    let (k, n, a, m, c, t) = (hex(k), hex(n), hex(a), hex(m), hex(c), hex(t));
    run.check(
        Rind,
        "random",
        &[&format!("{op}-seal"), &k, &n, &a, &m],
        &format!("{c} {t}"),
    );
    run.check(
        Rind,
        "random",
        &[&format!("{op}-open"), &k, &n, &a, &c, &t],
        &format!("{m} 1"),
    );
    let mut bad = unhex(&t);
    bad[0] ^= 1;
    let got = run.ask(Rind, &[&format!("{op}-open"), &k, &n, &a, &c, &hex(&bad)]);
    if !refused(&got) {
        run.fail(format!(
            "random: {op}-open {k} {n} {a} {c} {}\n  spec: {got}\n  want: refused",
            hex(&bad)
        ));
    }
}

fn chacha(run: &mut Run) {
    // ChaCha20 alone: Wycheproof's IETF counter boundaries and RFC 8439's.
    // An invalid case runs past the counter's end, outside the theorems'
    // domain, where the server answers `none`.
    let file = "chacha20_counter_test";
    for (g, t) in wycheproof(run, file) {
        if js(&g, "algorithm") != "ChaCha20-IETF" {
            continue;
        }
        let ctr =
            u32::from_le_bytes(unhex(js(&t, "initialCounter")).try_into().unwrap()).to_string();
        let words = [jh(&t, "key"), ctr, jh(&t, "iv"), jh(&t, "msg")];
        for op in ["chacha20", "chacha20-s2n"] {
            run.check(
                Vector,
                &label(file, &t),
                &[op, &words[0], &words[1], &words[2], &words[3]],
                &if valid(&t) {
                    jh(&t, "ct")
                } else {
                    "none".to_owned()
                },
            );
        }
    }
    // RFC 8439 section 2.4.2.
    run.source("RFC 8439 2.4.2");
    let k = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f";
    let n = "000000000000004a00000000";
    let m = hex(b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.");
    let c = "6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0bf91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d807ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab77937365af90bbf74a35be6b40b8eedf2785e42874d";
    for op in ["chacha20", "chacha20-s2n"] {
        run.check(Vector, "RFC 8439 2.4.2", &[op, k, "1", n, &m], c);
    }
    // draft-irtf-cfrg-xchacha-03 section 2.2.1.
    run.source("draft-irtf-cfrg-xchacha 2.2.1");
    run.check(
        Vector,
        "draft-irtf-cfrg-xchacha 2.2.1",
        &["hchacha20", k, "000000090000004a0000000031415927"],
        "82413b4227b27bfed30e42508a877d73a0f9e4d58a74a853c12ec41326d3ecdc",
    );

    for (file, op, nonce) in [
        ("chacha20_poly1305_test", "chacha20poly1305", 12),
        ("chacha20_poly1305_test", "chacha20poly1305-s2n", 12),
        ("xchacha20_poly1305_test", "xchacha20poly1305", 24),
    ] {
        for (_, t) in wycheproof(run, file) {
            // The specs take only the nonce length the AEAD fixes.
            if unhex(js(&t, "iv")).len() != nonce || unhex(js(&t, "tag")).len() != 16 {
                continue;
            }
            let ok = valid(&t);
            aead_vector(
                run,
                &label(file, &t),
                op,
                &jh(&t, "key"),
                &jh(&t, "iv"),
                &jh(&t, "aad"),
                &jh(&t, "msg"),
                &jh(&t, "ct"),
                &jh(&t, "tag"),
                ok,
            );
        }
    }
    for (rel, ops, nonce) in [
        (
            "aws-lc/crypto/cipher_extra/test/chacha20_poly1305_tests.txt",
            &["chacha20poly1305", "chacha20poly1305-s2n"][..],
            12,
        ),
        (
            "aws-lc/crypto/cipher_extra/test/xchacha20_poly1305_tests.txt",
            &["xchacha20poly1305"][..],
            24,
        ),
    ] {
        for rec in records(run, rel) {
            if rec.bytes("NONCE").len() != nonce || rec.bytes("TAG").len() != 16 {
                continue;
            }
            let ok = rec.get("NO_SEAL").is_none() && rec.get("FAILS").is_none();
            for op in ops {
                aead_vector(
                    run,
                    rel,
                    op,
                    &rec.h("KEY"),
                    &rec.h("NONCE"),
                    &rec.h("AD"),
                    &rec.h("IN"),
                    &rec.h("CT"),
                    &rec.h("TAG"),
                    ok,
                );
            }
        }
    }

    for _ in 0..run.random {
        let k: [u8; 32] = run.rng.bytes(32).try_into().unwrap();
        let n: [u8; 12] = run.rng.bytes(12).try_into().unwrap();
        // Drawn again past the counter's end, which rind refuses and the
        // server answers `none`: RFC 8439's 32-bit counter covers the blocks
        // from `ctr` to 2^32 - 1.
        let (ctr, mut c) = loop {
            let ctr = run.rng.u64() as u32;
            let c = run.rng.message(1000);
            if u64::from(ctr) + c.len().div_ceil(64) as u64 <= 1 << 32 {
                break (ctr, c);
            }
        };
        let m = hex(&c);
        if let Err(e) = rind::cipher::ChaCha20::new(&k).apply_keystream(&n, ctr, &mut c) {
            run.fail(format!(
                "random: rind's chacha20 refuses counter {ctr} for {m}: {e:?}"
            ));
            continue;
        }
        for op in ["chacha20", "chacha20-s2n"] {
            run.check(
                Rind,
                "random",
                &[op, &hex(&k), &ctr.to_string(), &hex(&n), &m],
                &hex(&c),
            );
        }
    }
    for op in ["chacha20poly1305", "chacha20poly1305-s2n"] {
        for _ in 0..run.random {
            let k = run.rng.bytes(32);
            let n: [u8; 12] = run.rng.bytes(12).try_into().unwrap();
            let a = run.rng.message(100);
            let m = run.rng.message(1000);
            let mut c = m.clone();
            let key = rind::aead::Key::new(&rind::aead::CHACHA20_POLY1305, &k).unwrap();
            let t = key
                .seal_in_place_separate_tag(rind::aead::Nonce::assume_unique_for_key(n), &a, &mut c)
                .unwrap();
            aead_random(run, op, &k, &n, &a, &m, &c, t.as_ref());
        }
    }
    for _ in 0..run.random {
        let k: [u8; 32] = run.rng.bytes(32).try_into().unwrap();
        let a = run.rng.message(100);
        let m = run.rng.message(1000);
        let mut c = m.clone();
        let n = rind::aead::RandomizedNonceKey::new(&k)
            .seal_in_place_append_tag(&a, &mut c)
            .unwrap();
        let t = c.split_off(c.len() - 16);
        aead_random(run, "xchacha20poly1305", &k, n.as_ref(), &a, &m, &c, &t);
    }

    // QUIC header protection: RFC 9001 A.5, and rind.
    run.source("RFC 9001 A.5");
    run.check(
        Vector,
        "RFC 9001 A.5",
        &[
            "hp-chacha20",
            "25a282b9e82f06f21f488917a4fc8f1b73573685608597d0efcb076b0ab7a7a4",
            "5e5cd55c41f69080575d7999c25a5bfb",
        ],
        "aefefe7d03",
    );
    for _ in 0..run.random {
        let k = run.rng.bytes(32);
        let s: [u8; 16] = run.rng.bytes(16).try_into().unwrap();
        let mask = rind::aead::quic::HeaderProtectionKey::new(&rind::aead::quic::CHACHA20, &k)
            .unwrap()
            .mask(&s);
        run.check(
            Rind,
            "random",
            &["hp-chacha20", &hex(&k), &hex(&s)],
            &hex(&mask),
        );
    }
}

// ## AES

fn cipher_alg(len: usize) -> &'static rind::cipher::Algorithm {
    match len {
        16 => &rind::cipher::AES_128,
        24 => &rind::cipher::AES_192,
        _ => &rind::cipher::AES_256,
    }
}

fn aes(run: &mut Run) {
    for kind in ["GFSbox", "KeySbox", "VarKey", "VarTxt"] {
        for bits in [128, 192, 256] {
            let rel = format!("cavp/aes/ECB{kind}{bits}.rsp");
            for rec in records(run, &rel) {
                let (k, p, c) = (rec.h("KEY"), rec.h("PLAINTEXT"), rec.h("CIPHERTEXT"));
                run.check(Vector, &rel, &["aes-encrypt", &k, &p], &c);
                run.check(Vector, &rel, &["aes-decrypt", &k, &c], &p);
            }
        }
    }
    let rel = "aws-lc/crypto/fipsmodule/aes/aes_tests.txt";
    for rec in records(run, rel) {
        if rec.get("Mode") != Some("Raw") {
            continue;
        }
        let (k, p, c) = (rec.h("Key"), rec.h("Plaintext"), rec.h("Ciphertext"));
        run.check(Vector, rel, &["aes-encrypt", &k, &p], &c);
        run.check(Vector, rel, &["aes-decrypt", &k, &c], &p);
    }
    for _ in 0..run.random {
        let k = run.rng.aes_key();
        let p: [u8; 16] = run.rng.bytes(16).try_into().unwrap();
        let mut c = p;
        rind::cipher::Aes::new(cipher_alg(k.len()), &k)
            .unwrap()
            .encrypt_block(&mut c);
        run.check(
            Rind,
            "random",
            &["aes-encrypt", &hex(&k), &hex(&p)],
            &hex(&c),
        );
        // Decrypting one block of CBC from a zero IV is the inverse cipher.
        let mut d = c;
        rind::cipher::AesCbcDecryptingKey::new(cipher_alg(k.len()), &k)
            .unwrap()
            .decrypt_blocks(&[0; 16], &mut d)
            .unwrap();
        run.check(
            Rind,
            "random",
            &["aes-decrypt", &hex(&k), &hex(&c)],
            &hex(&d),
        );
    }

    // QUIC header protection: RFC 9001 A.2, and rind.
    run.source("RFC 9001 A.2");
    run.check(
        Vector,
        "RFC 9001 A.2",
        &[
            "hp-aes",
            "9f50449e04a0e810283a1e9933adedd2",
            "d1b1c98dd7689fb8ec11d242b123dc9b",
        ],
        "437b9aec36",
    );
    for _ in 0..run.random {
        let (alg, len) = if run.rng.below(2) == 0 {
            (&rind::aead::quic::AES_128, 16)
        } else {
            (&rind::aead::quic::AES_256, 32)
        };
        let k = run.rng.bytes(len);
        let s: [u8; 16] = run.rng.bytes(16).try_into().unwrap();
        let mask = rind::aead::quic::HeaderProtectionKey::new(alg, &k)
            .unwrap()
            .mask(&s);
        run.check(Rind, "random", &["hp-aes", &hex(&k), &hex(&s)], &hex(&mask));
    }
}

fn gcm(run: &mut Run) {
    for bits in [128, 192, 256] {
        // Every IV length CAVP has, and the tag's prefix for truncated tags.
        let rel = format!("cavp/gcm/gcmEncryptExtIV{bits}.rsp");
        for rec in records(run, &rel) {
            if rec.sect("IVlen").parse::<usize>().unwrap() % 8 != 0
                || rec.sect("PTlen").parse::<usize>().unwrap() % 8 != 0
                || rec.sect("AADlen").parse::<usize>().unwrap() % 8 != 0
            {
                continue;
            }
            let (k, iv, a, p) = (rec.h("Key"), rec.h("IV"), rec.h("AAD"), rec.h("PT"));
            let got = run.ask(Vector, &["aes-gcm-seal", &k, &iv, &a, &p]);
            let (c, t) = (rec.h("CT"), rec.h("Tag"));
            let ok = got.split_once(' ').is_some_and(|(gc, gt)| {
                gc == c
                    && gt.len() == 32
                    && gt.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
                    && gt.starts_with(&t)
            });
            if !ok {
                run.fail(format!(
                    "{rel} {}: aes-gcm-seal {k} {iv} {a} {p}\n  spec: {got}\n  want: {c} {t}...",
                    rec.s("Count")
                ));
            }
        }
        // Full tags only: the spec checks all 16 bytes.
        let rel = format!("cavp/gcm/gcmDecrypt{bits}.rsp");
        for rec in records(run, &rel) {
            if rec.sect("Taglen") != "128"
                || rec.sect("IVlen").parse::<usize>().unwrap() % 8 != 0
                || rec.sect("PTlen").parse::<usize>().unwrap() % 8 != 0
                || rec.sect("AADlen").parse::<usize>().unwrap() % 8 != 0
            {
                continue;
            }
            let words = [
                rec.h("Key"),
                rec.h("IV"),
                rec.h("AAD"),
                rec.h("CT"),
                rec.h("Tag"),
            ];
            let mut request = vec!["aes-gcm-open"];
            request.extend(words.iter().map(String::as_str));
            match rec.get("PT") {
                Some(_) => run.check(Vector, &rel, &request, &format!("{} 1", rec.h("PT"))),
                None => {
                    let got = run.ask(Vector, &request);
                    if !refused(&got) {
                        run.fail(format!(
                            "{rel} {}: {}\n  spec: {got}\n  want: FAIL",
                            rec.s("Count"),
                            trim(&request)
                        ));
                    }
                }
            }
        }
    }
    let file = "aes_gcm_test";
    for (g, t) in wycheproof(run, file) {
        if jn(&g, "tagSize") != 128 || unhex(js(&t, "iv")).is_empty() {
            continue;
        }
        let ok = valid(&t);
        aead_vector(
            run,
            &label(file, &t),
            "aes-gcm",
            &jh(&t, "key"),
            &jh(&t, "iv"),
            &jh(&t, "aad"),
            &jh(&t, "msg"),
            &jh(&t, "ct"),
            &jh(&t, "tag"),
            ok,
        );
    }
    for bits in [128, 192, 256] {
        let rel = format!("aws-lc/crypto/cipher_extra/test/aes_{bits}_gcm_tests.txt");
        for rec in records(run, &rel) {
            if rec.bytes("TAG").len() != 16 || rec.bytes("NONCE").is_empty() {
                continue;
            }
            let ok = rec.get("NO_SEAL").is_none() && rec.get("FAILS").is_none();
            aead_vector(
                run,
                &rel,
                "aes-gcm",
                &rec.h("KEY"),
                &rec.h("NONCE"),
                &rec.h("AD"),
                &rec.h("IN"),
                &rec.h("CT"),
                &rec.h("TAG"),
                ok,
            );
        }
    }

    for _ in 0..run.random {
        let k = run.rng.aes_key();
        // A 12-byte IV half the time, which takes the AEAD's fast path.
        let iv = if run.rng.below(2) == 0 {
            run.rng.bytes(12)
        } else {
            {
                let n = 1 + run.rng.below(64);
                run.rng.bytes(n)
            }
        };
        let a = run.rng.message(100);
        let m = run.rng.message(1000);
        let mut c = m.clone();
        let key =
            rind::aead::gcm::Key::new(cipher_alg(k.len()), &k, rind::aead::gcm::TagLength::Full)
                .unwrap();
        let t = key
            .seal_in_place_separate_tag(
                rind::aead::gcm::Iv::assume_unique_for_key(&iv).unwrap(),
                &a,
                &mut c,
            )
            .unwrap();
        aead_random(run, "aes-gcm", &k, &iv, &a, &m, &c, t.as_ref());
    }
}

fn aes_modes(run: &mut Run) {
    // CTR: aws-lc's, with a 128-bit counter, and rind's at every width.
    let rel = "aws-lc/crypto/cipher_extra/test/cipher_tests.txt";
    for rec in records(run, rel) {
        let cipher = rec.get("Cipher").unwrap_or("");
        if cipher.ends_with("-CTR") {
            run.check(
                Vector,
                rel,
                &[
                    "aes-ctr",
                    &rec.h("Key"),
                    "128",
                    &rec.h("IV"),
                    &rec.h("Plaintext"),
                ],
                &rec.h("Ciphertext"),
            );
        }
        if cipher.starts_with("AES-") && cipher.ends_with("-CBC") && rec.get("Operation").is_none()
        {
            // aws-lc's CBC vectors are unpadded whole blocks: the padded
            // encryption's prefix.
            let got = run.ask(
                Vector,
                &[
                    "aes-cbc-encrypt",
                    &rec.h("Key"),
                    &rec.h("IV"),
                    &rec.h("Plaintext"),
                ],
            );
            let want = rec.bytes("Ciphertext");
            let c = unhex(&got);
            if !c.starts_with(&want) || c.len() != want.len() + 16 {
                run.fail(format!(
                    "{rel}: aes-cbc-encrypt {} {} {}\n  spec: {got}\n  want: {}...",
                    rec.h("Key"),
                    rec.h("IV"),
                    rec.h("Plaintext"),
                    hex(&want)
                ));
            }
        }
    }
    for _ in 0..run.random {
        // Drawn again past the counter's 2^bits blocks, which rind refuses
        // and the server answers `none`.
        let (bits, mut c) = loop {
            let bits = [32u8, 64, 128, 1 + run.rng.below(128) as u8][run.rng.below(4)];
            let c = run.rng.message(1000);
            if bits >= 64 || c.len().div_ceil(16) as u64 <= 1 << bits {
                break (bits, c);
            }
        };
        let k = run.rng.aes_key();
        let t0: [u8; 16] = run.rng.bytes(16).try_into().unwrap();
        let m = hex(&c);
        let ctr = rind::cipher::AesCtr::new(cipher_alg(k.len()), &k, bits).unwrap();
        if let Err(e) = ctr.apply_keystream(&t0, &mut c) {
            run.fail(format!(
                "random: rind's aes-ctr refuses {bits} bits for {m}: {e:?}"
            ));
            continue;
        }
        run.check(
            Rind,
            "random",
            &["aes-ctr", &hex(&k), &bits.to_string(), &hex(&t0), &m],
            &hex(&c),
        );
    }
    // Counter widths outside 1 to 128, which both refuse.
    for bits in [0u8, 129] {
        let k = run.rng.aes_key();
        let t0 = hex(&run.rng.bytes(16));
        if rind::cipher::AesCtr::new(cipher_alg(k.len()), &k, bits).is_ok() {
            run.fail(format!("random: rind's aes-ctr takes {bits} bits"));
        }
        run.check(
            Rind,
            "edge",
            &["aes-ctr", &hex(&k), &bits.to_string(), &t0, "-"],
            "none",
        );
    }
    // The counter's capacity at its edge: a 1-bit counter covers two
    // blocks, 32 bytes, and refuses 33.
    for len in [32, 33] {
        let k = run.rng.aes_key();
        let t0: [u8; 16] = run.rng.bytes(16).try_into().unwrap();
        let mut c = run.rng.bytes(len);
        let m = hex(&c);
        let want = match rind::cipher::AesCtr::new(cipher_alg(k.len()), &k, 1)
            .unwrap()
            .apply_keystream(&t0, &mut c)
        {
            Ok(()) => hex(&c),
            Err(_) => "none".to_owned(),
        };
        if (want == "none") != (len == 33) {
            run.fail(format!(
                "random: rind's 1-bit aes-ctr on {len} bytes gives {want}"
            ));
        }
        run.check(
            Rind,
            "edge",
            &["aes-ctr", &hex(&k), "1", &hex(&t0), &m],
            &want,
        );
    }

    // CBC with PKCS#7 padding.
    let file = "aes_cbc_pkcs5_test";
    for (_, t) in wycheproof(run, file) {
        let (k, iv, m, c) = (jh(&t, "key"), jh(&t, "iv"), jh(&t, "msg"), jh(&t, "ct"));
        let ct = unhex(js(&t, "ct"));
        if unhex(js(&t, "iv")).len() != 16 || !ct.len().is_multiple_of(16) {
            continue;
        }
        if valid(&t) {
            run.check(
                Vector,
                &label(file, &t),
                &["aes-cbc-encrypt", &k, &iv, &m],
                &c,
            );
            run.check(
                Vector,
                &label(file, &t),
                &["aes-cbc-decrypt", &k, &iv, &c],
                &m,
            );
        } else {
            run.check(
                Vector,
                &label(file, &t),
                &["aes-cbc-decrypt", &k, &iv, &c],
                "none",
            );
        }
    }
    for _ in 0..run.random {
        let k = run.rng.aes_key();
        let iv: [u8; 16] = run.rng.bytes(16).try_into().unwrap();
        let m = run.rng.message(1000);
        let mut c = m.clone();
        rind::cipher::AesCbcEncryptingKey::new(cipher_alg(k.len()), &k)
            .unwrap()
            .encrypt(rind::cipher::CbcIv::assume_unpredictable(iv), &mut c)
            .unwrap();
        run.check(
            Rind,
            "random",
            &["aes-cbc-encrypt", &hex(&k), &hex(&iv), &hex(&m)],
            &hex(&c),
        );
        // A changed last block, which rind's unpadding mostly refuses, and a
        // byte added, which leaves a partial block both refuse.
        let mut bad = c.clone();
        let at = bad.len() - 1 - run.rng.below(16);
        bad[at] ^= 1 + run.rng.below(255) as u8;
        let mut long = c.clone();
        long.push(run.rng.u64() as u8);
        for (i, c) in [c, bad, long].into_iter().enumerate() {
            let mut d = c.clone();
            let want = match rind::cipher::AesCbcDecryptingKey::new(cipher_alg(k.len()), &k)
                .unwrap()
                .decrypt(&iv, &mut d)
            {
                Ok(m) => hex(m),
                Err(_) => "none".to_owned(),
            };
            // The untouched ciphertext decrypts to the message, so both
            // refusing it fails.
            if i == 0 && want != hex(&m) {
                run.fail(format!(
                    "random: rind's aes-cbc decrypts its own ciphertext to {want}"
                ));
            }
            run.check(
                Rind,
                "random",
                &["aes-cbc-decrypt", &hex(&k), &hex(&iv), &hex(&c)],
                &want,
            );
        }
    }

    // Key wrap, with and without padding.
    for (file, op, mode) in [
        ("aes_wrap_test", "aes-kw", rind::key_wrap::Mode::Kw),
        ("aes_kwp_test", "aes-kwp", rind::key_wrap::Mode::Kwp),
    ] {
        let (wrap, unwrap) = (format!("{op}-wrap"), format!("{op}-unwrap"));
        // The lengths each spec takes, as `AesKek`'s theorems in
        // `Rind.X86_64.AesKw` refuse the others before it runs, and the
        // server answers `none` outside: KW wraps whole semiblocks, two or
        // more, and unwraps three or more; KWP wraps any length from a byte
        // and unwraps two semiblocks or more.
        let wraps = match mode {
            rind::key_wrap::Mode::Kw => 16,
            _ => 1,
        };
        for (_, t) in wycheproof(run, file) {
            let (k, m, c) = (jh(&t, "key"), jh(&t, "msg"), jh(&t, "ct"));
            let ml = unhex(js(&t, "msg")).len();
            let wrappable =
                ml >= wraps && (mode == rind::key_wrap::Mode::Kwp || ml.is_multiple_of(8));
            if !wrappable {
                run.check(Vector, &label(file, &t), &[&wrap, &k, &m], "none");
            } else if valid(&t) {
                run.check(Vector, &label(file, &t), &[&wrap, &k, &m], &c);
            }
            let want = if valid(&t) { m } else { "none".to_owned() };
            run.check(Vector, &label(file, &t), &[&unwrap, &k, &c], &want);
        }
        for _ in 0..run.random {
            let k = run.rng.aes_key();
            let m = match mode {
                rind::key_wrap::Mode::Kw => {
                    let n = 8 * (2 + run.rng.below(30));
                    run.rng.bytes(n)
                }
                _ => {
                    let n = 1 + run.rng.below(240);
                    run.rng.bytes(n)
                }
            };
            let kek = rind::key_wrap::AesKek::new(cipher_alg(k.len()), &k).unwrap();
            let mut c = vec![0; m.len().div_ceil(8) * 8 + 8];
            kek.wrap_key(mode, &m, &mut c).unwrap();
            run.check(Rind, "random", &[&wrap, &hex(&k), &hex(&m)], &hex(&c));
            let mut bad = c.clone();
            let at = run.rng.below(bad.len());
            bad[at] ^= 1;
            // A partial semiblock, and one semiblock too few.
            let mut long = c.clone();
            long.push(run.rng.u64() as u8);
            let short = c[..c.len().min(match mode {
                rind::key_wrap::Mode::Kw => 16,
                _ => 8,
            })]
                .to_vec();
            for (i, c) in [c, bad, long, short].into_iter().enumerate() {
                let mut out = vec![0; c.len().saturating_sub(8)];
                let want = match kek.unwrap_key(mode, &c, &mut out) {
                    Ok(m) => hex(m),
                    Err(_) => "none".to_owned(),
                };
                // The untouched ciphertext unwraps to the key, so both
                // refusing it fails.
                if i == 0 && want != hex(&m) {
                    run.fail(format!(
                        "random: rind's {unwrap} unwraps its own wrap to {want}"
                    ));
                }
                run.check(Rind, "random", &[&unwrap, &hex(&k), &hex(&c)], &want);
            }
        }
    }
}

// ## The NIST curves

struct Curve {
    name: &'static str,
    cavp: &'static str,
    wycheproof: &'static str,
    len: usize,
    /// The group's order n, big-endian hex of `len` bytes (SEC 2).
    order: &'static str,
    ecdh: &'static rind::agreement::Algorithm,
    sign: &'static rind::ecdsa::SigningAlgorithm,
    verify: &'static rind::ecdsa::VerificationAlgorithm,
    hash: &'static rind::digest::Algorithm,
}

const CURVES: &[Curve] = &[
    Curve {
        name: "p256",
        cavp: "P-256",
        wycheproof: "secp256r1",
        len: 32,
        order: "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
        ecdh: &rind::agreement::ECDH_P256,
        sign: &rind::ecdsa::sign::P256_SHA256_FIXED,
        verify: &rind::ecdsa::verify::P256_SHA256_FIXED,
        hash: &rind::digest::SHA256,
    },
    Curve {
        name: "p384",
        cavp: "P-384",
        wycheproof: "secp384r1",
        len: 48,
        order: "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
        ecdh: &rind::agreement::ECDH_P384,
        sign: &rind::ecdsa::sign::P384_SHA384_FIXED,
        verify: &rind::ecdsa::verify::P384_SHA384_FIXED,
        hash: &rind::digest::SHA384,
    },
];

fn curve(cavp: &str) -> Option<&'static Curve> {
    CURVES.iter().find(|c| c.cavp == cavp)
}

/// A number's `len` big-endian bytes, as hex, from hex of any length.
fn fixed(s: &str, len: usize) -> String {
    let b = unhex(s);
    let b = &b[b.iter().position(|&x| x != 0).unwrap_or(b.len())..];
    let mut out = vec![0; len.saturating_sub(b.len())];
    out.extend_from_slice(b);
    hex(&out)
}

/// The two numbers of a reply that should be a finite point or an ECDSA
/// signature on a curve of `len` bytes: exactly two lowercase hex numbers of
/// that length, or `None`.
fn pair(got: &str, len: usize) -> Option<(&str, &str)> {
    let (x, y) = got.split_once(' ')?;
    let ok =
        |s: &str| s.len() == 2 * len && s.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'));
    (ok(x) && ok(y)).then_some((x, y))
}

/// An uncompressed point's coordinates as hex, or `None` for another
/// encoding.
fn point(bytes: &[u8], len: usize) -> Option<(String, String)> {
    (bytes.len() == 1 + 2 * len && bytes[0] == 4)
        .then(|| (hex(&bytes[1..1 + len]), hex(&bytes[1 + len..])))
}

/// A random key on `c` from the section's source, so the seed reproduces
/// it: a scalar drawn again until it is from 1 to n - 1, judged against the
/// curve's order rather than by rind, which must then take it.
fn nist_key(run: &mut Run, c: &Curve) -> rind::agreement::PrivateKey {
    let n = unhex(c.order);
    let scalar = loop {
        let s = run.rng.bytes(c.len);
        if s.iter().any(|&b| b != 0) && s < n {
            break s;
        }
    };
    rind::agreement::PrivateKey::from_scalar(c.ecdh, &scalar).unwrap_or_else(|e| {
        panic!(
            "spec-tests: rind refuses the {} scalar {}: {e:?}",
            c.name,
            hex(&scalar)
        )
    })
}

fn nist(run: &mut Run) {
    let rel = "cavp/ecdh/KAS_ECC_CDH_PrimitiveTest.txt";
    for rec in records(run, rel) {
        let Some((c, _)) = rec.curve() else {
            continue;
        };
        let d = rec.h("dIUT");
        run.check(
            Vector,
            rel,
            &["ec-base", c.name, &d],
            &format!("{} {}", rec.h("QIUTx"), rec.h("QIUTy")),
        );
        let got = run.ask(
            Vector,
            &["ec-mul", c.name, &d, &rec.h("QCAVSx"), &rec.h("QCAVSy")],
        );
        if pair(&got, c.len).map(|(x, _)| x) != Some(&rec.h("ZIUT")) {
            run.fail(format!(
                "{rel} {}: ec-mul\n  spec: {got}\n  want: {}",
                rec.s("COUNT"),
                rec.h("ZIUT")
            ));
        }
    }
    let rel = "cavp/ecdsa/KeyPair.rsp";
    for rec in records(run, rel) {
        // Each curve's block opens with a record of its count, `N = 10`.
        let (Some((c, _)), Some(d)) = (rec.curve(), rec.get("d")) else {
            continue;
        };
        run.check(
            Vector,
            rel,
            &["ec-base", c.name, &h(d)],
            &format!("{} {}", rec.h("Qx"), rec.h("Qy")),
        );
    }
    // A key's validity: on the curve, the spec answers its own point.
    let rel = "cavp/ecdsa/PKV.rsp";
    for rec in records(run, rel) {
        let Some((c, _)) = rec.curve() else {
            continue;
        };
        let (x, y) = (rec.h("Qx"), rec.h("Qy"));
        let got = run.ask(Vector, &["ec-mul", c.name, "01", &x, &y]);
        let ok = rec.s("Result").starts_with('P');
        let want = if ok {
            format!("{} {}", fixed(&x, c.len), fixed(&y, c.len))
        } else {
            "offcurve".to_owned()
        };
        if got != want {
            run.fail(format!(
                "{rel}: ec-mul {} 01 {x} {y}\n  spec: {got}\n  want: {want}",
                c.name
            ));
        }
    }
    let rel = "aws-lc/crypto/fipsmodule/ec/ec_scalar_base_mult_tests.txt";
    for rec in records(run, rel) {
        let Some(c) = curve(rec.s("Curve")) else {
            continue;
        };
        // aws-lc writes the point at infinity as (0, 0).
        let (x, y) = (fixed(rec.s("X"), c.len), fixed(rec.s("Y"), c.len));
        let zero = hex(&vec![0; c.len]);
        let want = if x == zero && y == zero {
            "infinity".to_owned()
        } else {
            format!("{x} {y}")
        };
        run.check(Vector, rel, &["ec-base", c.name, &rec.h("N")], &want);
    }
    for c in CURVES {
        let file = format!("ecdh_{}_ecpoint_test", c.wycheproof);
        for (_, t) in wycheproof(run, &file) {
            let Some((x, y)) = point(&unhex(js(&t, "public")), c.len) else {
                continue;
            };
            let got = run.ask(Vector, &["ec-mul", c.name, &jh(&t, "private"), &x, &y]);
            let ok = match js(&t, "result") {
                "valid" => pair(&got, c.len).map(|(x, _)| x) == Some(&jh(&t, "shared")),
                "invalid" => got == "offcurve" || got == "infinity",
                "acceptable" => true,
                r => panic!(
                    "spec-tests: {}: no Wycheproof result {r:?}",
                    label(&file, &t)
                ),
            };
            if !ok {
                run.fail(format!(
                    "{}: ec-mul {} {x} {y}\n  spec: {got}\n  want: {} {}",
                    label(&file, &t),
                    c.name,
                    jh(&t, "shared"),
                    js(&t, "result")
                ));
            }
        }
    }

    for c in CURVES {
        for _ in 0..run.random {
            let ours = nist_key(run, c);
            let peer = nist_key(run, c);
            let d = hex(ours.to_scalar().as_ref());
            let (qx, qy) = point(ours.public_key().as_ref(), c.len).unwrap();
            run.check(
                Rind,
                "random",
                &["ec-base", c.name, &d],
                &format!("{qx} {qy}"),
            );
            let (px, py) = point(peer.public_key().as_ref(), c.len).unwrap();
            let shared = ours.agree(peer.public_key().as_ref()).unwrap();
            let got = run.ask(Rind, &["ec-mul", c.name, &d, &px, &py]);
            if pair(&got, c.len).map(|(x, _)| x) != Some(&hex(shared.as_ref())) {
                run.fail(format!(
                    "random: ec-mul {} {d} {px} {py}\n  spec: {got}\n  want: {}",
                    c.name,
                    hex(shared.as_ref())
                ));
            }
        }
    }
}

fn ecdsa(run: &mut Run) {
    let rel = "cavp/ecdsa/SigVer.rsp";
    for rec in records(run, rel) {
        let Some((c, Some(hash))) = rec.curve() else {
            continue;
        };
        if hash != if c.len == 32 { "SHA-256" } else { "SHA-384" } {
            continue;
        }
        let words = w(&[
            &"ecdsa-verify".to_owned(),
            &c.name.to_owned(),
            &rec.h("Qx"),
            &rec.h("Qy"),
            &rec.h("Msg"),
            &rec.h("R"),
            &rec.h("S"),
        ]);
        let want = if rec.s("Result").starts_with('P') {
            "valid"
        } else {
            "invalid"
        };
        verdict(run, rel, &r(&words), want, &["offcurve"]);
    }
    for c in CURVES {
        let file = format!("ecdsa_{}_sha{}_p1363_test", c.wycheproof, 8 * c.len);
        for (g, t) in wycheproof(run, &file) {
            let sig = unhex(js(&t, "sig"));
            if sig.len() != 2 * c.len {
                continue;
            }
            let key = &g["publicKey"];
            let words = w(&[
                &"ecdsa-verify".to_owned(),
                &c.name.to_owned(),
                &jh(key, "wx"),
                &jh(key, "wy"),
                &jh(&t, "msg"),
                &hex(&sig[..c.len]),
                &hex(&sig[c.len..]),
            ]);
            verdict(
                run,
                &label(&file, &t),
                &r(&words),
                js(&t, "result"),
                &["offcurve"],
            );
        }
    }
    // Signing from a given nonce, with the digest cut to the order's length.
    let rel = "aws-lc/crypto/fipsmodule/ecdsa/ecdsa_sign_tests.txt";
    for rec in records(run, rel) {
        let Some(c) = curve(rec.s("Curve")) else {
            continue;
        };
        let e = rec.bytes("Digest");
        let e = hex(&e[..e.len().min(c.len)]);
        run.check(
            Vector,
            rel,
            &["ecdsa-sign", c.name, &rec.h("Private"), &rec.h("K"), &e],
            &format!("{} {}", fixed(rec.s("R"), c.len), fixed(rec.s("S"), c.len)),
        );
    }

    for c in CURVES {
        for _ in 0..run.random {
            let scalar = nist_key(run, c);
            let key = rind::ecdsa::KeyPair::from_scalar_and_public_key(
                c.sign,
                scalar.to_scalar().as_ref(),
                scalar.public_key().as_ref(),
            )
            .unwrap();
            let d = hex(key.to_scalar().as_ref());
            let (qx, qy) = point(key.public_key().as_ref(), c.len).unwrap();
            run.check(
                Rind,
                "random",
                &["ec-base", c.name, &d],
                &format!("{qx} {qy}"),
            );
            let m = run.rng.message(200);
            // rind's signature verifies under the spec.
            let sig = key.sign(&m).unwrap();
            let sig = sig.as_ref();
            let (r0, s0) = (hex(&sig[..c.len]), hex(&sig[c.len..]));
            run.check(
                Rind,
                "random",
                &["ecdsa-verify", c.name, &qx, &qy, &hex(&m), &r0, &s0],
                "1",
            );
            // The spec's signature, from a random nonce from 1 to n - 1,
            // verifies under rind. Only an r or s of 0, with negligible odds,
            // would let the spec answer `none`.
            let k = hex(nist_key(run, c).to_scalar().as_ref());
            let e = hex(rind::digest::digest(c.hash, &m).as_ref());
            let got = run.ask(Rind, &["ecdsa-sign", c.name, &d, &k, &e]);
            let public = rind::ecdsa::PublicKey::new(c.verify, key.public_key().as_ref()).unwrap();
            let ok = pair(&got, c.len).is_some_and(|(r1, s1)| {
                public.verify(&m, &[unhex(r1), unhex(s1)].concat()).is_ok()
            });
            if !ok {
                run.fail(format!(
                    "random: ecdsa-sign {} {d} {k} {e}\n  spec: {got}\n  rind refuses it",
                    c.name
                ));
            }
            // A changed message verifies under neither.
            let mut bad = m.clone();
            bad.push(run.rng.u64() as u8);
            let want = if public.verify(&bad, sig).is_ok() {
                "1"
            } else {
                "0"
            };
            run.check(
                Rind,
                "random",
                &["ecdsa-verify", c.name, &qx, &qy, &hex(&bad), &r0, &s0],
                want,
            );
        }
    }
}

// ## Curve25519

fn x25519(run: &mut Run) {
    let file = "x25519_test";
    for (_, t) in wycheproof(run, file) {
        if unhex(js(&t, "public")).len() != 32 || unhex(js(&t, "private")).len() != 32 {
            continue;
        }
        run.check(
            Vector,
            &label(file, &t),
            &["x25519", &jh(&t, "private"), &jh(&t, "public")],
            &jh(&t, "shared"),
        );
    }
    let base = hex(&[[9u8].as_slice(), &[0; 31]].concat());
    for _ in 0..run.random {
        let k = run.rng.bytes(32);
        let u = run.rng.bytes(32);
        let key = rind::agreement::PrivateKey::from_scalar(&rind::agreement::X25519, &k).unwrap();
        run.check(
            Rind,
            "random",
            &["x25519", &hex(&k), &base],
            &hex(key.public_key().as_ref()),
        );
        // rind refuses exactly a peer of small order, whose shared secret
        // the spec computes as zero, and never returns that secret.
        let want = match key.agree(&u) {
            Ok(shared) if shared.as_ref() == [0; 32] => {
                run.fail(format!(
                    "random: rind's x25519 returns zero for {}",
                    hex(&u)
                ));
                continue;
            }
            Ok(shared) => hex(shared.as_ref()),
            Err(_) => hex(&[0; 32]),
        };
        run.check(Rind, "random", &["x25519", &hex(&k), &hex(&u)], &want);
    }
}

fn ed25519(run: &mut Run) {
    run.source("small order");
    run.check(Vector, "small order", &["ed25519-small-order"], "1");
    let file = "ed25519_test";
    for (g, t) in wycheproof(run, file) {
        let key = jh(&g["publicKey"], "pk");
        verdict(
            run,
            &label(file, &t),
            &["ed25519-verify", &key, &jh(&t, "msg"), &jh(&t, "sig")],
            js(&t, "result"),
            &["badkey"],
        );
    }
    let rel = "aws-lc/crypto/fipsmodule/curve25519/ed25519_tests.txt";
    for rec in records(run, rel) {
        let seed = hex(&rec.bytes("PRIV")[..32]);
        let (key, m, sig) = (rec.h("PUB"), rec.h("MESSAGE"), rec.h("SIG"));
        run.check(Vector, rel, &["ed25519-public", &seed], &key);
        run.check(Vector, rel, &["ed25519-sign", &seed, &m], &sig);
        run.check(Vector, rel, &["ed25519-verify", &key, &m, &sig], "1");
    }
    // CCTV's edge cases, which carry no verdict: rind's must be the spec's,
    // and its theorems' refusal of a key of small order, before it verifies,
    // which `edSmallOrderY` lists.
    let rel = "cctv/ed25519/ed25519vectors.json";
    run.source(rel);
    let json: Value =
        serde_json::from_str(&std::fs::read_to_string(run.path(rel)).unwrap()).unwrap();
    let cases = run.sample(json.as_array().unwrap().clone());
    for t in cases {
        let (key, sig) = (unhex(js(&t, "key")), unhex(js(&t, "sig")));
        let m = js(&t, "msg").as_bytes();
        let rind = rind::ed25519::PublicKey::new(&key).and_then(|k| k.verify(m, &sig));
        let small = run.ask(Vector, &["ed25519-small-key", &hex(&key)]);
        let got = run.ask(Vector, &["ed25519-verify", &hex(&key), &hex(m), &hex(&sig)]);
        let known =
            matches!(small.as_str(), "0" | "1") && matches!(got.as_str(), "0" | "1" | "badkey");
        // The spec's small-order list must refuse exactly the keys rind's
        // key constructor refuses as small-order, noncanonical aliases too.
        let rind_small = matches!(
            rind::ed25519::PublicKey::new(&key),
            Err(rind::Error::KeyRejected(ref k)) if k.to_string() == "a small-order point"
        );
        if !known || (small == "1") != rind_small || (small == "0" && got == "1") != rind.is_ok() {
            run.fail(format!(
                "{rel} #{}: ed25519-verify\n  spec: {got}, small order {small}\n  rind: {rind:?}",
                t["number"]
            ));
        }
    }

    for _ in 0..run.random {
        let seed = run.rng.bytes(32);
        let m = run.rng.message(500);
        let key = rind::ed25519::KeyPair::from_seed(&seed).unwrap();
        let public = hex(key.public_key().as_ref());
        let sig = key.sign(&m);
        run.check(Rind, "random", &["ed25519-public", &hex(&seed)], &public);
        run.check(
            Rind,
            "random",
            &["ed25519-sign", &hex(&seed), &hex(&m)],
            &hex(sig.as_ref()),
        );
        run.check(
            Rind,
            "random",
            &["ed25519-verify", &public, &hex(&m), &hex(sig.as_ref())],
            "1",
        );
        let mut bad = sig.as_ref().to_vec();
        let at = run.rng.below(64);
        bad[at] ^= 1 << run.rng.below(8);
        let want = match key.public_key().verify(&m, &bad) {
            Ok(()) => "1",
            Err(_) => "0",
        };
        run.check(
            Rind,
            "random",
            &["ed25519-verify", &public, &hex(&m), &hex(&bad)],
            want,
        );
    }
}

// ## RSA

/// A DER length and the rest, from `der` after a tag.
fn der_len(der: &[u8]) -> (usize, &[u8]) {
    match der[0] {
        n if n < 0x80 => (n as usize, &der[1..]),
        n => {
            let k = (n & 0x7f) as usize;
            let len = der[1..1 + k].iter().fold(0, |a, &b| a << 8 | b as usize);
            (len, &der[1 + k..])
        }
    }
}

/// The modulus and exponent of a PKCS#1 `RSAPublicKey`.
fn rsa_components(der: &[u8]) -> (Vec<u8>, Vec<u8>) {
    assert_eq!(der[0], 0x30);
    let (_, body) = der_len(&der[1..]);
    let mut ints = Vec::new();
    let mut rest = body;
    for _ in 0..2 {
        assert_eq!(rest[0], 0x02);
        let (len, tail) = der_len(&rest[1..]);
        ints.push(tail[..len].to_vec());
        rest = &tail[len..];
    }
    (ints.remove(0), ints.remove(0))
}

fn rsa(run: &mut Run) {
    let mut files: Vec<(String, &str)> = Vec::new();
    for bits in [2048, 3072, 4096, 8192] {
        for sha in [256, 384, 512] {
            files.push((format!("rsa_signature_{bits}_sha{sha}_test"), "pkcs1"));
        }
    }
    for bits in [1024, 1536, 2048, 3072, 4096] {
        files.push((format!("rsa_pkcs1_{bits}_sig_gen_test"), "pkcs1"));
    }
    for name in [
        "2048_sha256_mgf1_0",
        "2048_sha256_mgf1_32",
        "2048_sha384_mgf1_48",
        "3072_sha256_mgf1_32",
        "4096_sha256_mgf1_32",
        "4096_sha384_mgf1_48",
        "4096_sha512_mgf1_32",
        "4096_sha512_mgf1_64",
        "misc",
    ] {
        files.push((format!("rsa_pss_{name}_test"), "pss"));
    }
    for (file, scheme) in files {
        for (g, t) in wycheproof(run, &file) {
            let Some(op) = hash_name(js(&g, "sha")) else {
                continue;
            };
            let key = if g["publicKey"].is_object() {
                &g["publicKey"]
            } else {
                &g["privateKey"]
            };
            let (n, e) = (jh(key, "modulus"), jh(key, "publicExponent"));
            let (m, s) = (jh(&t, "msg"), jh(&t, "sig"));
            let label = label(&file, &t);
            if scheme == "pkcs1" {
                verdict(
                    run,
                    &label,
                    &["rsa-pkcs1-verify", op, &n, &e, &m, &s],
                    js(&t, "result"),
                    &[],
                );
            } else {
                // The spec's MGF1 hashes with the message's hash.
                if g["mgf"] != "MGF1" || hash_name(js(&g, "mgfSha")) != Some(op) {
                    continue;
                }
                let slen = jn(&g, "sLen").to_string();
                verdict(
                    run,
                    &label,
                    &["rsa-pss-verify", op, &n, &e, &m, &s, &slen],
                    js(&t, "result"),
                    &[],
                );
            }
        }
    }

    use rind::rsa::{sign, verify};
    let schemes: [(
        &str,
        &str,
        &rind::rsa::SigningAlgorithm,
        &rind::rsa::VerificationAlgorithm,
        usize,
    ); 6] = [
        (
            "pkcs1",
            "sha256",
            &sign::PKCS1_SHA256,
            &verify::PKCS1_SHA256,
            32,
        ),
        (
            "pkcs1",
            "sha384",
            &sign::PKCS1_SHA384,
            &verify::PKCS1_SHA384,
            48,
        ),
        (
            "pkcs1",
            "sha512",
            &sign::PKCS1_SHA512,
            &verify::PKCS1_SHA512,
            64,
        ),
        ("pss", "sha256", &sign::PSS_SHA256, &verify::PSS_SHA256, 32),
        ("pss", "sha384", &sign::PSS_SHA384, &verify::PSS_SHA384, 48),
        ("pss", "sha512", &sign::PSS_SHA512, &verify::PSS_SHA512, 64),
    ];
    if run.random == 0 {
        return;
    }
    // Key generation is slow: two keys serve every case.
    let keys = [
        rind::rsa::KeyPair::generate(rind::rsa::KeySize::Rsa2048).unwrap(),
        rind::rsa::KeyPair::generate(rind::rsa::KeySize::Rsa3072).unwrap(),
    ];
    for (scheme, op, sign, verify, hlen) in schemes {
        for i in 0..run.random {
            let key = &keys[i % 2];
            let (n, e) = rsa_components(key.public_key().as_ref());
            let (n, e) = (hex(&n), hex(&e));
            let m = run.rng.message(300);
            let sig = key.sign(sign, &m).unwrap();
            let mut bad = sig.as_ref().to_vec();
            let at = run.rng.below(bad.len());
            bad[at] ^= 1 << run.rng.below(8);
            if let Err(e) = key.public_key().verify(verify, &m, sig.as_ref()) {
                run.fail(format!(
                    "random: rind refuses its own {op} signature: {e:?}"
                ));
            }
            for s in [sig.as_ref(), &bad] {
                let want = match key.public_key().verify(verify, &m, s) {
                    Ok(()) => "1",
                    Err(_) => "0",
                };
                let (m, s) = (hex(&m), hex(s));
                if scheme == "pkcs1" {
                    run.check(
                        Rind,
                        "random",
                        &["rsa-pkcs1-verify", op, &n, &e, &m, &s],
                        want,
                    );
                } else {
                    run.check(
                        Rind,
                        "random",
                        &["rsa-pss-verify", op, &n, &e, &m, &s, &hlen.to_string()],
                        want,
                    );
                }
            }
        }
    }
}

// ## ML-KEM

/// ML-KEM, one parameter set. SymCrypt's spec takes most of a second over a
/// key generation or decapsulation, so without `full` each vector file runs
/// a sample of `MLKEM_SAMPLE`, and the random tests a quarter of the others'
/// cases.
fn mlkem<A: rind::kem::Algorithm>(run: &mut Run, set: &str) {
    let k = set.parse::<usize>().unwrap() / 256;
    let file = format!("mlkem_{set}_keygen_seed_test");
    let cases = wycheproof(run, &file);
    for (_, t) in run.sample_n(cases, MLKEM_SAMPLE) {
        let seed = unhex(js(&t, "seed"));
        run.check(
            Vector,
            &label(&file, &t),
            &["mlkem-keygen", set, &hex(&seed[..32]), &hex(&seed[32..])],
            &format!("{} {}", jh(&t, "ek"), jh(&t, "dk")),
        );
    }
    let file = format!("mlkem_{set}_encaps_test");
    let cases = wycheproof(run, &file);
    for (_, t) in run.sample_n(cases, MLKEM_SAMPLE) {
        // The spec takes keys only of the set's length.
        if unhex(js(&t, "ek")).len() != 384 * k + 32 {
            continue;
        }
        let want = if valid(&t) {
            format!("{} {}", jh(&t, "K"), jh(&t, "c"))
        } else {
            "badkey".to_owned()
        };
        run.check(
            Vector,
            &label(&file, &t),
            &["mlkem-encaps", set, &jh(&t, "ek"), &jh(&t, "m")],
            &want,
        );
    }
    let file = format!("mlkem_{set}_semi_expanded_decaps_test");
    for (_, t) in wycheproof(run, &file) {
        // Nor decapsulation keys and ciphertexts of other lengths.
        if unhex(js(&t, "dk")).len() != 768 * k + 96 || unhex(js(&t, "c")).len() != expected_c(set)
        {
            continue;
        }
        let want = if valid(&t) {
            jh(&t, "K")
        } else {
            "badkey".to_owned()
        };
        run.check(
            Vector,
            &label(&file, &t),
            &["mlkem-decaps", set, &jh(&t, "dk"), &jh(&t, "c")],
            &want,
        );
    }
    // Key generation from a seed, then decapsulation: CCTV's strcmp,
    // FIPS 203's, and implicit rejection's.
    let file = format!("mlkem_{set}_test");
    let cases: Vec<_> = wycheproof(run, &file)
        .into_iter()
        .filter(|(g, t)| {
            // A seed or ciphertext of another length is an invalid case: the
            // spec takes two seeds of 32 bytes, and the set's ciphertexts.
            js(g, "type") == "MLKEMTest"
                && unhex(js(t, "seed")).len() == 64
                && unhex(js(t, "c")).len() == expected_c(set)
        })
        .collect();
    for (_, t) in run.sample_n(cases, MLKEM_SAMPLE) {
        let seed = unhex(js(&t, "seed"));
        let label = label(&file, &t);
        let got = run.ask(
            Vector,
            &["mlkem-keygen", set, &hex(&seed[..32]), &hex(&seed[32..])],
        );
        let (ek, dk) = got.split_once(' ').unwrap();
        if ek != jh(&t, "ek") {
            run.fail(format!(
                "{label}: mlkem-keygen\n  spec: {ek}\n  want: {}",
                jh(&t, "ek")
            ));
        }
        let dk = dk.to_owned();
        run.check(
            Vector,
            &label,
            &["mlkem-decaps", set, &dk, &jh(&t, "c")],
            &jh(&t, "K"),
        );
    }

    let random = if run.full {
        run.random
    } else {
        run.random.div_ceil(4)
    };
    for _ in 0..random {
        mlkem_random::<A>(run, set);
    }
}

/// The most cases an ML-KEM vector file runs without `full`.
const MLKEM_SAMPLE: usize = 10;

fn expected_c(set: &str) -> usize {
    match set {
        "512" => 768,
        "768" => 1088,
        _ => 1568,
    }
}

/// rind has no seeded key generation or encapsulation, so each direction
/// pairs one side's: the spec encapsulates to rind's key, which decapsulates
/// it, and rind encapsulates to the spec's key, which the spec decapsulates.
fn mlkem_random<A: rind::kem::Algorithm>(run: &mut Run, set: &str) {
    use shake::{ExtendableOutput, Update};
    let dk = rind::kem::DecapsulationKey::<A>::generate().unwrap();
    let ek = hex(dk.public_key().as_ref());
    let m = hex(&run.rng.bytes(32));
    let got = run.ask(Rind, &["mlkem-encaps", set, &ek, &m]);
    match got.split_once(' ') {
        Some((k, c)) => {
            let ct = rind::kem::Ciphertext::<A>::new(&unhex(c)).unwrap();
            let want = hex(dk.decapsulate(&ct).as_ref());
            if k != want {
                run.fail(format!(
                    "random: mlkem-encaps {set} {ek} {m}\n  spec: {k}\n  rind decapsulates {want}"
                ));
            }
        }
        None => run.fail(format!(
            "random: mlkem-encaps {set} {ek} {m}\n  spec: {got}"
        )),
    }

    let (d, z) = (hex(&run.rng.bytes(32)), hex(&run.rng.bytes(32)));
    let got = run.ask(Rind, &["mlkem-keygen", set, &d, &z]);
    let (ek, dk) = got.split_once(' ').unwrap();
    let (c, k) = rind::kem::EncapsulationKey::<A>::new(&unhex(ek))
        .unwrap()
        .encapsulate()
        .unwrap();
    run.check(
        Rind,
        "random",
        &["mlkem-decaps", set, dk, &hex(c.as_ref())],
        &hex(k.as_ref()),
    );
    // A changed ciphertext: implicit rejection's key, J(z || c) =
    // SHAKE256(z || c, 32) of FIPS 203 Algorithm 18, with the z the spec's
    // key generation took: only a changed ciphertext that re-encrypts to
    // itself would decapsulate otherwise, and its odds are negligible.
    let mut bad = c.as_ref().to_vec();
    let at = run.rng.below(bad.len());
    bad[at] ^= 1;
    let mut j = shake::Shake256::default();
    j.update(&unhex(&z));
    j.update(&bad);
    let mut want = [0u8; 32];
    j.finalize_xof_into(&mut want);
    run.check(
        Rind,
        "random (changed ciphertext)",
        &["mlkem-decaps", set, dk, &hex(&bad)],
        &hex(&want),
    );
}
