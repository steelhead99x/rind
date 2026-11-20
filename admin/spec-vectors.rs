//! Prints a Lean file that runs the executable specs in `proofs/Rind/`
//! (`HashSpec`, `Sha2`, `Sha3`) on cases and fails if one disagrees: the
//! published vectors in `thirdparty/vectors/` (CAVP and Wycheproof), with the
//! vector's own answer, and random inputs from a fixed seed, with rind's
//! output. A spec that agrees with every published case but drifts on others
//! is caught by the random ones, and a spec that disagrees with rind or a
//! standard fails `admin/prove`.
//!
//! The run is a fixed sample, to stay within the `lean` job's budget; with
//! `SPEC_VECTORS=full`, every vector the specs can run in reasonable time (an
//! uncapped sweep took 45 minutes in the interpreter, so messages above 16 KiB
//! and PBKDF2 above 1024 iterations stay out) and many more random inputs,
//! which the nightly `prove` run uses.
//!
//! Usage: run by `admin/prove`, from the repository root, built against rind's
//! rlib; its output is `admin/spec-vectors.lean` with the cases filled in.

use std::fmt::Write as _;
use std::fs;
use std::num::NonZeroU32;

use rind::digest::legacy::SHA1;
use rind::digest::{SHA3_256, SHA3_384, SHA3_512, SHA256, SHA384, SHA512, SHA512_256, digest};
use rind::{hkdf, hmac, pbkdf2};

const VECTORS: &str = "thirdparty/vectors";

/// One case: the spec to run, its inputs, and the answer it must give.
struct Case {
    alg: &'static str,
    name: String,
    a: Vec<u8>,
    b: Vec<u8>,
    c: Vec<u8>,
    n: u32,
    m: u32,
    want: Vec<u8>,
}

impl Case {
    fn new(alg: &'static str, name: String, want: Vec<u8>) -> Self {
        Self {
            alg,
            name,
            a: vec![],
            b: vec![],
            c: vec![],
            n: 0,
            m: 0,
            want,
        }
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().fold(String::new(), |mut s, b| {
        let _ = write!(s, "{b:02x}");
        s
    })
}

fn unhex(s: &str) -> Vec<u8> {
    assert!(s.len() % 2 == 0, "odd hex {s}");
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
        .collect()
}

/// xorshift64*, from a fixed seed, so the cases are the same on every run.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn bytes(&mut self, len: usize) -> Vec<u8> {
        (0..len).map(|_| (self.next() >> 32) as u8).collect()
    }

    /// Fewer than `n` random bytes.
    fn upto(&mut self, n: u64) -> Vec<u8> {
        let len = self.below(n) as usize;
        self.bytes(len)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// The `(Len, Msg, expected)` triples of a CAVP `.rsp` file, `want` naming the
/// expected-output field.
fn rsp(path: &str, want: &str) -> Vec<(usize, Vec<u8>, Vec<u8>)> {
    let text = fs::read_to_string(format!("{VECTORS}/cavp/{path}")).unwrap();
    let (mut len, mut msg, mut out) = (None, None, Vec::new());
    for line in text.lines() {
        let Some((k, v)) = line.split_once(" = ") else {
            continue;
        };
        match k {
            "Len" => len = Some(v.parse().unwrap()),
            "Msg" => msg = Some(unhex(v)),
            k if k == want => {
                out.push((len.take().unwrap(), msg.take().unwrap(), unhex(v)));
            }
            _ => {}
        }
    }
    assert!(!out.is_empty(), "no cases in {path}");
    out
}

/// Every `step`th element, from the first.
fn sample<T>(all: Vec<T>, step: usize) -> impl Iterator<Item = T> {
    all.into_iter().step_by(step)
}

/// A Wycheproof file's tests as maps of each test's fields, read from its
/// pretty-printed lines: a test starts at its `tcId`, and its scalar fields
/// are one per line.
fn wycheproof(file: &str) -> Vec<Vec<(String, String)>> {
    let text = fs::read_to_string(format!("{VECTORS}/wycheproof/testvectors_v1/{file}")).unwrap();
    let mut tests: Vec<Vec<(String, String)>> = Vec::new();
    for line in text.lines() {
        let line = line.trim().trim_end_matches(',');
        let Some((k, v)) = line.split_once("\": ") else {
            continue;
        };
        let k = k.trim_start_matches('"');
        let v = v.trim().trim_matches('"');
        if k == "tcId" {
            tests.push(Vec::new());
        }
        if let Some(t) = tests.last_mut() {
            t.push((k.to_string(), v.to_string()));
        }
    }
    assert!(!tests.is_empty(), "no tests in {file}");
    tests
}

fn field<'a>(t: &'a [(String, String)], k: &str) -> &'a str {
    t.iter()
        .find(|(f, _)| f == k)
        .map(|(_, v)| v.as_str())
        .unwrap_or_else(|| panic!("no {k}"))
}

fn main() {
    let full = std::env::var("SPEC_VECTORS").is_ok_and(|v| v == "full");
    let mut cases: Vec<Case> = Vec::new();

    // CAVP hashes: the short and long messages, each file's sample.
    let hashes: [(&'static str, &str, &str); 7] = [
        ("sha256", "sha2/SHA256", "MD"),
        ("sha384", "sha2/SHA384", "MD"),
        ("sha512", "sha2/SHA512", "MD"),
        ("sha512_256", "sha2/SHA512_256", "MD"),
        ("sha3_256", "sha3/SHA3_256", "MD"),
        ("sha3_384", "sha3/SHA3_384", "MD"),
        ("sha3_512", "sha3/SHA3_512", "MD"),
    ];
    for (alg, stem, out) in hashes {
        for kind in ["ShortMsg", "LongMsg"] {
            let all = rsp(&format!("{stem}{kind}.rsp"), out);
            let step = if full { 1 } else { all.len().div_ceil(6) };
            for (i, (len, msg, md)) in sample(all, step).enumerate() {
                // A bit-oriented case or a very long one is out of the
                // interpreter's reach in the sample.
                if len % 8 != 0 || len > 8 * if full { 16384 } else { 4096 } {
                    continue;
                }
                let mut c = Case::new(alg, format!("cavp {stem}{kind} #{i}"), md);
                c.a = msg[..len / 8].to_vec();
                cases.push(c);
            }
        }
    }

    // CAVP HMAC: the L = 20, 32, 48, 64 sections are HMAC-SHA1, -SHA256,
    // -SHA384, and -SHA512; the Mac is truncated to Tlen.
    let text = fs::read_to_string(format!("{VECTORS}/cavp/hmac/HMAC.rsp")).unwrap();
    let mut section = "";
    let (mut key, mut msg) = (Vec::new(), Vec::new());
    let mut seen = std::collections::HashMap::<&str, usize>::new();
    for line in text.lines() {
        if let Some(l) = line.strip_prefix("[L=") {
            section = match l.trim_end_matches(']') {
                "20" => "hmac_sha1",
                "32" => "hmac_sha256",
                "48" => "hmac_sha384",
                "64" => "hmac_sha512",
                _ => "",
            };
        } else if let Some(v) = line.strip_prefix("Key = ") {
            key = unhex(v);
        } else if let Some(v) = line.strip_prefix("Msg = ") {
            msg = unhex(v);
        } else if let Some(v) = line.strip_prefix("Mac = ") {
            if section.is_empty() {
                continue;
            }
            let n = seen.entry(section).or_default();
            *n += 1;
            if !full && *n % 40 != 1 {
                continue;
            }
            let mut c = Case::new(
                match section {
                    "hmac_sha1" => "hmac_sha1",
                    "hmac_sha256" => "hmac_sha256",
                    "hmac_sha384" => "hmac_sha384",
                    _ => "hmac_sha512",
                },
                format!("cavp hmac {section} #{n}"),
                unhex(v),
            );
            c.a = key.clone();
            c.b = msg.clone();
            cases.push(c);
        }
    }

    // Wycheproof's valid HMAC, HKDF, and PBKDF2 tests, with the RFC 5869,
    // RFC 6070, and RFC 7914 ones among them. PBKDF2's iteration counts above
    // the cap are out of the interpreter's reach.
    let iteration_cap = if full { 1024 } else { 64 };
    for (alg, file) in [
        ("hmac_sha1", "hmac_sha1_test.json"),
        ("hmac_sha256", "hmac_sha256_test.json"),
        ("hmac_sha384", "hmac_sha384_test.json"),
        ("hmac_sha512", "hmac_sha512_test.json"),
    ] {
        let tests = wycheproof(file);
        let step = if full { 1 } else { tests.len().div_ceil(8) };
        for t in sample(tests, step) {
            if field(&t, "result") != "valid" {
                continue;
            }
            let mut c = Case::new(
                alg,
                format!("wycheproof {file} #{}", field(&t, "tcId")),
                unhex(field(&t, "tag")),
            );
            c.a = unhex(field(&t, "key"));
            c.b = unhex(field(&t, "msg"));
            cases.push(c);
        }
    }
    for (alg, file) in [
        ("hkdf_sha1", "hkdf_sha1_test.json"),
        ("hkdf_sha256", "hkdf_sha256_test.json"),
        ("hkdf_sha384", "hkdf_sha384_test.json"),
        ("hkdf_sha512", "hkdf_sha512_test.json"),
    ] {
        let tests = wycheproof(file);
        let step = if full { 1 } else { tests.len().div_ceil(8) };
        for t in sample(tests, step) {
            if field(&t, "result") != "valid" {
                continue;
            }
            let mut c = Case::new(
                alg,
                format!("wycheproof {file} #{}", field(&t, "tcId")),
                unhex(field(&t, "okm")),
            );
            c.a = unhex(field(&t, "ikm"));
            c.b = unhex(field(&t, "salt"));
            c.c = unhex(field(&t, "info"));
            c.n = field(&t, "size").parse().unwrap();
            cases.push(c);
        }
    }
    for (alg, file) in [
        ("pbkdf2_sha1", "pbkdf2_hmacsha1_test.json"),
        ("pbkdf2_sha256", "pbkdf2_hmacsha256_test.json"),
        ("pbkdf2_sha384", "pbkdf2_hmacsha384_test.json"),
        ("pbkdf2_sha512", "pbkdf2_hmacsha512_test.json"),
    ] {
        for t in wycheproof(file) {
            let iterations: u32 = field(&t, "iterationCount").parse().unwrap();
            if field(&t, "result") != "valid" || iterations > iteration_cap {
                continue;
            }
            let mut c = Case::new(
                alg,
                format!("wycheproof {file} #{}", field(&t, "tcId")),
                unhex(field(&t, "dk")),
            );
            c.a = unhex(field(&t, "password"));
            c.b = unhex(field(&t, "salt"));
            c.n = iterations;
            c.m = field(&t, "dkLen").parse().unwrap();
            cases.push(c);
        }
    }

    // Random inputs, compared with rind's output: every length around each
    // hash's block and rate boundaries, then random ones.
    let mut rng = Rng(0x7e57_5eed_dec0_ded5);
    let edge = [
        0, 1, 31, 32, 33, 55, 56, 57, 63, 64, 65, 71, 72, 73, 103, 104, 105, 111, 112, 113, 119,
        120, 127, 128, 129, 135, 136, 137, 143, 144, 200, 255, 256, 257, 300,
    ];
    let randoms = if full { 200 } else { 16 };
    let hashes: [(&'static str, &rind::digest::Algorithm); 8] = [
        ("sha1", &SHA1),
        ("sha256", &SHA256),
        ("sha384", &SHA384),
        ("sha512", &SHA512),
        ("sha512_256", &SHA512_256),
        ("sha3_256", &SHA3_256),
        ("sha3_384", &SHA3_384),
        ("sha3_512", &SHA3_512),
    ];
    for (alg, algorithm) in hashes {
        let lens = edge
            .iter()
            .map(|&l| l as u64)
            .chain((0..randoms).map(|_| rng.below(2000)));
        for (i, len) in lens.collect::<Vec<_>>().into_iter().enumerate() {
            if !full && i % 3 != 0 && i < edge.len() {
                continue;
            }
            let msg = rng.bytes(len as usize);
            let mut c = Case::new(
                alg,
                format!("random {alg} #{i}"),
                digest(algorithm, &msg).as_ref().to_vec(),
            );
            c.a = msg;
            cases.push(c);
        }
    }
    let macs: [(&'static str, &'static rind::hmac::Algorithm); 3] = [
        ("hmac_sha256", &rind::hmac::HMAC_SHA256),
        ("hmac_sha384", &rind::hmac::HMAC_SHA384),
        ("hmac_sha512", &rind::hmac::HMAC_SHA512),
    ];
    let sha1_mac = &rind::hmac::legacy::HMAC_SHA1;
    let macs = macs.into_iter().chain([("hmac_sha1", sha1_mac)]);
    for (alg, algorithm) in macs {
        for i in 0..randoms {
            // Keys across the block size, so the hashed-key branch runs.
            let key = rng.upto(300);
            let msg = rng.upto(400);
            let tag = hmac::sign(&hmac::Key::new(algorithm, &key), &msg);
            let mut c = Case::new(alg, format!("random {alg} #{i}"), tag.as_ref().to_vec());
            c.a = key;
            c.b = msg;
            cases.push(c);
        }
    }
    let kdfs: [(&'static str, &'static hkdf::Algorithm); 3] = [
        ("hkdf_sha256", &hkdf::HKDF_SHA256),
        ("hkdf_sha384", &hkdf::HKDF_SHA384),
        ("hkdf_sha512", &hkdf::HKDF_SHA512),
    ];
    for (alg, algorithm) in kdfs
        .into_iter()
        .chain([("hkdf_sha1", &hkdf::legacy::HKDF_SHA1)])
    {
        for i in 0..randoms {
            let ikm = rng.upto(64);
            let salt = rng.upto(150);
            let info = rng.upto(80);
            // Past one hash output and not a multiple of it.
            let n = 1 + rng.below(200) as usize;
            let prk = hkdf::Salt::new(algorithm, &salt).extract(&ikm).unwrap();
            let mut out = vec![0; n];
            prk.fill(&[&info], &mut out).unwrap();
            let mut c = Case::new(alg, format!("random {alg} #{i}"), out);
            c.a = ikm;
            c.b = salt;
            c.c = info;
            c.n = n as u32;
            cases.push(c);
        }
    }
    let pbkdfs: [(&'static str, &'static pbkdf2::Algorithm); 4] = [
        ("pbkdf2_sha1", &pbkdf2::legacy::PBKDF2_HMAC_SHA1),
        ("pbkdf2_sha256", &pbkdf2::PBKDF2_HMAC_SHA256),
        ("pbkdf2_sha384", &pbkdf2::PBKDF2_HMAC_SHA384),
        ("pbkdf2_sha512", &pbkdf2::PBKDF2_HMAC_SHA512),
    ];
    for (alg, algorithm) in pbkdfs {
        for i in 0..randoms.min(if full { 40 } else { 4 }) {
            let password = rng.upto(150);
            let salt = rng.upto(40);
            let iterations = 1 + rng.below(iteration_cap.min(40) as u64) as u32;
            let m = 1 + rng.below(150) as u32;
            let mut out = vec![0; m as usize];
            pbkdf2::Secret::new(algorithm, &password)
                .derive(NonZeroU32::new(iterations).unwrap(), &salt, &mut out)
                .unwrap();
            let mut c = Case::new(alg, format!("random {alg} #{i}"), out);
            c.a = password;
            c.b = salt;
            c.n = iterations;
            c.m = m;
            cases.push(c);
        }
    }

    // One string literal, which Lean elaborates far faster than a list of
    // thousands of structures.
    let mut data = String::new();
    for c in &cases {
        let _ = writeln!(
            data,
            "{}|{}|{}|{}|{}|{}|{}|{}",
            c.alg,
            c.name,
            hex(&c.a),
            hex(&c.b),
            hex(&c.c),
            c.n,
            c.m,
            hex(&c.want)
        );
    }
    print!(
        "{}",
        include_str!("spec-vectors.lean")
            .replace("@COUNT@", &cases.len().to_string())
            .replace("@DATA@", &data)
    );
}
