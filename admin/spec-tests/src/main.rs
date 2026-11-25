//! Tests the Lean specs `proofs/README.md`'s trust base trusts as
//! transliterations of their standards: runs each, as the compiled
//! `spec-server` answers, on its algorithm's published vectors from
//! `thirdparty/vectors/`, and on random inputs from a fixed seed compared with
//! rind's output, and fails on any disagreement. `admin/prove spec-tests` runs it.
//!
//! Usage: `spec-tests <spec-server> <vectors dir> <seed> <random cases per test> [full]`
//!
//! Each section of `cases` runs on its own thread with its own server, and
//! its own random source, from the seed and the section's name, so a seed
//! reproduces each section's inputs alone (`SPEC_TESTS_ONLY=<section>,...`
//! runs only those). The exceptions, which no seed reproduces, are what rind
//! offers no seeded API for and draws from its own generator: RSA and ML-KEM
//! keys, rind's ML-KEM encapsulations, ECDSA nonces, RSA-PSS salts, and
//! XChaCha20-Poly1305 nonces. A failure prints its request, cut short past
//! 400 characters. Without `full`, a vector
//! file of more than `SAMPLE` cases runs every k-th, and the slowest specs
//! run a sample of their own, as `cases` says of each; with it, every vector
//! the filters in `cases` admit runs.

mod cases;

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, ExitCode, Stdio};
use std::sync::Mutex;
use std::time::Instant;

/// The most cases a vector file runs without `full`.
pub const SAMPLE: usize = 400;

/// Every request the server answers, so a test that stops running fails.
const SPECS: &[&str] = &[
    "sha1",
    "sha256",
    "sha256-s2n",
    "sha384",
    "sha384-s2n",
    "sha512",
    "sha512-s2n",
    "sha512_256",
    "sha512_256-s2n",
    "sha3_256",
    "sha3_384",
    "sha3_512",
    "shake128",
    "shake256",
    "sha3_256-symcrypt",
    "shake128-symcrypt",
    "hmac",
    "hkdf",
    "pbkdf2",
    "chacha20",
    "chacha20-s2n",
    "hchacha20",
    "poly1305",
    "poly1305-s2n",
    "chacha20poly1305-seal",
    "chacha20poly1305-open",
    "chacha20poly1305-s2n-seal",
    "chacha20poly1305-s2n-open",
    "xchacha20poly1305-seal",
    "xchacha20poly1305-open",
    "hp-chacha20",
    "hp-aes",
    "aes-encrypt",
    "aes-decrypt",
    "aes-gcm-seal",
    "aes-gcm-open",
    "aes-ctr",
    "aes-cbc-encrypt",
    "aes-cbc-decrypt",
    "aes-kw-wrap",
    "aes-kw-unwrap",
    "aes-kwp-wrap",
    "aes-kwp-unwrap",
    "ec-mul",
    "ec-base",
    "ecdsa-sign",
    "ecdsa-verify",
    "ed25519-public",
    "ed25519-sign",
    "ed25519-verify",
    "ed25519-small-order",
    "ed25519-small-key",
    "x25519",
    "rsa-pkcs1-verify",
    "rsa-pss-verify",
    "mlkem-keygen",
    "mlkem-encaps",
    "mlkem-decaps",
];

/// The specs that run on no random inputs: rind offers no SHAKE or Poly1305
/// alone, the SymCrypt sponge is proven the byte sponge `sha3_*` and
/// `shake*` run, HChaCha20 runs inside XChaCha20-Poly1305, and the small-order
/// list is a constant, which CCTV's keys test against rind.
const NO_RANDOM: &[&str] = &[
    "shake128",
    "shake256",
    "sha3_256-symcrypt",
    "shake128-symcrypt",
    "hchacha20",
    "poly1305",
    "poly1305-s2n",
    "ed25519-small-order",
    "ed25519-small-key",
];

/// Whether `w` is a word an answer may hold: lowercase hex, `-` for no
/// bytes, or one of the words the server answers where a spec gives no
/// value. Checking every answer here keeps a malformed one, `error`
/// included, from passing a comparison that decodes it leniently.
fn answer_word(w: &str) -> bool {
    matches!(w, "-" | "none" | "offcurve" | "badkey" | "infinity")
        || (!w.is_empty() && w.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')))
}

/// The spec server, a child process answering a line per request.
struct Server {
    child: Child,
    input: BufWriter<ChildStdin>,
    output: BufReader<ChildStdout>,
}

impl Server {
    fn start(path: &Path) -> Result<Self, String> {
        let mut child = Command::new(path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .map_err(|e| format!("cannot run {}: {e}", path.display()))?;
        let input = BufWriter::new(child.stdin.take().unwrap());
        let output = BufReader::new(child.stdout.take().unwrap());
        Ok(Self {
            child,
            input,
            output,
        })
    }

    /// Closes the server's input, which ends it, and fails unless it then
    /// writes nothing more and exits cleanly.
    fn finish(self) -> Option<String> {
        let Self {
            mut child,
            input,
            mut output,
        } = self;
        drop(input);
        // One byte tells EOF from more output, without waiting on a server
        // that keeps writing.
        let extra = match std::io::Read::read(&mut output, &mut [0; 1]) {
            Ok(0) => None,
            Ok(_) => Some("the server wrote after its last answer".to_owned()),
            Err(e) => Some(format!("the server's output: {e}")),
        };
        if extra.is_some() {
            let _ = child.kill();
            let _ = child.wait();
            return extra;
        }
        match child.wait() {
            Ok(status) if status.success() => None,
            Ok(status) => Some(format!("the server exited with {status}")),
            Err(e) => Some(format!("the server: {e}")),
        }
    }

    fn ask(&mut self, words: &[&str]) -> String {
        writeln!(self.input, "{}", words.join(" ")).unwrap();
        self.input.flush().unwrap();
        let mut line = String::new();
        self.output.read_line(&mut line).unwrap();
        // An answer ends with its newline; one cut short by the server's
        // exit does not.
        let Some(line) = line.strip_suffix('\n') else {
            panic!("spec-tests: {} answered {line:?} unterminated", words[0]);
        };
        let line = line.to_owned();
        if line.is_empty() || !line.split(' ').all(answer_word) {
            panic!("spec-tests: {} answered {line:?}", words[0]);
        }
        line
    }
}

/// Where a case comes from.
#[derive(Clone, Copy)]
pub enum From {
    /// A published vector, with its expected answer or, where it carries
    /// none, rind's.
    Vector,
    /// A random input, with rind's answer.
    Rind,
}

/// A section's state: its server, its random source, and what ran.
pub struct Run {
    server: Server,
    pub rng: Rng,
    pub random: usize,
    pub full: bool,
    pub vectors: PathBuf,
    counts: BTreeMap<String, [usize; 2]>,
    /// The time each spec took, in seconds.
    times: BTreeMap<String, f64>,
    failures: Vec<String>,
    /// The vector cases each source file or document ran, so that a parser
    /// that silently skips a whole file fails the run.
    sources: BTreeMap<String, usize>,
    source: Option<String>,
}

impl Run {
    /// Names the source the vector cases asked from here on come from.
    pub fn source(&mut self, name: &str) {
        self.sources.entry(name.to_owned()).or_default();
        self.source = Some(name.to_owned());
    }

    /// Asks the server `words` and checks its answer is `want`.
    pub fn check(&mut self, from: From, label: &str, words: &[&str], want: &str) {
        let got = self.ask(from, words);
        if got != want {
            // A section's first failure prints its whole request, which a
            // random input rind drew itself needs to be replayed.
            let request = if self.failures.is_empty() {
                words.join(" ")
            } else {
                trim(words)
            };
            self.failures
                .push(format!("{label}: {request}\n  spec: {got}\n  want: {want}"));
        }
    }

    /// The server's answer to `words`, counted, for a check of its own.
    pub fn ask(&mut self, from: From, words: &[&str]) -> String {
        self.counts.entry(words[0].to_owned()).or_default()[from as usize] += 1;
        if let (From::Vector, Some(source)) = (from, &self.source) {
            *self.sources.get_mut(source).unwrap() += 1;
        }
        let start = Instant::now();
        let got = self.server.ask(words);
        *self.times.entry(words[0].to_owned()).or_default() += start.elapsed().as_secs_f64();
        got
    }

    /// Records a failed check of an answer `ask` returned.
    pub fn fail(&mut self, message: String) {
        self.failures.push(message);
    }

    /// The cases of a vector file to run: all with `full`, otherwise every
    /// k-th of a file of more than `SAMPLE`.
    pub fn sample<T>(&self, cases: Vec<T>) -> Vec<T> {
        self.sample_n(cases, SAMPLE)
    }

    /// The cases to run of a spec too slow for `SAMPLE`: all with `full`,
    /// otherwise every k-th of more than `n`.
    pub fn sample_n<T>(&self, cases: Vec<T>, n: usize) -> Vec<T> {
        if self.full || cases.len() <= n {
            return cases;
        }
        let step = cases.len().div_ceil(n);
        cases.into_iter().step_by(step).collect()
    }

    pub fn path(&self, rel: &str) -> PathBuf {
        self.vectors.join(rel)
    }
}

/// A request for a message, cut short.
pub fn trim(words: &[&str]) -> String {
    let mut s = words.join(" ");
    if s.len() > 400 {
        let mut at = 400;
        while !s.is_char_boundary(at) {
            at -= 1;
        }
        s.truncate(at);
        s.push_str("...");
    }
    s
}

/// SplitMix64, for random inputs a seed reproduces.
pub struct Rng(u64);

impl Rng {
    pub fn u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }

    /// A number below `n`.
    pub fn below(&mut self, n: usize) -> usize {
        (self.u64() % n as u64) as usize
    }

    pub fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.u64() as u8).collect()
    }

    /// An AES key of a random length.
    pub fn aes_key(&mut self) -> Vec<u8> {
        let n = [16, 24, 32][self.below(3)];
        self.bytes(n)
    }

    /// Bytes of a random length below `max`, short lengths as likely as long.
    pub fn message(&mut self, max: usize) -> Vec<u8> {
        let n = if self.u64().is_multiple_of(2) {
            self.below(65)
        } else {
            self.below(max)
        };
        self.bytes(n)
    }
}

/// `bytes` as the server reads them: hex, `-` for none.
pub fn hex(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        return "-".to_owned();
    }
    let mut s = String::with_capacity(2 * bytes.len());
    for b in bytes {
        write!(s, "{b:02x}").unwrap();
    }
    s
}

/// The bytes hex spells, or a quoted string's own. Hex of odd length is a
/// number's, as CAVP writes some, with its leading zero left out.
pub fn unhex(s: &str) -> Vec<u8> {
    let s = s.trim();
    if let Some(q) = s.strip_prefix('"').and_then(|s| s.strip_suffix('"')) {
        return q.as_bytes().to_vec();
    }
    let padded;
    let s = if s.len() % 2 == 1 {
        padded = format!("0{s}");
        &padded
    } else {
        s
    };
    (0..s.len())
        .step_by(2)
        .map(|i| {
            u8::from_str_radix(&s[i..i + 2], 16)
                .unwrap_or_else(|_| panic!("spec-tests: bad hex {s:?}"))
        })
        .collect()
}

/// What a section reports.
struct Report {
    counts: BTreeMap<String, [usize; 2]>,
    times: BTreeMap<String, f64>,
    failures: Vec<String>,
    sources: BTreeMap<String, usize>,
    took: f64,
}

fn main() -> ExitCode {
    // The paths stay OS strings, which need not be UTF-8.
    let args: Vec<std::ffi::OsString> = std::env::args_os().collect();
    if !(5..=6).contains(&args.len()) || (args.len() == 6 && args[5] != "full") {
        eprintln!(
            "usage: spec-tests <spec-server> <vectors dir> <seed> <random cases per test> [full]"
        );
        return ExitCode::from(2);
    }
    let server = PathBuf::from(&args[1]);
    let vectors = PathBuf::from(&args[2]);
    let number = |a: &std::ffi::OsString| a.to_str().and_then(|a| a.parse::<u64>().ok());
    let (Some(seed), Some(random)) = (number(&args[3]), number(&args[4])) else {
        eprintln!("spec-tests: the seed and random cases must be numbers");
        return ExitCode::from(2);
    };
    let random = random as usize;
    let full = args.len() == 6;
    let only = match std::env::var("SPEC_TESTS_ONLY") {
        Ok(o) => Some(o),
        Err(std::env::VarError::NotPresent) => None,
        Err(std::env::VarError::NotUnicode(_)) => {
            eprintln!("spec-tests: SPEC_TESTS_ONLY is not Unicode");
            return ExitCode::from(2);
        }
    };
    if let Some(o) = &only
        && let Some(bad) = o
            .split(',')
            .find(|o| !cases::SECTIONS.iter().any(|(name, _)| name == o))
    {
        eprintln!("spec-tests: no section {bad:?} in SPEC_TESTS_ONLY");
        return ExitCode::from(2);
    }
    let sections: Vec<_> = cases::SECTIONS
        .iter()
        .filter(|(name, _)| {
            only.as_ref()
                .is_none_or(|o| o.split(',').any(|o| o == *name))
        })
        .collect();

    // The slowest sections first, so the longest one starts at once.
    let queue = Mutex::new(sections.iter().enumerate());
    let threads = std::thread::available_parallelism()
        .map_or(1, |n| n.get())
        .min(sections.len());
    let mut reports: Vec<(usize, &str, Report)> = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..threads)
            .map(|_| {
                scope.spawn(|| {
                    let mut done = Vec::new();
                    loop {
                        let Some((i, (name, section))) = queue.lock().unwrap().next() else {
                            break;
                        };
                        // Each section's inputs depend on the seed and its name alone.
                        let mut h = seed;
                        for b in name.bytes() {
                            h = (h ^ b as u64).wrapping_mul(0x100000001b3);
                        }
                        let process = match Server::start(&server) {
                            Ok(process) => process,
                            Err(e) => {
                                let report = Report {
                                    counts: BTreeMap::new(),
                                    times: BTreeMap::new(),
                                    failures: vec![format!("{name}: {e}")],
                                    sources: BTreeMap::new(),
                                    took: 0.0,
                                };
                                done.push((i, *name, report));
                                continue;
                            }
                        };
                        let mut run = Run {
                            server: process,
                            rng: Rng(h),
                            random,
                            full,
                            vectors: vectors.clone(),
                            counts: BTreeMap::new(),
                            times: BTreeMap::new(),
                            failures: Vec::new(),
                            sources: BTreeMap::new(),
                            source: None,
                        };
                        let start = Instant::now();
                        // A panic, such as a request the server cannot
                        // parse, fails the section but keeps what it found.
                        if std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            section(&mut run)
                        }))
                        .is_err()
                        {
                            run.failures.push(format!("{name}: the section panicked"));
                        }
                        let took = start.elapsed().as_secs_f64();
                        let mut failures = run.failures;
                        if run.counts.is_empty() && run.sources.is_empty() {
                            failures.push(format!("{name}: the section ran nothing"));
                        }
                        // Each section runs its own random cases of what it
                        // runs on vectors, so another section's of the same
                        // spec, such as another ML-KEM set's, cannot stand in.
                        for (spec, [v, r]) in &run.counts {
                            if *v > 0
                                && *r == 0
                                && random > 0
                                && !NO_RANDOM.contains(&spec.as_str())
                            {
                                failures.push(format!("{name}: {spec} ran on no random inputs"));
                            }
                        }
                        failures.extend(run.server.finish().map(|e| format!("{name}: {e}")));
                        let report = Report {
                            counts: run.counts,
                            times: run.times,
                            failures,
                            sources: run.sources,
                            took,
                        };
                        done.push((i, *name, report));
                    }
                    done
                })
            })
            .collect();
        workers
            .into_iter()
            .flat_map(|w| w.join().unwrap())
            .collect()
    });
    reports.sort_by_key(|(i, _, _)| *i);

    let mut counts: BTreeMap<String, [usize; 2]> = BTreeMap::new();
    let mut times: BTreeMap<String, f64> = BTreeMap::new();
    let mut failures = Vec::new();
    println!(
        "spec-tests: seed {seed}, {random} random cases per test{}",
        if full { ", unsampled" } else { "" }
    );
    let mut ok = true;
    for (_, name, report) in reports {
        println!("spec-tests: {name} took {:.1}s", report.took);
        for (k, [v, r]) in report.counts {
            let e = counts.entry(k).or_default();
            e[0] += v;
            e[1] += r;
        }
        for (k, s) in report.times {
            *times.entry(k).or_default() += s;
        }
        failures.extend(report.failures);
        for (source, n) in report.sources {
            if n == 0 {
                eprintln!("spec-tests: {source} ran no vectors");
                ok = false;
            }
        }
    }

    println!(
        "{:<28} {:>8} {:>8} {:>8}",
        "spec", "vectors", "rind", "seconds"
    );
    for spec in SPECS {
        let [v, r] = counts.get(*spec).copied().unwrap_or_default();
        let t = times.get(*spec).copied().unwrap_or_default();
        println!("{spec:<28} {v:>8} {r:>8} {t:>8.1}");
        // Every spec runs on published vectors, and on random inputs unless
        // `NO_RANDOM` lists it.
        if only.is_none() && (v == 0 || (r == 0 && random > 0 && !NO_RANDOM.contains(spec))) {
            eprintln!("spec-tests: {spec} ran on too few cases");
            ok = false;
        }
    }
    for spec in counts.keys() {
        if !SPECS.contains(&spec.as_str()) {
            eprintln!("spec-tests: {spec} is not in SPECS");
            ok = false;
        }
    }
    for failure in &failures {
        eprintln!("spec-tests: {failure}");
    }
    if !failures.is_empty() {
        eprintln!("spec-tests: {} disagreements", failures.len());
        ok = false;
    }
    if ok {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
