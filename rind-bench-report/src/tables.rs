//! The report's tables. `admin/bench-report` is the source; `tests/constants.rs` fails if these drift.

use std::collections::HashSet;
use std::sync::OnceLock;

use crate::format::re_escape;

pub const SLOWER: f64 = 1.1;
pub const BUSY_SHARE: f64 = 0.1;
pub const LEASE_HELD: i32 = 73;
pub const COPY_FAILED: i32 = 74;
pub const REMOTE_DIR: &str = ".cache/rind-bench-report";
pub const REPO: &str = "kixel-ai/rind";
pub const CRITERION_ARGS: &[&str] = &["--noplot", "--warm-up-time", "1", "--measurement-time", "3"];
pub const FONT: &str =
    "-apple-system, BlinkMacSystemFont, 'Segoe UI', Helvetica, Arial, sans-serif";

pub const SPEED_BINS: &[f64] = &[SLOWER, 1.25, 1.5, 2.0, 4.0, 8.0];
pub const SPEED_LABELS: &[&str] = &[
    "fastest, or within 10%",
    "to 1.25×",
    "to 1.5×",
    "to 2×",
    "to 4×",
    "to 8×",
    "over 8×",
];
pub const TIER_BINS: &[f64] = &[0.8, 0.9, 0.98, 1.02, 1.1, 1.25];
pub const TIER_LABELS: &[&str] = &[
    "under 0.8",
    "to 0.9",
    "to 0.98",
    "even",
    "to 1.1",
    "to 1.25",
    "over 1.25",
];
pub const SPEED_COLORS: &[&str] = &[
    "#1a9641", "#74c476", "#c2e07c", "#f9d64a", "#f6a03c", "#e4572e", "#a50f15",
];

pub struct Theme {
    pub name: &'static str,
    pub ink: &'static str,
    pub muted: &'static str,
    pub rule: &'static str,
    pub speed: &'static [&'static str],
    pub tier: &'static [&'static str],
}

pub const THEMES: &[Theme] = &[
    Theme {
        name: "light",
        ink: "#0b0b0b",
        muted: "#52514e",
        rule: "#c3c2b7",
        speed: SPEED_COLORS,
        tier: &[
            "#184f95", "#3987e5", "#b7d3f6", "#f0efec", "#f6c4b5", "#e5735a", "#b3321f",
        ],
    },
    Theme {
        name: "dark",
        ink: "#f0efec",
        muted: "#c3c2b7",
        rule: "#383835",
        speed: SPEED_COLORS,
        tier: &[
            "#6da7ec", "#2a78d6", "#184f95", "#383835", "#8a2f1f", "#c4452c", "#ec7a63",
        ],
    },
];

pub struct HostSpec {
    pub name: &'static str,
    pub jobs: u32,
    pub ssh: Option<&'static str>,
    pub lease: Option<&'static str>,
    pub note: Option<&'static str>,
}

const VPS_VIRGINIA: &str = "OVH VPS in Virginia, 4 shared vCPUs: other tenants add noise that a dedicated host's times lack.";
const VPS_OREGON: &str = "OVH VPS in Oregon, 4 shared vCPUs: other tenants add noise that a dedicated host's times lack.";
const KIXTOP_NOTE: &str = "The maintainer's MacBook, in daily use. Its cores have DIT, which rind sets around each call that handles a secret and the other libraries never set; Known gaps gives its cost.";

pub const HOSTS: &[HostSpec] = &[
    HostSpec {
        name: "nixos",
        jobs: 16,
        ssh: None,
        lease: None,
        note: None,
    },
    HostSpec {
        name: "desktop",
        jobs: 12,
        ssh: None,
        lease: None,
        note: None,
    },
    HostSpec {
        name: "nixos2",
        jobs: 3,
        ssh: None,
        lease: None,
        note: None,
    },
    HostSpec {
        name: "kixtop",
        jobs: 4,
        ssh: None,
        lease: None,
        note: Some(KIXTOP_NOTE),
    },
    HostSpec {
        name: "ovh-iad",
        jobs: 4,
        ssh: Some("root@vps-bcb7229a.vps.ovh.us"),
        lease: Some("/run/lock/moq-perf.lock"),
        note: Some(VPS_VIRGINIA),
    },
    HostSpec {
        name: "ovh-sea",
        jobs: 4,
        ssh: Some("root@vps-39a0ff2a.vps.ovh.us"),
        lease: Some("/run/lock/moq-perf.lock"),
        note: Some(VPS_OREGON),
    },
];

pub fn hosts() -> &'static [HostSpec] {
    HOSTS
}

pub fn host(name: &str) -> Option<&'static HostSpec> {
    HOSTS.iter().find(|h| h.name == name)
}

/// `(row name in rind-bench, library name in the report)`.
pub const LIBRARIES: &[(&str, &str)] = &[
    ("rind", "rind"),
    ("rind-dit-held", "rind-dit-held"),
    ("aws-lc-rs", "aws-lc-rs"),
    ("ring", "ring"),
    ("rustcrypto", "rustcrypto"),
    ("p256-rustcrypto", "rustcrypto"),
    ("p384-rustcrypto", "rustcrypto"),
    ("dalek", "rustcrypto"),
    ("graviola", "graviola"),
    ("libcrux", "libcrux"),
    ("libcrux-ml-kem", "libcrux"),
    ("openssl", "openssl"),
];

pub fn libraries() -> &'static [(&'static str, &'static str)] {
    LIBRARIES
}

pub fn library_of(row: &str) -> &str {
    LIBRARIES
        .iter()
        .find(|(k, _)| *k == row)
        .map(|(_, v)| *v)
        .unwrap_or(row)
}

pub const COLUMNS: &[(&str, &str)] = &[
    ("rind", "rind"),
    ("rind-dit-held", "rind (DIT held)"),
    ("aws-lc-rs", "aws-lc-rs"),
    ("ring", "ring"),
    ("rustcrypto", "RustCrypto + dalek"),
    ("graviola", "graviola"),
    ("libcrux", "libcrux"),
    ("openssl", "OpenSSL"),
];

pub fn columns() -> &'static [(&'static str, &'static str)] {
    COLUMNS
}

pub fn column_name(library: &str) -> &str {
    COLUMNS
        .iter()
        .find(|(k, _)| *k == library)
        .map(|(_, v)| *v)
        .unwrap_or(library)
}

pub const VARIANTS: &[(&str, &str)] = &[("rind-dit-held", "rind")];

pub fn variants() -> &'static [(&'static str, &'static str)] {
    VARIANTS
}

pub fn is_variant(library: &str) -> bool {
    VARIANTS.iter().any(|(k, _)| *k == library)
}

pub fn variant_of(library: &str) -> &str {
    VARIANTS
        .iter()
        .find(|(k, _)| *k == library)
        .map(|(_, v)| *v)
        .unwrap_or(library)
}

const GRAVIOLA_X86: &[&str] = &["aes", "pclmulqdq", "bmi1", "adx", "avx", "avx2"];
const GRAVIOLA_AARCH64: &[&str] = &["neon", "aes", "pmull", "sha2"];

pub fn required_features(library: &str, arch: &str) -> &'static [&'static str] {
    match (library, arch) {
        ("graviola", "x86_64") => GRAVIOLA_X86,
        ("graviola", "aarch64") => GRAVIOLA_AARCH64,
        _ => &[],
    }
}

pub struct CrateList<'a> {
    pub library: &'a str,
    pub crates: &'a [&'a str],
}

const CRATE_RIND: &[&str] = &["rind", "rind-rustls"];
const CRATE_AWS: &[&str] = &["aws-lc-rs", "aws-lc-sys"];
const CRATE_RING: &[&str] = &["ring"];
const CRATE_RUSTCRYPTO: &[&str] = &[
    "aes-gcm",
    "chacha20poly1305",
    "sha2",
    "sha3",
    "hmac",
    "hkdf",
    "p256",
    "p384",
    "p521",
    "rsa",
    "ml-dsa",
    "ml-kem",
    "ed25519-dalek",
    "x25519-dalek",
];
const CRATE_GRAVIOLA: &[&str] = &["graviola", "rustls-graviola"];
const CRATE_LIBCRUX: &[&str] = &[
    "libcrux-aes",
    "libcrux-chacha20poly1305",
    "libcrux-ecdh",
    "libcrux-ecdsa",
    "libcrux-ed25519",
    "libcrux-hkdf",
    "libcrux-hmac",
    "libcrux-ml-dsa",
    "libcrux-ml-kem",
    "libcrux-rsa",
    "libcrux-sha2",
    "libcrux-sha3",
];
const CRATE_OPENSSL: &[&str] = &["openssl", "openssl-sys", "rustls-openssl"];
const CRATE_TLS: &[&str] = &["rustls"];

pub const CRATES: &[CrateList<'static>] = &[
    CrateList {
        library: "rind",
        crates: CRATE_RIND,
    },
    CrateList {
        library: "aws-lc-rs",
        crates: CRATE_AWS,
    },
    CrateList {
        library: "ring",
        crates: CRATE_RING,
    },
    CrateList {
        library: "rustcrypto",
        crates: CRATE_RUSTCRYPTO,
    },
    CrateList {
        library: "graviola",
        crates: CRATE_GRAVIOLA,
    },
    CrateList {
        library: "libcrux",
        crates: CRATE_LIBCRUX,
    },
    CrateList {
        library: "openssl",
        crates: CRATE_OPENSSL,
    },
    CrateList {
        library: "tls",
        crates: CRATE_TLS,
    },
];

pub fn crates_for() -> &'static [CrateList<'static>] {
    CRATES
}

pub const BUILDS: &[(&str, &str)] = &[
    ("rind", "rind"),
    ("aws-lc-rs", "aws-lc-rs"),
    ("ring", "ring"),
    ("rustcrypto", "RustCrypto + dalek"),
    ("graviola", "graviola"),
    ("libcrux", "libcrux"),
    ("openssl", "OpenSSL, the system's, linked dynamically"),
    ("openssl-vendored", "OpenSSL, vendored"),
    ("rustls-rind", "rustls + rind-rustls"),
    ("rustls-aws-lc-rs", "rustls + aws-lc-rs"),
    ("rustls-ring", "rustls + ring"),
];

pub fn builds() -> &'static [(&'static str, &'static str)] {
    BUILDS
}

const CPU_X86: &[&str] = &[
    "adx",
    "aes",
    "avx",
    "avx2",
    "avx512bw",
    "avx512dq",
    "avx512f",
    "avx512ifma",
    "avx512vbmi",
    "avx512vbmi2",
    "avx512vl",
    "bmi2",
    "intel",
    "movbe",
    "pclmulqdq",
    "popcnt",
    "sha",
    "sse4.1",
    "ssse3",
    "vaes",
    "vpclmulqdq",
];
const CPU_AARCH64: &[&str] = &["aes", "dit", "neon", "pmull", "sha2", "sha3"];

pub fn cpu_features(arch: &str) -> &'static [&'static str] {
    match arch {
        "x86_64" => CPU_X86,
        "aarch64" => CPU_AARCH64,
        _ => &[],
    }
}

pub fn known_arch(arch: &str) -> bool {
    matches!(arch, "x86_64" | "aarch64")
}

pub struct TierSpec {
    pub target: &'static str,
    pub portable: bool,
    pub tier: &'static str,
    pub name: &'static str,
}

pub const TIERS: &[TierSpec] = &[
    TierSpec {
        target: "x86_64-unknown-linux-gnu",
        portable: false,
        tier: "",
        name: "x86_64",
    },
    TierSpec {
        target: "x86_64-unknown-linux-gnu",
        portable: true,
        tier: "no-ifma",
        name: "no IFMA",
    },
    TierSpec {
        target: "x86_64-unknown-linux-gnu",
        portable: true,
        tier: "no-avx512",
        name: "no AVX-512",
    },
    TierSpec {
        target: "x86_64-unknown-linux-gnu",
        portable: true,
        tier: "no-adx",
        name: "no ADX",
    },
    TierSpec {
        target: "x86_64-unknown-linux-gnu",
        portable: true,
        tier: "",
        name: "no AVX2",
    },
    TierSpec {
        target: "x86_64-unknown-linux-gnu",
        portable: true,
        tier: "no-avx",
        name: "no AVX",
    },
    TierSpec {
        target: "x86_64-unknown-linux-gnu",
        portable: true,
        tier: "no-aes",
        name: "no AES-NI",
    },
    TierSpec {
        target: "x86_64-unknown-linux-gnu",
        portable: true,
        tier: "no-ssse3",
        name: "SSE2",
    },
    TierSpec {
        target: "aarch64-unknown-linux-gnu",
        portable: false,
        tier: "",
        name: "aarch64",
    },
    TierSpec {
        target: "aarch64-unknown-linux-gnu",
        portable: true,
        tier: "no-sha3",
        name: "no SHA-3",
    },
    TierSpec {
        target: "aarch64-unknown-linux-gnu",
        portable: true,
        tier: "",
        name: "no crypto",
    },
    TierSpec {
        target: "armv7-unknown-linux-gnueabihf",
        portable: false,
        tier: "",
        name: "armv7",
    },
    TierSpec {
        target: "armv7-unknown-linux-gnueabihf",
        portable: true,
        tier: "no-crypto",
        name: "armv7 NEON",
    },
    TierSpec {
        target: "x86_64-unknown-linux-gnu",
        portable: true,
        tier: "generic",
        name: "portable",
    },
];

pub fn tiers() -> &'static [TierSpec] {
    TIERS
}

pub fn tier_name_of(target: &str, portable: bool, tier: &str) -> Option<&'static str> {
    TIERS
        .iter()
        .find(|t| t.target == target && t.portable == portable && t.tier == tier)
        .map(|t| t.name)
}

pub fn tier_names() -> impl Iterator<Item = &'static str> {
    TIERS.iter().map(|t| t.name)
}

pub const BASELINES: &[&str] = &["aws-lc-rs", "ring"];

pub fn baselines() -> &'static [&'static str] {
    BASELINES
}

/// `(row label, regex matched from the start of a nightly benchmark id)`.
pub const TIER_ROWS: &[(&str, &str)] = &[
    ("AES-GCM", r"aes(128|192|256)-gcm(-open)?/"),
    (
        "AES block, AES-CTR",
        r"(aes(128|192|256)-ctr|quic-header-protection/aes(128|256))/",
    ),
    ("AES-CBC", r"aes(128|192|256)-cbc-"),
    ("AES-KW, AES-KWP", r"aes(128|256)-kwp?-"),
    (
        "ChaCha20 (header protection)",
        r"quic-header-protection/chacha20/",
    ),
    (
        "ChaCha20-Poly1305, XChaCha20-Poly1305",
        r"x?chacha20poly1305(-open)?/",
    ),
    ("SHA-1", r"sha1/"),
    ("SHA-256", r"sha256(-updates)?/"),
    ("SHA-384, SHA-512, SHA-512/256", r"sha(384|512|512-256)/"),
    ("SHA-3", r"sha3-"),
    ("MD5", r"md5/"),
    ("HMAC", r"hmac-"),
    ("HKDF", r"hkdf-"),
    ("PBKDF2", r"pbkdf2-"),
    ("X25519", r"x25519-"),
    ("Ed25519", r"ed25519-"),
    ("P-256 ECDH, ECDSA", r"p256-"),
    ("P-384 ECDH, ECDSA", r"p384-"),
    ("P-521 ECDH, ECDSA", r"p521-"),
    ("ML-KEM-768", r"mlkem768-"),
    ("ML-DSA", r"mldsa(44|65|87)-"),
    ("RSA signatures", r"rsa\d+-(pkcs1|pss|load)"),
    ("RSA-OAEP", r"rsa\d+-oaep-"),
    ("JSON Web Tokens", r"jwt-[^/]+/\*/token$"),
    ("rind-rustls handshakes", r"rustls-(full|resumed)-"),
    ("rind-rustls 1 MB transfer", r"rustls-bulk/"),
];

pub const UNRANKED: &[(&str, &str)] = &[
    (
        r"rsa\d+-key-generation",
        "RSA key generation varies too much from run to run to rank",
    ),
    (
        r"jwt-[^/]+/\*/load$",
        "a token's key loading, the part of `token` spent on the key",
    ),
];

const NAMES: &[(&str, &str)] = &[
    (
        "rustls-full-handshake-group/x25519mlkem768",
        "full handshake, X25519MLKEM768",
    ),
    (
        "rustls-full-handshake-group/x25519",
        "full handshake, X25519",
    ),
    (
        "rustls-full-handshake-group/secp256r1",
        "full handshake, P-256",
    ),
    (
        "rustls-full-handshake-key/ed25519",
        "full handshake, Ed25519 certificate",
    ),
    (
        "rustls-full-handshake-key/rsa-2048",
        "full handshake, RSA-2048 certificate",
    ),
    (
        "rustls-resumed-handshake/x25519",
        "resumed handshake, X25519",
    ),
    ("rustls-bulk/aes128-gcm", "1 MB transfer, AES-128-GCM"),
    ("rustls-bulk/aes256-gcm", "1 MB transfer, AES-256-GCM"),
    (
        "rustls-bulk/chacha20poly1305",
        "1 MB transfer, ChaCha20-Poly1305",
    ),
    ("aes128-gcm", "AES-128-GCM seal"),
    ("aes128-gcm-open", "AES-128-GCM open"),
    ("aes256-gcm", "AES-256-GCM seal"),
    ("aes256-gcm-open", "AES-256-GCM open"),
    ("chacha20poly1305", "ChaCha20-Poly1305 seal"),
    ("xchacha20poly1305", "XChaCha20-Poly1305 seal"),
    ("quic-header-protection/aes128", "AES-128 header protection"),
    ("quic-header-protection/aes256", "AES-256 header protection"),
    (
        "quic-header-protection/chacha20",
        "ChaCha20 header protection",
    ),
    ("x25519-ecdh", "X25519"),
    ("p256-ecdh", "P-256 ECDH"),
    ("ed25519-sign", "Ed25519 sign"),
    ("ed25519-verify", "Ed25519 verify"),
    ("p256-ecdsa-sign", "P-256 ECDSA sign"),
    ("p256-ecdsa-verify", "P-256 ECDSA verify"),
    ("sha256", "SHA-256"),
    ("sha512", "SHA-512"),
    ("sha3-256", "SHA3-256"),
    ("sha3-512", "SHA3-512"),
    ("hmac-sha256", "HMAC-SHA256"),
    (
        "hkdf-sha256/extract-expand",
        "HKDF-SHA256 extract and expand",
    ),
    ("hkdf-sha256/expand", "HKDF-SHA256 expand"),
    ("rsa2048-pkcs1-sha256-sign", "RSA-2048 PKCS#1 sign"),
    ("rsa2048-pkcs1-sha256-verify", "RSA-2048 PKCS#1 verify"),
    ("rsa2048-pss-sha256-sign", "RSA-2048 PSS sign"),
    ("rsa2048-pss-sha256-verify", "RSA-2048 PSS verify"),
    ("mlkem768-keygen", "ML-KEM-768 key generation"),
    ("mlkem768-encaps", "ML-KEM-768 encapsulate"),
    ("mlkem768-decaps", "ML-KEM-768 decapsulate"),
    ("mldsa65-keygen", "ML-DSA-65 key generation"),
    ("mldsa65-sign", "ML-DSA-65 sign"),
    ("mldsa65-verify", "ML-DSA-65 verify"),
    ("p384-ecdh", "P-384 ECDH"),
    ("p384-ecdsa-sign", "P-384 ECDSA sign"),
    ("p384-ecdsa-verify", "P-384 ECDSA verify"),
    ("p521-ecdh", "P-521 ECDH"),
    ("p521-ecdsa-sign", "P-521 ECDSA sign"),
    ("p521-ecdsa-verify", "P-521 ECDSA verify"),
];

pub fn row_name(operation: &str) -> String {
    operation.replace("/{lib}", "")
}

pub fn name_of(row: &str) -> Option<&'static str> {
    NAMES.iter().find(|(k, _)| *k == row).map(|(_, v)| *v)
}

/// The report's label for a row, including a message size when the row has one.
pub fn label(row: &str) -> String {
    if let Some((head, size)) = split_size(row) {
        let name = name_of(head).unwrap_or(head);
        format!("{name}, {size}")
    } else {
        name_of(row).unwrap_or(row).to_string()
    }
}

fn split_size(row: &str) -> Option<(&str, String)> {
    let (head, tail) = row.rsplit_once('/')?;
    if head.is_empty() {
        return None;
    }
    let bytes = tail.as_bytes();
    if bytes.last() != Some(&b'B') {
        return None;
    }
    let mut i = 0;
    if i >= bytes.len() || !bytes[i].is_ascii_digit() {
        return None;
    }
    while i < bytes.len() && bytes[i].is_ascii_digit() {
        i += 1;
    }
    let unit = &tail[i..];
    if unit != "B" && unit != "KB" {
        return None;
    }
    Some((head, format!("{} {unit}", &tail[..i])))
}

fn section_ops() -> Vec<(String, Vec<String>)> {
    let mut sections = Vec::new();
    let tls = [
        "rustls-full-handshake-group/x25519mlkem768/{lib}",
        "rustls-full-handshake-group/x25519/{lib}",
        "rustls-full-handshake-group/secp256r1/{lib}",
        "rustls-full-handshake-key/ed25519/{lib}",
        "rustls-full-handshake-key/rsa-2048/{lib}",
        "rustls-resumed-handshake/x25519/{lib}",
        "rustls-bulk/aes128-gcm/{lib}",
        "rustls-bulk/aes256-gcm/{lib}",
        "rustls-bulk/chacha20poly1305/{lib}",
    ];
    sections.push((
        "TLS 1.3 with rustls".to_string(),
        tls.into_iter().map(str::to_string).collect(),
    ));
    let aeads = [
        "aes128-gcm",
        "aes128-gcm-open",
        "aes256-gcm",
        "aes256-gcm-open",
        "chacha20poly1305",
        "xchacha20poly1305",
    ];
    let sizes = ["32B", "1350B", "16KB"];
    let mut aead_ops = Vec::new();
    for aead in aeads {
        for size in sizes {
            aead_ops.push(format!("{aead}/{{lib}}/{size}"));
        }
    }
    sections.push(("AEADs".to_string(), aead_ops));
    let mut quic = Vec::new();
    for cipher in ["aes128", "aes256", "chacha20"] {
        quic.push(format!("quic-header-protection/{cipher}/{{lib}}"));
    }
    sections.push(("QUIC header protection".to_string(), quic));
    sections.push((
        "Key agreement".to_string(),
        ["x25519-ecdh/{lib}", "p256-ecdh/{lib}"]
            .into_iter()
            .map(str::to_string)
            .collect(),
    ));
    sections.push((
        "Signatures".to_string(),
        [
            "ed25519-sign/{lib}",
            "ed25519-verify/{lib}",
            "p256-ecdsa-sign/{lib}",
            "p256-ecdsa-verify/{lib}",
        ]
        .into_iter()
        .map(str::to_string)
        .collect(),
    ));
    let mut hashes = Vec::new();
    for hash in ["sha256", "sha512", "sha3-256", "sha3-512"] {
        for size in ["64B", "1350B", "16KB"] {
            hashes.push(format!("{hash}/{{lib}}/{size}"));
        }
    }
    hashes.push("hmac-sha256/{lib}/64B".to_string());
    hashes.push("hmac-sha256/{lib}/1350B".to_string());
    hashes.push("hkdf-sha256/extract-expand/{lib}".to_string());
    hashes.push("hkdf-sha256/expand/{lib}".to_string());
    sections.push(("Hashes and KDFs".to_string(), hashes));
    sections.push((
        "RSA".to_string(),
        [
            "rsa2048-pkcs1-sha256-sign/{lib}",
            "rsa2048-pkcs1-sha256-verify/{lib}",
            "rsa2048-pss-sha256-sign/{lib}",
            "rsa2048-pss-sha256-verify/{lib}",
        ]
        .into_iter()
        .map(str::to_string)
        .collect(),
    ));
    sections.push((
        "ML-KEM".to_string(),
        [
            "mlkem768-keygen/{lib}",
            "mlkem768-encaps/{lib}",
            "mlkem768-decaps/{lib}",
        ]
        .into_iter()
        .map(str::to_string)
        .collect(),
    ));
    sections.push((
        "ML-DSA".to_string(),
        [
            "mldsa65-keygen/{lib}",
            "mldsa65-sign/{lib}",
            "mldsa65-verify/{lib}",
        ]
        .into_iter()
        .map(str::to_string)
        .collect(),
    ));
    sections.push((
        "P-384 and P-521".to_string(),
        [
            "p384-ecdh/{lib}",
            "p384-ecdsa-sign/{lib}",
            "p384-ecdsa-verify/{lib}",
            "p521-ecdh/{lib}",
            "p521-ecdsa-sign/{lib}",
            "p521-ecdsa-verify/{lib}",
        ]
        .into_iter()
        .map(str::to_string)
        .collect(),
    ));
    sections
}

pub fn sections() -> &'static [(String, Vec<String>)] {
    static SECTIONS: OnceLock<Vec<(String, Vec<String>)>> = OnceLock::new();
    SECTIONS.get_or_init(section_ops)
}

pub fn operations() -> &'static [String] {
    static OPS: OnceLock<Vec<String>> = OnceLock::new();
    OPS.get_or_init(|| {
        sections()
            .iter()
            .flat_map(|(_, ops)| ops.iter().cloned())
            .collect()
    })
}

pub fn operation_regex(refused: &HashSet<&str>) -> String {
    let lib = if refused.is_empty() {
        "[^/]+".to_string()
    } else {
        let rows = LIBRARIES
            .iter()
            .filter(|(_, name)| !refused.contains(name))
            .map(|(row, _)| re_escape(row))
            .collect::<Vec<_>>()
            .join("|");
        format!("({rows})")
    };
    let placeholder = re_escape("{lib}");
    let ops = operations()
        .iter()
        .map(|op| re_escape(op).replace(&placeholder, &lib))
        .collect::<Vec<_>>()
        .join("|");
    format!("^({ops})$")
}

/// The operation template and the rind-bench row of a criterion id.
pub fn operation_of(full_id: &str) -> Option<(String, String)> {
    for op in operations() {
        if let Some(library) = match_lib(op, full_id) {
            return Some((op.clone(), library.to_string()));
        }
    }
    None
}

fn match_lib<'a>(op: &str, full_id: &'a str) -> Option<&'a str> {
    let (pre, post) = op.split_once("{lib}")?;
    if !full_id.starts_with(pre) || !full_id.ends_with(post) {
        return None;
    }
    let mid = &full_id[pre.len()..full_id.len() - post.len()];
    if mid.is_empty() || mid.contains('/') {
        return None;
    }
    Some(mid)
}

pub fn criterion_args() -> &'static [&'static str] {
    CRITERION_ARGS
}

pub fn repo() -> &'static str {
    REPO
}
