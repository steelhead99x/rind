// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;

pub(crate) trait CavpSink {
    fn on_meta(&mut self, meta: &str);
    fn on_value(&mut self, name: &str, value: Value<'_>);
}

#[derive(Debug)]
pub(crate) struct Value<'a>(&'a str);

impl Value<'_> {
    pub(crate) fn bytes(&self) -> Vec<u8> {
        if self.0.len().is_multiple_of(2) {
            return hex::decode(self.0).unwrap();
        }
        let mut buf = self.0.to_string();
        buf.insert(0, '0');
        hex::decode(buf).unwrap()
    }

    pub(crate) fn int(&self) -> u64 {
        self.0.parse::<u64>().unwrap()
    }

    pub(crate) fn str(&self) -> &str {
        self.0
    }
}

/// Feeds `sink` the CAVP vector file at `filename`, relative to this crate's
/// directory, so the tests run from any directory, as the iOS simulator's do.
pub(crate) fn process_cavp(filename: impl AsRef<Path>, sink: &mut dyn CavpSink) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(filename);
    let f = File::open(&path).unwrap_or_else(|_| panic!("cannot open {}", path.display()));
    for line in BufReader::new(f).lines() {
        let line = line.unwrap();
        // Some of NIST's files end their lines with CRLF.
        let line = line.strip_suffix('\r').unwrap_or(&line);

        match line.chars().next() {
            Some('[') => {
                let right = line.rfind(']').expect("missing ] for meta");
                sink.on_meta(&line[1..right]);
                continue;
            }
            Some('#') => {
                println!("{line}");
                continue;
            }
            None => continue,
            _ => {}
        };

        if let Some(equal_idx) = line.find(" = ") {
            let name = &line[..equal_idx];
            let value = &line[equal_idx + 3..];

            sink.on_value(name, Value(value));
        } else {
            sink.on_value(line, Value(""));
        }
    }
}

/// Reads every test from the Wycheproof vector file `name`.
pub(crate) fn wycheproof<T: serde::de::DeserializeOwned>(name: &str) -> Vec<T> {
    #[derive(serde::Deserialize)]
    struct TestGroup<T> {
        tests: Vec<T>,
    }

    let tests: Vec<T> = wycheproof_groups::<TestGroup<T>>(name)
        .into_iter()
        .flat_map(|g| g.tests)
        .collect();
    assert!(!tests.is_empty(), "{name} has no tests");
    tests
}

/// Reads every test group from the Wycheproof vector file `name`, for tests
/// that need a group's fields.
pub(crate) fn wycheproof_groups<G: serde::de::DeserializeOwned>(name: &str) -> Vec<G> {
    #[derive(serde::Deserialize)]
    struct TestFile<G> {
        #[serde(rename = "testGroups")]
        groups: Vec<G>,
    }

    let path = format!(
        "{}/../thirdparty/wycheproof/testvectors_v1/{name}",
        env!("CARGO_MANIFEST_DIR")
    );
    let file = File::open(&path).unwrap_or_else(|_| panic!("cannot open {path}"));
    let file: TestFile<G> =
        serde_json::from_reader(BufReader::new(file)).expect("invalid test JSON");
    assert!(!file.groups.is_empty(), "{path} has no test groups");
    file.groups
}

/// Reads the test groups of the ACVP vector set `name`, which
/// `admin/sync-acvp` trims to the groups rind runs.
pub(crate) fn acvp(name: &str) -> Vec<serde_json::Value> {
    #[derive(serde::Deserialize)]
    struct VectorSet {
        #[serde(rename = "testGroups")]
        groups: Vec<serde_json::Value>,
    }

    let path = format!(
        "{}/../thirdparty/acvp/{name}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let file = File::open(&path).unwrap_or_else(|_| panic!("cannot open {path}"));
    let set: VectorSet = serde_json::from_reader(BufReader::new(file)).expect("invalid ACVP JSON");
    assert!(!set.groups.is_empty(), "{path} has no test groups");
    set.groups
}

/// Typed access to an ACVP test group's or test's fields, which panics on a
/// missing or mistyped field.
pub(crate) trait Acvp {
    /// The tests of this group.
    fn tests(&self) -> &[serde_json::Value];
    /// The hex field `name`, decoded.
    fn hex(&self, name: &str) -> Vec<u8>;
    /// The integer field `name`, which ACVP writes as a number or a string,
    /// and which must fit in a `usize`.
    fn int(&self, name: &str) -> usize;
    /// The string field `name`.
    fn str(&self, name: &str) -> &str;
    /// The boolean field `name`.
    fn flag(&self, name: &str) -> bool;
}

impl Acvp for serde_json::Value {
    fn tests(&self) -> &[serde_json::Value] {
        self["tests"].as_array().expect("group has no tests")
    }

    fn hex(&self, name: &str) -> Vec<u8> {
        hex::decode(self.str(name)).unwrap_or_else(|_| panic!("{name} is not hex"))
    }

    fn int(&self, name: &str) -> usize {
        match &self[name] {
            Self::Number(n) => n.as_u64().and_then(|n| usize::try_from(n).ok()),
            Self::String(s) => s.parse().ok(),
            _ => None,
        }
        .unwrap_or_else(|| panic!("{name} is not an integer"))
    }

    fn str(&self, name: &str) -> &str {
        self[name]
            .as_str()
            .unwrap_or_else(|| panic!("{name} is not a string"))
    }

    fn flag(&self, name: &str) -> bool {
        self[name]
            .as_bool()
            .unwrap_or_else(|| panic!("{name} is not a boolean"))
    }
}

/// Steps an AES Monte Carlo test's key, per AESAVS section 6.4: XORs it with
/// the low bits of a round's last two outputs, as many as the key holds.
pub(crate) fn aes_mct_next_key(key: &mut [u8], second_last: &[u8; 16], last: &[u8; 16]) {
    let outputs = [&second_last[..], &last[..]].concat();
    let start = 32 - key.len();
    for (k, o) in key.iter_mut().zip(&outputs[start..]) {
        *k ^= o;
    }
}

/// A Wycheproof test's expected result.
#[derive(Clone, Copy, Debug, PartialEq, serde::Deserialize)]
#[serde(rename_all = "lowercase")]
pub(crate) enum Expected {
    Valid,
    Invalid,
    Acceptable,
}

/// The path of `name` in C2SP's CCTV vectors.
pub(crate) fn cctv(name: &str) -> String {
    format!("{}/../thirdparty/cctv/{name}", env!("CARGO_MANIFEST_DIR"))
}

/// Reads a CCTV file of `name = hex` lines, each blank-line-separated record
/// as its values in order.
pub(crate) fn cctv_records(name: &str) -> Vec<Vec<(String, Vec<u8>)>> {
    let path = cctv(name);
    let text = std::fs::read_to_string(&path).unwrap_or_else(|_| panic!("cannot open {path}"));
    let records: Vec<_> = text
        .split("\n\n")
        .map(|record| {
            record
                .lines()
                .map(|line| {
                    let (name, value) = line.split_once(" = ").expect("expected `name = value`");
                    (name.to_string(), hex::decode(value).unwrap_or_default())
                })
                .collect::<Vec<_>>()
        })
        .filter(|record| !record.is_empty())
        .collect();
    assert!(!records.is_empty(), "{path} has no records");
    records
}

/// The first value named `name` in a CCTV record.
pub(crate) fn cctv_value<'a>(record: &'a [(String, Vec<u8>)], name: &str) -> &'a [u8] {
    &record
        .iter()
        .find(|(n, _)| n == name)
        .unwrap_or_else(|| panic!("record lacks {name}"))
        .1
}

pub(crate) mod bignum;
mod binsec;
pub(crate) mod file_test;
