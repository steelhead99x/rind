// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The break build (`--features __break_tests`) shows each self-test's
//! failure path, as a lab asks to see: `RIND_FIPS_BREAK` names a test whose
//! input the module corrupts, and the module must print that test's name and
//! abort, so nothing after it runs.
//!
//! Each case runs a trigger test of this binary again in a child, which
//! loads the module with the variable set.
#![cfg(rind_fips_module)]
#![cfg(feature = "__break_tests")]

use std::os::unix::process::ExitStatusExt;
use std::process::{Command, ExitStatus};

/// Every known-answer test, by the name the module prints, and the
/// integrity test.
const SELF_TESTS: [&str; 26] = [
    "integrity",
    "sha1",
    "sha256",
    "sha512",
    "sha3",
    "hmac",
    "hkdf",
    "pbkdf2",
    "aes_encrypt",
    "aes_decrypt",
    "aes_gcm_seal",
    "aes_gcm_open",
    "drbg",
    "ecdsa_sign",
    "ecdsa_verify",
    "ecdh",
    "ed25519_sign",
    "ed25519_verify",
    "rsa_sign",
    "rsa_verify",
    "ml_kem_keygen",
    "ml_kem_encaps",
    "ml_kem_decaps",
    "ml_dsa_keygen",
    "ml_dsa_sign",
    "ml_dsa_verify",
];

/// Runs trigger test `trigger` in a child with `RIND_FIPS_BREAK=name`,
/// returning how it exited and its standard error.
fn run(trigger: &str, name: &str) -> (ExitStatus, String) {
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", trigger, "--test-threads=1", "--nocapture"])
        .env("RIND_FIPS_BREAK", name)
        .output()
        .unwrap();
    (
        output.status,
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// Asserts that breaking `name` makes `trigger` abort at that test, printing
/// its name, before the trigger's own output.
fn assert_breaks(trigger: &str, name: &str) {
    const SIGABRT: i32 = 6;
    let (status, stderr) = run(trigger, name);
    assert_eq!(
        status.signal(),
        Some(SIGABRT),
        "breaking {name} did not abort {trigger}: {status}: {stderr}"
    );
    assert!(
        stderr.contains(&format!("rind-fips: {name} self-test failed")),
        "breaking {name} failed {trigger} otherwise: {stderr}"
    );
    assert!(
        !stderr.contains("trigger done"),
        "{trigger} went on after {name} failed: {stderr}"
    );
}

/// What the children run: every self-test, on demand.
#[test]
fn trigger_self_test() {
    rind_fips::self_test();
    eprintln!("trigger done");
}

#[test]
fn every_self_test_fails_when_broken() {
    for name in SELF_TESTS {
        assert_breaks("trigger_self_test", name);
    }
}

/// Every pairwise consistency test, by the name the module prints, and the
/// trigger that generates a key pair it checks.
const PCTS: [(&str, &str); 6] = [
    ("pct_ecdh", "trigger_ecdh_generate"),
    ("pct_ml_kem", "trigger_ml_kem_generate"),
    ("pct_ecdsa", "trigger_ecdsa_generate"),
    ("pct_ed25519", "trigger_ed25519_generate"),
    ("pct_rsa", "trigger_rsa_generate"),
    ("pct_ml_dsa", "trigger_ml_dsa_generate"),
];

#[test]
fn trigger_ecdh_generate() {
    use rind_fips::agreement::{ECDH_P256, PrivateKey};
    PrivateKey::generate(&ECDH_P256).unwrap();
    eprintln!("trigger done");
}

#[test]
fn trigger_ml_kem_generate() {
    use rind_fips::kem::{DecapsulationKey, ML_KEM_768};
    DecapsulationKey::generate(&ML_KEM_768).unwrap();
    eprintln!("trigger done");
}

#[test]
fn trigger_ecdsa_generate() {
    use rind_fips::signature::{EcdsaKeyPair, sign};
    EcdsaKeyPair::generate(&sign::ECDSA_P256_SHA256_ASN1).unwrap();
    eprintln!("trigger done");
}

#[test]
fn trigger_ed25519_generate() {
    rind_fips::signature::Ed25519KeyPair::generate().unwrap();
    eprintln!("trigger done");
}

#[test]
fn trigger_rsa_generate() {
    use rind_fips::{rsa::KeySize, signature::RsaKeyPair};
    RsaKeyPair::generate(KeySize::Rsa2048).unwrap();
    eprintln!("trigger done");
}

#[test]
fn trigger_ml_dsa_generate() {
    use rind_fips::signature::sign::{MlDsa44, MlDsaKeyPair};
    MlDsaKeyPair::<MlDsa44>::generate().unwrap();
    eprintln!("trigger done");
}

#[test]
fn every_pairwise_test_fails_when_broken() {
    for (name, trigger) in PCTS {
        assert_breaks(trigger, name);
    }
}

/// What the children run: one thread draws and exits, wiping its DRBG
/// itself, and another draws and is still running as the process exits.
#[test]
fn trigger_exit_with_a_running_thread() {
    std::thread::spawn(|| rind_fips::rand::fill(&mut [0; 16]).unwrap())
        .join()
        .unwrap();
    let (drawn, wait) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        rind_fips::rand::fill(&mut [0; 16]).unwrap();
        drawn.send(()).unwrap();
        loop {
            std::thread::park();
        }
    });
    wait.recv().unwrap();
}

#[test]
fn exit_wipes_the_drbgs_of_running_threads() {
    let (status, stderr) = run("trigger_exit_with_a_running_thread", "");
    assert!(status.success(), "{stderr}");
    assert!(
        stderr.contains("rind-fips: zeroised 1 DRBG instances at exit"),
        "{stderr}"
    );
}

unsafe extern "C" {
    fn fork() -> i32;
    fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
}

/// What the children run: one thread draws and keeps running while another
/// forks, and the forked child exits at once.
#[test]
fn trigger_fork_with_a_running_thread() {
    let (drawn, wait) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        rind_fips::rand::fill(&mut [0; 16]).unwrap();
        drawn.send(()).unwrap();
        loop {
            std::thread::park();
        }
    });
    wait.recv().unwrap();
    // SAFETY: the child only exits.
    let pid = unsafe { fork() };
    assert!(pid >= 0, "fork failed");
    if pid == 0 {
        std::process::exit(0);
    }
    let mut status = 0;
    // SAFETY: `pid` is our child, and `status` writable.
    assert_eq!(unsafe { waitpid(pid, &mut status, 0) }, pid);
    assert_eq!(status, 0);
}

// The child wipes and forgets the copy of the running thread's DRBG as it
// forks, so finds none at exit, while the parent wipes the thread's own.
#[test]
fn a_forked_child_wipes_its_parents_drbgs() {
    let (status, stderr) = run("trigger_fork_with_a_running_thread", "");
    assert!(status.success(), "{stderr}");
    assert!(
        stderr.contains("rind-fips: zeroised 0 DRBG instances at exit"),
        "{stderr}"
    );
    assert!(
        stderr.contains("rind-fips: zeroised 1 DRBG instances at exit"),
        "{stderr}"
    );
}

#[test]
fn an_unknown_name_breaks_nothing() {
    let (status, stderr) = run("trigger_self_test", "sha");
    assert!(status.success(), "{stderr}");
}
