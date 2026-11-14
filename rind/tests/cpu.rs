//! The CPU check names each required feature the CPU lacks, and every
//! operation refuses with the same message.

#[test]
fn check_passes() {
    assert_eq!(rind::cpu::check(), Ok(()));
}

// `RIND_CPU_DISABLE_*` only takes effect with debug assertions or
// `--cfg rind_cpu_disable`, and x86_64 and the portable armv7 backend require
// no CPU features.
#[cfg(all(any(debug_assertions, rind_cpu_disable), rind_backend = "aarch64"))]
#[test]
fn missing_feature_is_named() {
    const REQUIRED: &[&str] = &["neon"];

    // Every operation refuses through `Entry`, so one AEAD and one hash stand
    // for the rest.
    const OPERATIONS: &[&str] = &["aes-gcm", "sha256"];

    // Set in the child process this test spawns once per feature and
    // operation, since the toggle is process-wide and would fail every other
    // test in this one.
    const CHILD: &str = "RIND_TEST_MISSING_CPU_FEATURE";

    // The child reports both refusals as output and lets the operation's
    // panic end it, since a `panic = "abort"` build cannot catch it.
    if let Some(operation) = std::env::var_os(CHILD) {
        use rind::digest::{SHA256, digest};

        println!("check: {}", rind::cpu::check().unwrap_err());
        match operation.to_str().unwrap() {
            "aes-gcm" => drop(rind::aead::Key::new(&rind::aead::AES_128_GCM, &[0; 16]).unwrap()),
            "sha256" => drop(digest(&SHA256, b"")),
            other => unreachable!("{other}"),
        }
        return;
    }

    for (feature, operation) in REQUIRED
        .iter()
        .flat_map(|feature| OPERATIONS.iter().map(move |operation| (feature, operation)))
    {
        // Under qemu-user, cargo runs this binary through
        // `CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUNNER`. The child is the
        // same aarch64 image, so it has to go through that runner too, as
        // `low::aarch64::cpu::reexec` does for the in-crate override tests.
        let exe = std::env::current_exe().unwrap();
        let mut cmd = match std::env::var("CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUNNER") {
            Ok(runner) => {
                let mut parts = runner.split_whitespace();
                let mut cmd = std::process::Command::new(parts.next().unwrap());
                cmd.args(parts);
                cmd.arg(exe);
                cmd
            }
            Err(_) => std::process::Command::new(exe),
        };
        let output = cmd
            .args(["--exact", "missing_feature_is_named", "--nocapture"])
            .env(CHILD, operation)
            .env(format!("RIND_CPU_DISABLE_{feature}"), "1")
            .output()
            .unwrap();
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );

        let expected = format!(
            "rind requires {feature} CPU support on {}",
            std::env::consts::ARCH
        );
        assert!(!output.status.success(), "{feature} {operation}: {text}");
        assert!(
            text.contains(&format!("check: {expected}\n")),
            "{feature} {operation}: {text}"
        );
        // The panic message follows its `panicked at <location>:` line.
        assert!(
            text.contains(&format!(":\n{expected}\n")),
            "{feature} {operation}: {text}"
        );
    }
}

// Legacy SSE code, such as rind's AES-GCM, pays a state transition or a false
// dependency when it follows a 256- or 512-bit kernel that left the upper
// halves of ymm0-15 dirty, so every operation that may run one must return
// with them clean. XINUSE[2] reports that state where `xgetbv` reads XINUSE;
// a CPU or emulator on which `vzeroupper` does not clear it is not checked.
#[cfg(rind_backend = "x86_64")]
#[test]
fn upper_vector_state_left_clean() {
    use core::arch::asm;
    use core::arch::x86_64::{__cpuid_count, _mm256_zeroupper};

    use rind::aead::{AES_128_GCM, AES_256_GCM, CHACHA20_POLY1305, Key, Nonce};
    use rind::agreement::{self, X25519};
    use rind::digest::{SHA256, SHA512, digest, legacy::SHA1};
    use rind::kem::{DecapsulationKey, EncapsulationKey, ML_KEM_768};
    use rind::signature::{EcdsaKeyPair, RsaKeyPair, sign};

    fn dirty() -> bool {
        let xinuse: u32;
        // SAFETY: the caller checked CPUID for `xgetbv` with ECX = 1.
        unsafe {
            asm!("xgetbv", in("ecx") 1, out("eax") xinuse, out("edx") _, options(nomem, nostack))
        };
        xinuse & 4 != 0
    }
    #[target_feature(enable = "avx")]
    fn zeroupper() {
        _mm256_zeroupper();
    }
    fn vzeroupper() {
        // SAFETY: the caller checked for AVX.
        unsafe { zeroupper() };
    }

    let xgetbv1 = __cpuid_count(0xd, 1).eax & 4 != 0;
    if !std::arch::is_x86_feature_detected!("avx") || !xgetbv1 {
        return;
    }
    vzeroupper();
    if dirty() {
        return;
    }

    // Checks the state as `operation` leaves it, before anything it returns
    // is dropped: dropping a key wipes it, which may clear the state.
    fn check<T>(what: &str, operation: impl FnOnce() -> T) -> T {
        vzeroupper();
        let output = operation();
        assert!(!dirty(), "{what} left the upper vector state dirty");
        output
    }

    let nonce = || Nonce::assume_unique_for_key([0; 12]);
    for (algorithm, key_len) in [
        (&AES_128_GCM, 16),
        (&AES_256_GCM, 32),
        (&CHACHA20_POLY1305, 32),
    ] {
        let key = check(&format!("{algorithm:?} key"), || {
            Key::new(algorithm, &vec![1; key_len]).unwrap()
        });
        for len in [32, 1200, 16384] {
            let mut data = vec![2; len];
            let tag = check(&format!("{algorithm:?} seal {len}"), || {
                key.seal_in_place_separate_tag(nonce(), b"aad", &mut data)
                    .unwrap()
            });
            data.extend_from_slice(tag.as_ref());
            check(&format!("{algorithm:?} open {len}"), || {
                key.open_in_place(nonce(), b"aad", &mut data).unwrap().len()
            });
        }
        check(&format!("{algorithm:?} key drop"), || drop(key));
    }

    let dk = check("ML-KEM-768 generate", || {
        DecapsulationKey::generate(&ML_KEM_768).unwrap()
    });
    let ek = EncapsulationKey::new(&ML_KEM_768, dk.public_key().as_ref()).unwrap();
    let (ciphertext, secret) = check("ML-KEM-768 encapsulate", || ek.encapsulate().unwrap());
    let decapsulated = check("ML-KEM-768 decapsulate", || {
        dk.decapsulate(ciphertext.as_ref()).unwrap()
    });
    check("ML-KEM-768 secret drop", || drop((secret, decapsulated)));

    for algorithm in [&SHA1, &SHA256, &SHA512] {
        check(&format!("{algorithm:?}"), || digest(algorithm, &[3; 4096]));
    }
    for algorithm in [&sign::ECDSA_P256_SHA256_ASN1, &sign::ECDSA_P384_SHA384_ASN1] {
        let key = check(&format!("{algorithm:?} generate"), || {
            EcdsaKeyPair::generate(algorithm).unwrap()
        });
        check(&format!("{algorithm:?} sign"), || {
            key.sign(b"message").unwrap()
        });
    }
    let ours = check("X25519 generate", || {
        agreement::PrivateKey::generate(&X25519).unwrap()
    });
    let theirs = agreement::PrivateKey::generate(&X25519)
        .unwrap()
        .public_key()
        .clone();
    check("X25519 agree", || ours.agree(theirs.as_ref()).unwrap());
    let rsa = RsaKeyPair::from_pkcs8(include_bytes!("../src/high/rsa/rsa2048.pkcs8.der")).unwrap();
    check("RSA-2048 sign", || {
        rsa.sign(&sign::RSA_PKCS1_SHA256, b"message").unwrap()
    });
}
