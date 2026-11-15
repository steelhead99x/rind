// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The module refuses, as it loads, a CPU missing a feature it requires,
//! aborting with the feature's name. Masking AES with `RIND_CPU_DISABLE_aes`
//! stands in for such a CPU: the test runs itself again in a child with the
//! mask set.
#![cfg(rind_fips_module)]

use std::os::unix::process::ExitStatusExt;
use std::process::Command;

/// What the module names when it lacks AES, on each architecture it runs on.
#[cfg(target_arch = "x86_64")]
const AES: &str = "aes";
#[cfg(target_arch = "aarch64")]
const AES: &str = "aes, pmull, and sha2";

#[test]
fn refuses_a_cpu_without_aes() {
    // Every CPU the tests run on has what the module requires, so the parent
    // loaded it; the child must never get this far.
    assert_eq!(rind_fips::cpu::check(), Ok(()));
    if std::env::var_os("RIND_CPU_DISABLE_aes").is_some() {
        panic!("the module loaded on a CPU without AES");
    }

    const SIGABRT: i32 = 6;
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "refuses_a_cpu_without_aes", "--nocapture"])
        .env("RIND_CPU_DISABLE_aes", "")
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.signal(),
        Some(SIGABRT),
        "{}: {stderr}",
        output.status
    );
    assert!(
        stderr.contains(&format!("rind-fips: requires {AES} CPU support")),
        "{stderr}"
    );
}
