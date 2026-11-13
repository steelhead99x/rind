// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! End-to-end checks of the `scan-license` binary on fixture trees.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static UNIQUE: AtomicU64 = AtomicU64::new(0);

fn bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_scan-license"))
}

fn scratch() -> PathBuf {
    let n = UNIQUE.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "rind-admin-scan-license-bin-{}-{}",
        std::process::id(),
        n
    ));
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn write(path: &Path, body: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(path, body).unwrap();
}

fn populate_ok(root: &Path) {
    write(
        &root.join("rind/src/lib.rs"),
        "// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0\n",
    );
    write(&root.join("rind/LICENSE"), "license text\n");
    write(&root.join("rind-python/LICENSE"), "license text\n");
}

fn run(root: &Path) -> (i32, String, String) {
    let out = Command::new(bin())
        .current_dir(root)
        .output()
        .expect("run scan-license");
    let status = out.status.code().unwrap_or(255);
    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    (status, stdout, stderr)
}

#[test]
fn clean_tree_exits_zero_and_prints_nothing() {
    let root = scratch();
    populate_ok(&root);
    let (status, stdout, stderr) = run(&root);
    assert_eq!((status, stdout.as_str(), stderr.as_str()), (0, "", ""));
    fs::remove_dir_all(&root).unwrap();
}

#[test]
fn missing_spdx_is_reported_and_fails() {
    let root = scratch();
    populate_ok(&root);
    write(&root.join("rind/src/mid/no_spdx.rs"), "fn x() {}\n");
    let (status, stdout, stderr) = run(&root);
    assert_eq!(status, 1);
    assert_eq!(stderr, "");
    assert_eq!(
        stdout,
        "rind/src/mid/no_spdx.rs requires a SPDX-License-Identifier\n"
    );
    fs::remove_dir_all(&root).unwrap();
}

#[test]
fn mismatched_python_license_is_reported_and_fails() {
    let root = scratch();
    populate_ok(&root);
    write(&root.join("rind-python/LICENSE"), "other text\n");
    let (status, stdout, stderr) = run(&root);
    assert_eq!(status, 1);
    assert_eq!(stderr, "");
    assert_eq!(
        stdout,
        "rind-python/LICENSE must be a copy of rind/LICENSE\n"
    );
    fs::remove_dir_all(&root).unwrap();
}

#[test]
fn both_problems_are_reported() {
    let root = scratch();
    populate_ok(&root);
    write(&root.join("rind/src/a.rs"), "fn a() {}\n");
    write(&root.join("rind-python/LICENSE"), "other text\n");
    let (status, stdout, stderr) = run(&root);
    assert_eq!(status, 1);
    assert_eq!(stderr, "");
    assert_eq!(
        stdout,
        "rind/src/a.rs requires a SPDX-License-Identifier\nrind-python/LICENSE must be a copy of rind/LICENSE\n"
    );
    fs::remove_dir_all(&root).unwrap();
}
