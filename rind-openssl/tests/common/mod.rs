// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! What the provider and ctgrind tests share: loading rind with the README's
//! configuration.
//!
//! The tests link rind's provider into the test binary and register it with
//! OpenSSL as a built-in, so they always check the build under test, with its
//! features and flags. The shared library is another build's output that no
//! test can name: Cargo keeps each unit's output in its own
//! `build/<package>/<hash>/out`, hands a test no path to its package's own
//! library, and leaves one library per feature or flag set in the target
//! directory. Only `documented_config_loads_rind` loads a library file, to
//! check that the configuration's `module =` line works; any build passes it.
#![allow(dead_code)]

use std::ffi::{c_char, c_int, c_void};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::SystemTime;

use openssl_sys::OSSL_LIB_CTX;

unsafe extern "C" {
    fn OSSL_PROVIDER_add_builtin(
        ctx: *mut OSSL_LIB_CTX,
        name: *const c_char,
        init: unsafe extern "C" fn(
            *const c_void,
            *const c_void,
            *mut *const c_void,
            *mut *mut c_void,
        ) -> c_int,
    ) -> c_int;
}

/// Makes rind's provider, linked into this binary, the one `ctx` activates
/// for the `rind` section of its configuration. A null `ctx` is OpenSSL's
/// default library context.
pub fn add_builtin(ctx: *mut OSSL_LIB_CTX) {
    let ok = unsafe {
        OSSL_PROVIDER_add_builtin(ctx, c"rind".as_ptr(), rind_openssl::OSSL_provider_init)
    };
    assert_eq!(ok, 1);
}

/// The README's configuration, written to a file. `module` is the library
/// its `module =` line names; `None` drops the line, so the section
/// activates the built-in that [`add_builtin`] registered.
pub fn config(module: Option<&Path>) -> PathBuf {
    config_with(module, "")
}

/// As [`config`], with `extra` lines added to the `rind` section, such as
/// `ec = 1`.
pub fn config_with(module: Option<&Path>, extra: &str) -> PathBuf {
    let mut found = false;
    let config: String = include_str!("../../openssl.cnf")
        .lines()
        .map(|line| match (line.starts_with("module = "), module) {
            (false, _) => format!("{line}\n"),
            (true, None) => {
                found = true;
                extra_lines(extra)
            }
            (true, Some(path)) => {
                found = true;
                format!("module = {}\n{}", conf_value(path), extra_lines(extra))
            }
        })
        .collect();
    assert!(found, "the documented configuration names no module");
    // Tests run in parallel, and under nextest each in a process of its own.
    static FILES: AtomicUsize = AtomicUsize::new(0);
    let path = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!(
        "rind-openssl-{}-{}.cnf",
        std::process::id(),
        FILES.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, config).unwrap();
    path
}

fn extra_lines(extra: &str) -> String {
    extra.lines().map(|line| format!("{line}\n")).collect()
}

/// `path` as an `openssl.cnf` value: each ASCII character but a letter,
/// digit, or `/._-` escaped, as a `#` would start a comment and a `$` a
/// variable.
fn conf_value(path: &Path) -> String {
    let mut out = String::new();
    for c in path.display().to_string().chars() {
        if c.is_ascii() && !(c.is_ascii_alphanumeric() || "/._-".contains(c)) {
            out.push('\\');
        }
        out.push(c);
    }
    out
}

/// A shared library some test build made: beside the test binary where
/// Cargo puts it there, else the newest in the sibling unit directories of
/// Cargo's newer build layout. Not necessarily this build's, as the
/// module comment says.
pub fn library() -> PathBuf {
    let name = format!(
        "{}rind_openssl{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    );
    let exe = std::env::current_exe().unwrap();
    let beside = exe.with_file_name(&name);
    if beside.exists() {
        return beside;
    }
    let units = exe.ancestors().nth(3).unwrap_or_else(|| {
        panic!("{} is too shallow to find {name} from", exe.display());
    });
    let mut found: Vec<(SystemTime, PathBuf)> = std::fs::read_dir(units)
        .unwrap_or_else(|error| panic!("cannot list {}: {error}", units.display()))
        .filter_map(|unit| {
            let path = unit.ok()?.path().join("out").join(&name);
            Some((path.metadata().ok()?.modified().ok()?, path))
        })
        .collect();
    found.sort();
    match found.pop() {
        Some((_, path)) => path,
        None => panic!(
            "no {name} beside {} or in a sibling of its directory",
            exe.display()
        ),
    }
}
