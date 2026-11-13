// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Shared helpers for the `rind-admin` binaries.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

/// Walk `dir` for regular files whose name ends in `.rs`, directories first
/// in sorted order. Does not follow symbolic links.
pub fn rust_sources(dir: &Path) -> io::Result<Vec<PathBuf>> {
    let mut out = Vec::new();
    walk_rs(dir, &mut out)?;
    Ok(out)
}

fn walk_rs(dir: &Path, out: &mut Vec<PathBuf>) -> io::Result<()> {
    let mut entries = fs::read_dir(dir)?.collect::<io::Result<Vec<_>>>()?;
    entries.sort_by_key(|e| e.file_name());
    for ent in entries {
        let path = ent.path();
        let ft = ent.file_type()?;
        if ft.is_symlink() {
            continue;
        }
        if ft.is_dir() {
            walk_rs(&path, out)?;
        } else if ft.is_file() && path.extension().is_some_and(|ext| ext == "rs") {
            out.push(path);
        }
    }
    Ok(())
}

/// Whether the file's contents contain the SPDX marker the checker requires.
pub fn has_spdx_identifier(bytes: &[u8]) -> bool {
    // Matches `grep -L "SPDX-License-Identifier:"`.
    memchr_substr(bytes, b"SPDX-License-Identifier:")
}

fn memchr_substr(haystack: &[u8], needle: &[u8]) -> bool {
    haystack.windows(needle.len()).any(|w| w == needle)
}

/// Paths of `.rs` files under `src_root` that lack an SPDX identifier, as
/// relative paths from `cwd` when possible, sorted.
pub fn missing_spdx(src_root: &Path, cwd: &Path) -> io::Result<Vec<PathBuf>> {
    let mut missing = Vec::new();
    for path in rust_sources(src_root)? {
        let bytes = fs::read(&path)?;
        if !has_spdx_identifier(&bytes) {
            missing.push(relativize(&path, cwd));
        }
    }
    missing.sort();
    Ok(missing)
}

/// True when the two files exist and have identical bytes.
pub fn files_identical(a: &Path, b: &Path) -> io::Result<bool> {
    Ok(fs::read(a)? == fs::read(b)?)
}

fn relativize(path: &Path, cwd: &Path) -> PathBuf {
    path.strip_prefix(cwd)
        .map(Path::to_path_buf)
        .unwrap_or_else(|_| path.to_path_buf())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::sync::atomic::{AtomicU64, Ordering};

    static UNIQUE: AtomicU64 = AtomicU64::new(0);

    fn scratch() -> PathBuf {
        let n = UNIQUE.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!(
            "rind-admin-scan-license-{}-{}",
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

    #[test]
    fn spdx_detects_the_grep_string() {
        assert!(has_spdx_identifier(
            b"// SPDX-License-Identifier: Apache-2.0\n"
        ));
        assert!(!has_spdx_identifier(b"// SPDX-License-Identifier\n"));
        assert!(!has_spdx_identifier(b""));
    }

    #[test]
    fn missing_spdx_lists_only_files_without_the_marker() {
        let root = scratch();
        write(
            &root.join("rind/src/ok.rs"),
            "// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0\nfn ok() {}\n",
        );
        write(&root.join("rind/src/nested/bad.rs"), "fn bad() {}\n");
        write(&root.join("rind/src/ignored.txt"), "not rust\n");
        let missing = missing_spdx(&root.join("rind/src"), &root).unwrap();
        assert_eq!(missing, vec![PathBuf::from("rind/src/nested/bad.rs")]);
        fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn files_identical_is_byte_for_byte() {
        let root = scratch();
        write(&root.join("a"), "same\n");
        write(&root.join("b"), "same\n");
        write(&root.join("c"), "different\n");
        assert!(files_identical(&root.join("a"), &root.join("b")).unwrap());
        assert!(!files_identical(&root.join("a"), &root.join("c")).unwrap());
        fs::remove_dir_all(&root).unwrap();
    }
}
