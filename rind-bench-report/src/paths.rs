//! Locate the checkout the Python script calls `ROOT`.

use std::env;
use std::path::{Component, Path, PathBuf};

/// The workspace root: `RIND_BENCH_REPORT_ROOT`, else the ancestor of the
/// working directory that holds `admin/bench-report`, else this crate's parent.
pub fn workspace_root() -> PathBuf {
    if let Ok(root) = env::var("RIND_BENCH_REPORT_ROOT")
        && !root.is_empty()
    {
        return PathBuf::from(root);
    }
    if let Ok(cwd) = env::current_dir() {
        let mut dir = cwd;
        loop {
            if dir.join("admin/bench-report").is_file() && dir.join("benchmarks").is_dir() {
                return dir;
            }
            if !dir.pop() {
                break;
            }
        }
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .unwrap_or_else(|_| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(".."))
}

pub struct Paths {
    pub root: PathBuf,
}

impl Paths {
    pub fn discover() -> Self {
        Self {
            root: workspace_root(),
        }
    }

    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    pub fn benchmarks(&self) -> PathBuf {
        self.root.join("benchmarks")
    }

    pub fn data(&self) -> PathBuf {
        self.benchmarks().join("data")
    }

    pub fn verified(&self) -> PathBuf {
        self.benchmarks().join("verified.toml")
    }

    pub fn gaps(&self) -> PathBuf {
        self.benchmarks().join("gaps.toml")
    }

    pub fn report(&self) -> PathBuf {
        self.root.join("BENCHMARKS.md")
    }

    pub fn flake(&self) -> PathBuf {
        self.root.join("flake.nix")
    }

    pub fn lockfile(&self) -> PathBuf {
        self.root.join("Cargo.lock")
    }
}

/// `os.path.relpath`, without resolving symlinks.
pub fn relpath(path: &Path, start: &Path) -> String {
    let path = absolute(path);
    let start = absolute(start);
    let path_c: Vec<_> = path.components().collect();
    let start_c: Vec<_> = start.components().collect();
    let mut i = 0;
    while i < path_c.len() && i < start_c.len() && path_c[i] == start_c[i] {
        i += 1;
    }
    let mut parts = Vec::new();
    for _ in i..start_c.len() {
        parts.push("..".to_string());
    }
    for c in &path_c[i..] {
        match c {
            Component::Normal(s) => parts.push(s.to_string_lossy().into_owned()),
            Component::CurDir => {}
            Component::ParentDir => parts.push("..".to_string()),
            Component::RootDir | Component::Prefix(_) => {}
        }
    }
    if parts.is_empty() {
        ".".to_string()
    } else {
        parts.join("/")
    }
}

fn absolute(path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(path)
    }
}
