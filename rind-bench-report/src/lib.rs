//! Side-by-side Rust reader for [`admin/bench-report`](../admin/bench-report).
//!
//! The Python script remains the source of truth and the public command.
//! This crate parses schema 1, the report's tables, and `benchmarks/gaps.toml`
//! / `benchmarks/verified.toml` the way that script does. Later stages add
//! `render`, `gate`, `run`, and `collect` behind the same CLI.
//!
//! Operation globs use [`fnmatchcase`]: Linux CPython semantics, which do not
//! casefold. macOS `fnmatch.fnmatch` would.

mod collect;
mod error;
mod format;
mod gaps;
mod gate;
mod idle;
mod nightly;
mod paths;
mod prose;
mod report;
mod run;
mod schema;
mod summary;
mod svg;
mod tables;
mod verified;

#[cfg(test)]
mod behavior;

pub use collect::{collect, host_script, shell_quote};
pub use error::{Error, Result};
pub use format::{fnmatchcase, human, significant};
pub use gaps::{
    DecidedGap, GapHit, GapPattern, gaps_of, load_gap_patterns, load_gaps, parse_gaps, tier_column,
    tier_name, tier_row,
};
pub use gate::{GateReport, gate};
pub use nightly::nightly;
pub use paths::{Paths, relpath, workspace_root};
pub use report::{host_table, platform_of, render_check, render_files, render_write};
pub use run::run;
pub use schema::{
    BenchArtifact, BenchPoint, BuildCost, CpuInfo, HostResult, Loaded, Patch, Tier, TierDocument,
    TimingRow, Toolchain, load_bench_artifact, load_host_file, load_hosts, load_tier_file,
    parse_host, parse_tier,
};
pub use summary::summary;
pub use tables::{
    BASELINES, BUSY_SHARE, COPY_FAILED, CRITERION_ARGS, FONT, LEASE_HELD, REMOTE_DIR, REPO, SLOWER,
    SPEED_BINS, SPEED_COLORS, SPEED_LABELS, THEMES, TIER_BINS, TIER_LABELS, TIER_ROWS, UNRANKED,
    baselines, builds, column_name, columns, cpu_features, crates_for, criterion_args, host, hosts,
    is_variant, label, libraries, library_of, operation_of, operation_regex, operations, repo,
    required_features, row_name, sections, tiers, variant_of, variants,
};
pub use verified::{VerifiedEntry, host_arch, host_os, load_verified, parse_verified, proof_for};
