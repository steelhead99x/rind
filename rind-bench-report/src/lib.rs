//! Side-by-side Rust reader for [`admin/bench-report`](../admin/bench-report).
//!
//! The Python script remains the source of truth and the public command.
//! This crate parses schema 1, the report's tables, and `benchmarks/gaps.toml`
//! / `benchmarks/verified.toml` the way that script does. Later stages add
//! `render`, `gate`, `run`, and `collect` behind the same CLI.

mod error;
mod format;
mod gaps;
mod paths;
mod schema;
mod tables;
mod verified;

pub use error::{Error, Result};
pub use format::{fnmatchcase, human, significant};
pub use gaps::{
    DecidedGap, GapHit, gaps_of, load_gaps, parse_gaps, tier_column, tier_name, tier_row,
};
pub use paths::{Paths, relpath, workspace_root};
pub use schema::{
    BenchArtifact, BenchPoint, BuildCost, CpuInfo, HostResult, Loaded, Patch, Tier, TierDocument,
    TimingRow, Toolchain, load_bench_artifact, load_host_file, load_hosts, load_tier_file,
    parse_host, parse_tier,
};
pub use tables::{
    BASELINES, BUSY_SHARE, COPY_FAILED, CRITERION_ARGS, FONT, LEASE_HELD, REMOTE_DIR, REPO, SLOWER,
    SPEED_BINS, SPEED_COLORS, SPEED_LABELS, THEMES, TIER_BINS, TIER_LABELS, TIER_ROWS, UNRANKED,
    baselines, builds, column_name, columns, cpu_features, crates_for, criterion_args, host, hosts,
    is_variant, label, libraries, library_of, operation_of, operation_regex, operations, repo,
    required_features, row_name, sections, tiers, variant_of, variants,
};
pub use verified::{VerifiedEntry, host_arch, host_os, load_verified, parse_verified, proof_for};
