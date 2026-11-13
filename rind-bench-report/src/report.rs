//! `BENCHMARKS.md` and the files `render` writes.

use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

use indexmap::IndexMap;

use crate::error::{Error, Result};
use crate::format::human;
use crate::gaps::load_gaps;
use crate::gaps::{DecidedGap, tier_points, times};
use crate::paths::{Paths, relpath};
use crate::prose::{
    BUILD_INTRO, DIT_INTRO, GAPS_INTRO, GENERATED, IDLE, SPEED_INTRO, TIERS_INTRO, UPDATING_BUSY,
    VERIFIED_INTRO,
};
use crate::schema::{
    BuildMeasurement, HostResult, TierDocument, load_host_file, load_hosts, load_tier_file,
};
use crate::svg::{host_svg, overview_svg, tier_columns, tiers_svg};
use crate::tables::{
    BUILDS, HOSTS, REPO, THEMES, column_name, columns, host as host_spec, hosts as host_specs,
    label, operations, row_name, variant_of,
};
use crate::verified::{VerifiedEntry, load_verified, proof_for};

pub fn generate(
    root: &Path,
    hosts: &[HostResult],
    tiers: Option<&TierDocument>,
    verified: &[VerifiedEntry],
    gaps: &[DecidedGap],
) -> Result<Vec<(PathBuf, String)>> {
    let benchmarks = root.join("benchmarks");
    let shown = shown(hosts);
    let missing: Vec<String> = HOSTS
        .iter()
        .filter(|spec| shown.iter().all(|host| host.host != spec.name))
        .map(|spec| format!("`{}`", spec.name))
        .collect();
    let words = ["no", "one", "two", "three", "four", "five", "six"];
    let count = words.get(shown.len()).copied().unwrap_or("");
    let count = if count.is_empty() {
        shown.len().to_string()
    } else {
        count.to_string()
    };
    let mut md = vec![
        "# Benchmarks".to_string(),
        String::new(),
        GENERATED.to_string(),
        String::new(),
        format!(
            "How long rind and the usual Rust crypto libraries take for the same operations, on {count} machine{}, {rest}",
            if shown.len() == 1 { "" } else { "s" },
            rest = "and what each costs to build. Every library runs its native path on each host. A ✓ marks an operation whose whole computation a published formal proof covers, as [Verified code](#verified-code) lists."
        ),
        String::new(),
        "## Hosts".to_string(),
        String::new(),
    ];
    if !shown.is_empty() {
        md.push("| Host | CPU | OS | Measured |".to_string());
        md.push("|---|---|---|---|".to_string());
        for host in &shown {
            let model = host
                .cpu
                .as_ref()
                .map(|cpu| cpu.model.as_str())
                .unwrap_or("");
            let os = host.os.as_deref().unwrap_or("");
            md.push(format!(
                "| `{}` | {model} | {os} | {} |",
                host.host,
                measured(host)
            ));
        }
        md.push(String::new());
    }
    if !missing.is_empty() {
        md.push(format!("Not measured yet: {}.", missing.join(", ")));
        md.push(String::new());
    }
    md.push(IDLE.to_string());
    md.push(String::new());

    let mut files = Vec::new();
    if !shown.is_empty() {
        md.extend([
            "## Speed".to_string(),
            String::new(),
            SPEED_INTRO.to_string(),
            String::new(),
        ]);
        if timed_any(&shown, "rind-dit-held") {
            md.push(DIT_INTRO.to_string());
            md.push(String::new());
        }
        md.extend(picture(
            "overview",
            "Time over the fastest library's, by operation, library, and host",
        ));
        md.push(String::new());
        for theme in THEMES {
            let suffix = if theme.name == "dark" { "-dark" } else { "" };
            files.push((
                benchmarks.join(format!("overview{suffix}.svg")),
                overview_svg(hosts, verified, theme),
            ));
        }
    }
    for spec in HOSTS {
        let Some(host) = shown.iter().copied().find(|host| host.host == spec.name) else {
            continue;
        };
        let rows = host.results.as_deref().map(times).unwrap_or_default();
        let untimed: Vec<String> = operations()
            .iter()
            .map(|op| row_name(op))
            .filter(|row| rows.iter().all(|(name, _)| name != row))
            .map(|row| label(&row))
            .collect();
        let model = host
            .cpu
            .as_ref()
            .map(|cpu| cpu.model.as_str())
            .unwrap_or("");
        md.push(format!("### `{}`: {model}", host.host));
        md.push(String::new());
        md.push(format!(
            "Measured {}, on {} with {}.",
            measured(host),
            host.os.as_deref().unwrap_or(""),
            host.toolchain
                .as_ref()
                .map(|tool| tool.rustc.as_str())
                .unwrap_or("")
        ));
        md.push(String::new());
        if let Some(note) = spec.note {
            md.push(note.to_string());
            md.push(String::new());
        }
        if !untimed.is_empty() {
            md.push(format!(
                "Not timed on `{}`: {}.",
                host.host,
                untimed.join(", ")
            ));
            md.push(String::new());
        }
        if let Some(refused) = &host.refused
            && !refused.is_empty()
        {
            for (lib, missing_features) in refused {
                let upper: Vec<String> =
                    missing_features.iter().map(|f| f.to_uppercase()).collect();
                md.push(format!(
                    "{} isn't timed on `{}`: it requires {}, which this CPU lacks.",
                    column_name(lib),
                    host.host,
                    and_list(&upper)
                ));
            }
            md.push(String::new());
        }
        md.extend(picture(&host.host, &format!("Times on {}", host.host)));
        md.push(String::new());
        md.push("<details>".to_string());
        md.push(format!("<summary>Times on {}</summary>", host.host));
        md.push(String::new());
        md.extend(host_table(host, verified));
        md.push(String::new());
        md.push("</details>".to_string());
        md.push(String::new());
        for theme in THEMES {
            let suffix = if theme.name == "dark" { "-dark" } else { "" };
            files.push((
                benchmarks.join(format!("{}{suffix}.svg", host.host)),
                host_svg(&host.host, host, verified, theme),
            ));
        }
    }

    if !shown.is_empty() {
        md.extend([
            "## Build cost".to_string(),
            String::new(),
            BUILD_INTRO.to_string(),
            String::new(),
        ]);
    }
    for host in &shown {
        let Some(cost) = &host.build_cost else {
            continue;
        };
        md.push(format!("### `{}`", host.host));
        md.push(String::new());
        if cost.status != "ok" {
            md.push(format!(
                "Not measured: {}",
                cost.reason.as_deref().unwrap_or("")
            ));
            md.push(String::new());
            continue;
        }
        let info = cost.host.as_ref();
        md.push(format!(
            "Measured {} at {}, with {}, {}, and {} jobs.",
            &cost.started[..cost.started.len().min(10)],
            commit_link(&host.commit),
            info.and_then(|h| h.rustc.as_deref()).unwrap_or(""),
            info.and_then(|h| h.cc.as_deref()).unwrap_or(""),
            info.and_then(|h| h.jobs.as_deref()).unwrap_or("")
        ));
        md.push(String::new());
        if let Some(builds) = &cost.builds {
            md.extend(build_table(builds));
        }
        md.push(String::new());
    }

    md.push("## CPU tiers".to_string());
    md.push(String::new());
    if let Some(tiers) = tiers {
        let mut cpus: Vec<&str> = tiers.tiers.iter().map(|tier| tier.cpu.as_str()).collect();
        cpus.sort_unstable();
        cpus.dedup();
        md.push(TIERS_INTRO.to_string());
        md.push(String::new());
        md.push(format!(
            "From [run {}]({}), {} at {}, on {}.",
            tiers.run,
            tiers.url,
            &tiers.date[..tiers.date.len().min(10)],
            commit_link(&tiers.commit),
            cpus.join(", ")
        ));
        md.push(String::new());
        md.extend(picture(
            "tiers",
            "rind's time over the fastest of aws-lc-rs and ring, by CPU tier",
        ));
        md.push(String::new());
        md.push("<details>".to_string());
        md.push("<summary>Every benchmark</summary>".to_string());
        md.push(String::new());
        md.extend(tier_table(tiers)?);
        md.push(String::new());
        md.push("</details>".to_string());
        md.push(String::new());
        for theme in THEMES {
            let suffix = if theme.name == "dark" { "-dark" } else { "" };
            files.push((
                benchmarks.join(format!("tiers{suffix}.svg")),
                tiers_svg(tiers, theme)?,
            ));
        }
    } else {
        md.push("No nightly results yet.".to_string());
        md.push(String::new());
    }

    md.push("## Known gaps".to_string());
    md.push(String::new());
    md.push(GAPS_INTRO.to_string());
    md.push(String::new());
    if gaps.is_empty() {
        md.push("None.".to_string());
    } else {
        md.extend(gap_table(root, gaps)?);
    }
    md.push(String::new());
    md.push("## Verified code".to_string());
    md.push(String::new());
    md.push(VERIFIED_INTRO.to_string());
    md.push(String::new());
    md.push("| Library | Operations | Platform | Proof |".to_string());
    md.push("|---|---|---|---|".to_string());
    for entry in verified {
        let ops = entry
            .operations
            .iter()
            .map(|pattern| format!("`{pattern}`"))
            .collect::<Vec<_>>()
            .join(", ");
        md.push(format!(
            "| {} | {ops} | {} | [{}]({}) |",
            column_name(&entry.library),
            platform_of(entry),
            entry.proof,
            entry.link
        ));
    }
    md.extend([
        String::new(),
        "## Updating this report".to_string(),
        String::new(),
        "`admin/bench-report collect` runs the report's benchmarks, then".to_string(),
        "`admin/build-cost`, on each benchmark host in turn over ssh, in the Nix dev".to_string(),
        "shell and under `quest gate`, which waits for the host to have room but".to_string(),
        "shares it with other gated work, so its numbers are noisier than the nightly".to_string(),
        UPDATING_BUSY.to_string(),
        "`.tmp/bench-report/`. `admin/bench-report nightly` saves the latest nightly".to_string(),
        "`bench` run's results, and `admin/bench-report render --from DIR` copies a".to_string(),
        "collection's measured hosts into `benchmarks/data/` and writes".to_string(),
        "`BENCHMARKS.md` and its SVGs, which the README shows too, from them, `benchmarks/verified.toml`, and".to_string(),
        "`benchmarks/gaps.toml`, which must hold a quest or a reason for every gap".to_string(),
        "over 10%.".to_string(),
        String::new(),
    ]);
    files.push((root.join("BENCHMARKS.md"), md.join("\n")));
    Ok(files)
}

fn shown(hosts: &[HostResult]) -> Vec<&HostResult> {
    HOSTS
        .iter()
        .filter_map(|spec| hosts.iter().find(|host| host.host == spec.name))
        .collect()
}

fn timed_any(hosts: &[&HostResult], library: &str) -> bool {
    hosts.iter().any(|host| {
        host.results
            .as_ref()
            .is_some_and(|rows| rows.iter().any(|row| row.library == library))
    })
}

fn picture(name: &str, alt: &str) -> [String; 4] {
    [
        "<picture>".to_string(),
        format!(
            "  <source media=\"(prefers-color-scheme: dark)\" srcset=\"benchmarks/{name}-dark.svg\">"
        ),
        format!(
            "  <img alt=\"{}\" src=\"benchmarks/{name}.svg\">",
            alt.replace('&', "&amp;")
                .replace('<', "&lt;")
                .replace('>', "&gt;")
                .replace('"', "&quot;")
        ),
        "</picture>".to_string(),
    ]
}

fn commit_link(commit: &str) -> String {
    let short = commit.get(..8).unwrap_or(commit);
    format!("[`{short}`](https://github.com/{REPO}/commit/{commit})")
}

fn measured(host: &HostResult) -> String {
    let noisy = if host.load.as_ref().and_then(|load| load.noisy) == Some(true) {
        ", noisy"
    } else {
        ""
    };
    let day = host
        .started
        .as_deref()
        .and_then(|s| s.get(..10))
        .unwrap_or("");
    format!("{day} at {}{noisy}", commit_link(&host.commit))
}

pub fn platform_of(entry: &VerifiedEntry) -> String {
    let mut words = vec![
        entry
            .arch
            .clone()
            .unwrap_or_else(|| "any architecture".to_string()),
    ];
    let cpu = entry.cpu.as_deref().unwrap_or(&[]);
    let has: Vec<&str> = cpu
        .iter()
        .filter(|f| !f.starts_with('!'))
        .map(String::as_str)
        .collect();
    let lacks: Vec<&str> = cpu.iter().filter_map(|f| f.strip_prefix('!')).collect();
    if !has.is_empty() {
        words.push(format!("with {}", has.join(", ")));
    }
    if !lacks.is_empty() {
        words.push(format!("without {}", lacks.join(", ")));
    }
    if let Some(os) = &entry.os {
        words.push(
            match os.as_str() {
                "linux" => "on Linux",
                "macos" => "on macOS",
                other => other,
            }
            .to_string(),
        );
    }
    words.join(" ")
}

pub fn host_table(host: &HostResult, verified: &[VerifiedEntry]) -> Vec<String> {
    let rows = host.results.as_deref().map(times).unwrap_or_default();
    let libs = timed_libs(host);
    let mut lines = vec![
        format!(
            "| Operation | {} |",
            libs.iter()
                .map(|lib| column_name(lib))
                .collect::<Vec<_>>()
                .join(" | ")
        ),
        format!("|---|{}", "---|".repeat(libs.len())),
    ];
    for op in operations() {
        let row = row_name(op);
        let libs_ns = rows
            .iter()
            .find(|(name, _)| name == &row)
            .map(|(_, libs)| libs);
        let mut cells = Vec::new();
        for lib in &libs {
            let Some(ns) = libs_ns.and_then(|map| map.get(*lib)).copied() else {
                cells.push("-".to_string());
                continue;
            };
            let check = if proof_for(verified, variant_of(lib), &row, host).is_some() {
                " ✓"
            } else {
                ""
            };
            cells.push(format!("{}{check}", human(ns)));
        }
        lines.push(format!("| {} | {} |", label(&row), cells.join(" | ")));
    }
    lines
}

fn timed_libs(host: &HostResult) -> Vec<&'static str> {
    let mut timed = HashSet::new();
    if let Some(results) = &host.results {
        for row in results {
            timed.insert(row.library.as_str());
        }
    }
    columns()
        .iter()
        .filter(|(lib, _)| timed.contains(lib))
        .map(|(lib, _)| *lib)
        .collect()
}

fn build_table(builds: &[BuildMeasurement]) -> Vec<String> {
    let mut lines = vec![
        "| Build | Wall s (range) | CPU s | Stripped MB | Tools needed | Crates |".to_string(),
        "|---|---|---|---|---|---|".to_string(),
    ];
    for build in builds {
        let low = build.seconds.iter().copied().fold(f64::INFINITY, f64::min);
        let high = build
            .seconds
            .iter()
            .copied()
            .fold(f64::NEG_INFINITY, f64::max);
        let name = BUILDS
            .iter()
            .find(|(key, _)| *key == build.name)
            .map(|(_, label)| *label)
            .unwrap_or(build.name.as_str());
        let tools = if build.tools.is_empty() {
            "none".to_string()
        } else {
            build.tools.join(", ")
        };
        lines.push(format!(
            "| {name} | {:.1} ({low:.1} to {high:.1}) | {:.0} | {:.2} | {tools} | {} |",
            build.median_seconds,
            build.median_cpu_seconds,
            build.stripped_bytes as f64 / 1e6,
            build.packages.len()
        ));
    }
    lines
}

fn tier_table(doc: &TierDocument) -> Result<Vec<String>> {
    let columns = tier_columns(doc)?;
    let mut by_key: IndexMap<String, IndexMap<String, f64>> = IndexMap::new();
    for tier in &doc.tiers {
        let column = crate::gaps::tier_column(tier)?;
        for (key, point) in tier_points(tier) {
            by_key
                .entry(key)
                .or_default()
                .insert(column.clone(), point.ratio);
        }
    }
    let mut keys: Vec<String> = by_key.keys().cloned().collect();
    keys.sort();
    let mut lines = vec![
        format!("| Benchmark | {} |", columns.join(" | ")),
        format!("|---|{}", "---|".repeat(columns.len())),
    ];
    for key in keys {
        let cells = columns
            .iter()
            .map(|column| {
                by_key[&key]
                    .get(column)
                    .map(|ratio| format!("{ratio:.2}"))
                    .unwrap_or_default()
            })
            .collect::<Vec<_>>()
            .join(" | ");
        lines.push(format!("| `{key}` | {cells} |"));
    }
    Ok(lines)
}

fn gap_table(root: &Path, gaps: &[DecidedGap]) -> Result<Vec<String>> {
    let rows: HashSet<String> = operations().iter().map(|op| row_name(op)).collect();
    let mut lines = vec![
        "| Operation | On | rind's time over the fastest | Decision |".to_string(),
        "|---|---|---|---|".to_string(),
    ];
    for gap in gaps {
        let ops = gap
            .operations
            .iter()
            .map(|op| {
                if rows.contains(op) {
                    label(op)
                } else {
                    format!("`{op}`")
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        let on = gap
            .on
            .iter()
            .map(|place| {
                if host_spec(place).is_some() {
                    format!("`{place}`")
                } else {
                    format!("{place} tier")
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        let mut ratios: Vec<f64> = gap.covered.iter().map(|hit| hit.ratio).collect();
        ratios.sort_by(f64::total_cmp);
        let min = *ratios.first().unwrap_or(&0.0);
        let max = *ratios.last().unwrap_or(&0.0);
        let mut spread = format!("{min:.2}×");
        if max - min >= 0.005 {
            spread.push_str(&format!(" to {max:.2}×"));
        }
        let mut names: Vec<&str> = gap
            .covered
            .iter()
            .map(|hit| column_name(&hit.library))
            .collect();
        names.sort_unstable();
        names.dedup();
        let decision = if let Some(quest) = &gap.quest {
            format!("[{}]({})", quest_title(root, quest)?, &quest[1..])
        } else {
            gap.reason.clone().unwrap_or_default()
        };
        lines.push(format!(
            "| {ops} | {on} | {spread} ({}) | {decision} |",
            names.join(", ")
        ));
    }
    Ok(lines)
}

fn quest_title(root: &Path, path: &str) -> Result<String> {
    let file = root.join(path.trim_start_matches('/'));
    let text = fs::read_to_string(&file)
        .map_err(|err| Error::new(format!("{}: {err}", file.display())))?;
    let line = text.lines().next().unwrap_or("").trim();
    let mut rest = line.strip_prefix("# ").unwrap_or(line);
    if let Some(after) = rest.strip_prefix('[')
        && let Some(end) = after.find("] ")
    {
        let tag = &after[..end];
        if !tag.is_empty() && tag.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
            rest = &after[end + 2..];
        }
    }
    Ok(rest.to_string())
}

fn and_list(words: &[String]) -> String {
    match words {
        [] => String::new(),
        [one] => one.clone(),
        [first, second] => format!("{first} and {second}"),
        _ => {
            let (last, head) = words.split_last().expect("at least three");
            format!("{}, and {last}", head.join(", "))
        }
    }
}

pub fn render_files(paths: &Paths) -> Result<Vec<(PathBuf, String)>> {
    let inputs = load_inputs(paths)?;
    generate(
        &paths.root,
        &inputs.hosts,
        inputs.tiers.as_ref(),
        &inputs.verified,
        &inputs.gaps,
    )
}

struct ReportInputs {
    hosts: Vec<HostResult>,
    tiers: Option<TierDocument>,
    verified: Vec<VerifiedEntry>,
    gaps: Vec<DecidedGap>,
}

fn load_inputs(paths: &Paths) -> Result<ReportInputs> {
    let hosts = load_hosts(&paths.data())?;
    let tiers_path = paths.data().join("tiers.json");
    let tiers = if tiers_path.is_file() {
        Some(load_tier_file(&tiers_path)?.value)
    } else {
        None
    };
    let verified = load_verified(&paths.verified(), &paths.root)?;
    let gaps = load_gaps(&hosts, tiers.as_ref(), &paths.gaps(), &paths.root)?;
    Ok(ReportInputs {
        hosts,
        tiers,
        verified,
        gaps,
    })
}

pub fn render_check(paths: &Paths) -> Result<()> {
    let generated = existing_outputs(paths);
    let inputs = load_inputs(paths)?;
    if inputs.hosts.is_empty() && inputs.tiers.is_none() {
        if generated.is_empty() {
            return Ok(());
        }
        return Err(Error::new(
            "BENCHMARKS.md and its SVGs exist without results in benchmarks/data",
        ));
    }
    let files = generate(
        &paths.root,
        &inputs.hosts,
        inputs.tiers.as_ref(),
        &inputs.verified,
        &inputs.gaps,
    )?;
    let mut stale = Vec::new();
    for (path, content) in &files {
        let disk = fs::read_to_string(path).unwrap_or_default();
        if !path.is_file() || disk != *content {
            stale.push(path.clone());
        }
    }
    for path in &generated {
        if files.iter().all(|(got, _)| got != path) {
            stale.push(path.clone());
        }
    }
    if stale.is_empty() {
        Ok(())
    } else {
        let listed = stale
            .iter()
            .map(|path| relpath(path, &paths.root))
            .collect::<Vec<_>>()
            .join(", ");
        Err(Error::new(format!(
            "out of date, rerun `admin/bench-report render`: {listed}"
        )))
    }
}

pub fn render_write(paths: &Paths, from: Option<&Path>) -> Result<()> {
    if let Some(dir) = from {
        import_hosts(paths, dir)?;
    }
    let inputs = load_inputs(paths)?;
    if inputs.hosts.is_empty() && inputs.tiers.is_none() {
        return Err(Error::new(
            "no results in benchmarks/data: run `collect`, then `render --from DIR`",
        ));
    }
    let generated = existing_outputs(paths);
    let files = render_files(paths)?;
    for path in &generated {
        if files.iter().all(|(got, _)| got != path) {
            let _ = fs::remove_file(path);
        }
    }
    for (path, content) in &files {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|err| Error::new(err.to_string()))?;
        }
        fs::write(path, content).map_err(|err| Error::new(format!("{}: {err}", path.display())))?;
    }
    println!("{}", relpath(&paths.report(), &paths.root));
    Ok(())
}

fn existing_outputs(paths: &Paths) -> Vec<PathBuf> {
    let mut generated = Vec::new();
    if let Ok(dir) = fs::read_dir(paths.benchmarks()) {
        let mut svgs: Vec<PathBuf> = dir
            .filter_map(|entry| entry.ok())
            .map(|entry| entry.path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "svg"))
            .collect();
        svgs.sort();
        generated.extend(svgs);
    }
    if paths.report().is_file() {
        generated.push(paths.report());
    }
    generated
}

fn import_hosts(paths: &Paths, directory: &Path) -> Result<()> {
    fs::create_dir_all(paths.data()).map_err(|err| Error::new(err.to_string()))?;
    for spec in host_specs() {
        let path = directory.join(format!("{}.json", spec.name));
        if !path.is_file() {
            continue;
        }
        let host = load_host_file(&path)?;
        if host.value.status != "ok" {
            eprintln!(
                "bench-report: {}: not imported, {}: {}",
                spec.name,
                host.value.status,
                host.value.reason.as_deref().unwrap_or("")
            );
            continue;
        }
        fs::copy(&path, paths.data().join(format!("{}.json", spec.name)))
            .map_err(|err| Error::new(err.to_string()))?;
    }
    Ok(())
}
