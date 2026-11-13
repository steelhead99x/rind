//! `summary`: rind's time against the fastest other library.

use std::path::Path;

use indexmap::IndexMap;

use crate::error::Result;
use crate::format::human;
use crate::schema::load_host_file;
use crate::tables::{hosts, is_variant, operations, row_name};

pub fn summary(dir: &Path) -> Result<String> {
    let mut loaded = Vec::new();
    for spec in hosts() {
        let path = dir.join(format!("{}.json", spec.name));
        if path.is_file() {
            loaded.push(load_host_file(&path)?);
        }
    }
    let mut out = String::new();
    let mut measured = Vec::new();
    for host in &loaded {
        if host.value.status == "ok" {
            let noisy = if host.value.load.as_ref().and_then(|load| load.noisy) == Some(true) {
                " (noisy)"
            } else {
                ""
            };
            let model = host
                .value
                .cpu
                .as_ref()
                .map(|cpu| cpu.model.as_str())
                .unwrap_or("");
            let os = host.value.os.as_deref().unwrap_or("");
            let rustc = host
                .value
                .toolchain
                .as_ref()
                .map(|tool| tool.rustc.as_str())
                .unwrap_or("");
            out.push_str(&format!(
                "- `{}`: {model}, {os}, {rustc}{noisy}\n",
                host.value.host
            ));
            measured.push(host);
        } else {
            out.push_str(&format!(
                "- `{}`: not measured, {}: {}\n",
                host.value.host,
                host.value.status,
                host.value.reason.as_deref().unwrap_or("")
            ));
        }
    }
    if measured.is_empty() {
        return Ok(out);
    }
    out.push('\n');
    out.push_str("Each cell is rind's time, then that over the fastest other library's, and which library that is.\n");
    out.push('\n');
    out.push_str("| operation | ");
    out.push_str(
        &measured
            .iter()
            .map(|host| host.value.host.as_str())
            .collect::<Vec<_>>()
            .join(" | "),
    );
    out.push_str(" |\n");
    out.push_str("|---|");
    out.push_str(&"---|".repeat(measured.len()));
    out.push('\n');
    for op in operations() {
        let mut cells = Vec::new();
        for host in &measured {
            let results = host.value.results.as_deref().unwrap_or(&[]);
            let mut times: IndexMap<&str, f64> = IndexMap::new();
            for row in results {
                if row.operation == *op {
                    times.insert(row.library.as_str(), row.ns);
                }
            }
            let rind = times.get("rind").copied();
            let mut best_lib = None;
            let mut best_ns = f64::INFINITY;
            for (lib, ns) in &times {
                if *lib != "rind" && !is_variant(lib) && *ns < best_ns {
                    best_ns = *ns;
                    best_lib = Some(*lib);
                }
            }
            match (rind, best_lib) {
                (Some(ns), Some(lib)) => {
                    cells.push(format!("{}, {:.2}× {lib}", human(ns), ns / best_ns));
                }
                _ => cells.push("-".to_string()),
            }
        }
        out.push_str(&format!("| {} | {} |\n", row_name(op), cells.join(" | ")));
    }
    Ok(out)
}
