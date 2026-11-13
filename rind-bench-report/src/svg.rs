//! The report's hand-drawn SVGs. Numbers use the same format as Python's f-strings.

use indexmap::IndexMap;

use crate::format::human;
use crate::gaps::{TierPoint, times};
use crate::schema::{HostResult, TierDocument};
use crate::tables::{
    HOSTS, SLOWER, SPEED_BINS, SPEED_LABELS, TIER_BINS, TIER_LABELS, TIER_ROWS, Theme, column_name,
    columns as column_table, is_variant, label, operations, row_name, sections, variant_of,
};
use crate::verified::{VerifiedEntry, proof_for};

const SQUARE: f64 = 14.0;
const GAP: f64 = 2.0;
const ROW: f64 = 20.0;
const SECTION: f64 = 26.0;

pub fn bin_of(value: f64, edges: &[f64]) -> usize {
    edges
        .iter()
        .position(|edge| value <= *edge)
        .unwrap_or(edges.len())
}

fn text_width(text: &str, size: f64) -> f64 {
    text.chars().count() as f64 * size * 0.6
}

fn channel(hex: &str) -> f64 {
    let c = u32::from_str_radix(hex, 16).unwrap_or(0) as f64 / 255.0;
    if c <= 0.03928 {
        c / 12.92
    } else {
        ((c + 0.055) / 1.055).powf(2.4)
    }
}

fn luminance(color: &str) -> f64 {
    let r = channel(&color[1..3]);
    let g = channel(&color[3..5]);
    let b = channel(&color[5..7]);
    0.2126 * r + 0.7152 * g + 0.0722 * b
}

pub fn ink_on(fill: &str) -> &'static str {
    let lum = luminance(fill);
    if (lum + 0.05) / 0.05 > 1.05 / (lum + 0.05) {
        "#0b0b0b"
    } else {
        "#ffffff"
    }
}

fn esc(text: &str) -> String {
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

struct Svg<'a> {
    theme: &'a Theme,
    items: Vec<String>,
}

impl<'a> Svg<'a> {
    fn new(theme: &'a Theme) -> Self {
        Self {
            theme,
            items: Vec::new(),
        }
    }

    fn paint<'b>(&self, color: &'b str) -> &'b str {
        match color {
            "ink" => self.theme.ink,
            "muted" => self.theme.muted,
            "rule" => self.theme.rule,
            other => other,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn text(
        &mut self,
        x: f64,
        y: f64,
        text: &str,
        size: u32,
        anchor: &str,
        weight: &str,
        color: &str,
    ) {
        let fill = self.paint(color);
        self.items.push(format!(
            "<text x=\"{x:.1}\" y=\"{y:.1}\" font-size=\"{size}\" text-anchor=\"{anchor}\" font-weight=\"{weight}\" fill=\"{fill}\">{}</text>",
            esc(text)
        ));
    }

    fn rect(&mut self, x: f64, y: f64, w: f64, h: f64, fill: &str, title: Option<&str>) {
        let attrs = format!(
            "x=\"{x:.1}\" y=\"{y:.1}\" width=\"{w:.1}\" height=\"{h:.1}\" rx=\"2\" fill=\"{fill}\""
        );
        if let Some(title) = title {
            self.items.push(format!(
                "<rect {attrs}><title>{}</title></rect>",
                esc(title)
            ));
        } else {
            self.items.push(format!("<rect {attrs}/>"));
        }
    }

    fn verified(&mut self, x: f64, y: f64, size: f64, fill: &str) {
        let ink = ink_on(fill);
        let scale = size / 12.0;
        self.items.push(format!(
            "<g transform=\"translate({x:.1} {y:.1}) scale({scale:.3})\" pointer-events=\"none\"><path d=\"M6 0.6 L10.8 2.4 V5.8 C10.8 8.7 8.8 10.8 6 11.6 C3.2 10.8 1.2 8.7 1.2 5.8 V2.4 Z\" fill=\"{ink}\"/><path d=\"M3.7 6.1 L5.4 7.8 L8.4 4.5\" fill=\"none\" stroke=\"{fill}\" stroke-width=\"1.6\" stroke-linecap=\"round\" stroke-linejoin=\"round\"/></g>"
        ));
    }

    fn line(&mut self, x1: f64, y1: f64, x2: f64, y2: f64, color: &str) {
        let stroke = self.paint(color);
        self.items.push(format!(
            "<line x1=\"{x1:.1}\" y1=\"{y1:.1}\" x2=\"{x2:.1}\" y2=\"{y2:.1}\" stroke=\"{stroke}\"/>"
        ));
    }

    fn render(&self, width: f64, height: f64, title: &str) -> String {
        let font = crate::tables::FONT;
        let mut lines = vec![
            format!(
                "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width:.0}\" height=\"{height:.0}\" viewBox=\"0 0 {width:.0} {height:.0}\" font-family=\"{}\" role=\"img\">",
                esc(font)
            ),
            format!("<title>{}</title>", esc(title)),
        ];
        lines.extend(self.items.iter().cloned());
        lines.push("</svg>".to_string());
        lines.push(String::new());
        lines.join("\n")
    }
}

fn speed_legend(svg: &mut Svg, mut x: f64, y: f64) -> f64 {
    for (i, name) in SPEED_LABELS.iter().enumerate() {
        svg.rect(x, y - 10.0, 12.0, 12.0, svg.theme.speed[i], None);
        svg.text(x + 16.0, y, name, 11, "start", "normal", "muted");
        x += 16.0 + text_width(name, 11.0) + 12.0;
    }
    svg.rect(x, y - 10.0, 12.0, 12.0, svg.theme.speed[0], None);
    svg.verified(x + 1.0, y - 9.0, 10.0, svg.theme.speed[0]);
    svg.text(
        x + 16.0,
        y,
        "formally verified",
        11,
        "start",
        "normal",
        "muted",
    );
    x + 16.0 + text_width("formally verified", 11.0) + 12.0
}

fn grid_layout() -> (f64, f64) {
    let label_width = operations()
        .iter()
        .map(|op| text_width(&label(&row_name(op)), 12.0))
        .fold(0.0, f64::max)
        + 16.0;
    (label_width, 66.0)
}

pub fn header_lines(name: &str) -> Vec<String> {
    let chars: Vec<char> = name.chars().collect();
    let mut out = Vec::new();
    let mut start = 0;
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == ' ' && i + 1 < chars.len() && (chars[i + 1] == '+' || chars[i + 1] == '(') {
            out.push(chars[start..i].iter().collect());
            start = i + 1;
        }
        i += 1;
    }
    out.push(chars[start..].iter().collect());
    out
}

fn header_width(names: &[String]) -> f64 {
    names
        .iter()
        .flat_map(|name| header_lines(name))
        .map(|line| text_width(&line, 12.0))
        .fold(0.0, f64::max)
}

fn column_headers(svg: &mut Svg, x0: f64, y: f64, cell_width: f64, names: &[String]) {
    for (i, name) in names.iter().enumerate() {
        let cx = x0 + i as f64 * cell_width + cell_width / 2.0;
        let lines = header_lines(name);
        for (j, line) in lines.iter().enumerate() {
            let yy = y - 14.0 * (lines.len() - 1 - j) as f64;
            svg.text(cx, yy, line, 12, "middle", "bold", "ink");
        }
    }
}

fn timed_columns(hosts: &[&HostResult]) -> Vec<&'static str> {
    let mut timed = std::collections::HashSet::new();
    for host in hosts {
        if let Some(results) = &host.results {
            for row in results {
                timed.insert(row.library.as_str());
            }
        }
    }
    column_table()
        .iter()
        .filter(|(lib, _)| timed.contains(lib))
        .map(|(lib, _)| *lib)
        .collect()
}

fn host_times(host: &HostResult) -> Vec<(String, IndexMap<String, f64>)> {
    host.results.as_deref().map(times).unwrap_or_default()
}

fn lookup<'a>(
    rows: &'a [(String, IndexMap<String, f64>)],
    row: &str,
) -> Option<&'a IndexMap<String, f64>> {
    rows.iter()
        .find(|(name, _)| name == row)
        .map(|(_, libs)| libs)
}

/// Fastest non-variant time. Variants never set it.
fn fastest_ns(libs: &IndexMap<String, f64>) -> Option<f64> {
    libs.iter()
        .filter(|(lib, _)| !is_variant(lib))
        .map(|(_, ns)| *ns)
        .min_by(f64::total_cmp)
}

fn standing(hosts: &[&HostResult]) -> (usize, usize) {
    let mut lead = 0;
    let mut timed = 0;
    for host in hosts {
        for (_, libs) in host_times(host) {
            let Some(&rind) = libs.get("rind") else {
                continue;
            };
            if !libs.keys().any(|lib| lib != "rind" && !is_variant(lib)) {
                continue;
            }
            let Some(best) = fastest_ns(&libs) else {
                continue;
            };
            timed += 1;
            if rind / best <= SLOWER {
                lead += 1;
            }
        }
    }
    (lead, timed)
}

fn shown(hosts: &[HostResult]) -> Vec<&HostResult> {
    HOSTS
        .iter()
        .filter_map(|spec| hosts.iter().find(|host| host.host == spec.name))
        .collect()
}

pub fn overview_svg(hosts: &[HostResult], verified: &[VerifiedEntry], theme: &Theme) -> String {
    let svg_hosts = shown(hosts);
    let mut svg = Svg::new(theme);
    let libs_shown = timed_columns(&svg_hosts);
    let names: Vec<String> = libs_shown
        .iter()
        .map(|lib| column_name(lib).to_string())
        .collect();
    let squares =
        svg_hosts.len() as f64 * SQUARE + (svg_hosts.len().saturating_sub(1)) as f64 * GAP;
    let cell = (squares + 18.0).max(header_width(&names) + 12.0);
    let (label_width, mut top) = grid_layout();
    top += 28.0;
    let host_rows: Vec<_> = svg_hosts.iter().map(|host| host_times(host)).collect();
    let (lead, timed) = standing(&svg_hosts);
    let headline =
        format!("rind is the fastest, or within 10% of it, in {lead} of its {timed} times");
    svg.text(12.0, 22.0, &headline, 18, "start", "bold", "ink");
    let x = speed_legend(&mut svg, 12.0, 46.0).max(12.0 + text_width(&headline, 18.0) + 12.0);
    let width = x.max(label_width + cell * names.len() as f64 + 12.0);
    let listed = svg_hosts
        .iter()
        .map(|host| host.host.as_str())
        .collect::<Vec<_>>()
        .join(", ");
    svg.text(
        12.0,
        66.0,
        &format!("Each cell's squares, left to right: {listed}."),
        11,
        "start",
        "normal",
        "muted",
    );
    column_headers(&mut svg, label_width, top, cell, &names);
    let mut y = top + 8.0;
    for (section, ops) in sections() {
        y += SECTION;
        svg.text(12.0, y - 8.0, section, 12, "start", "bold", "ink");
        svg.line(12.0, y - 4.0, width - 12.0, y - 4.0, "rule");
        for op in ops {
            let row = row_name(op);
            svg.text(12.0, y + 14.0, &label(&row), 12, "start", "normal", "ink");
            for (c, lib) in libs_shown.iter().enumerate() {
                let x = label_width + c as f64 * cell + (cell - squares) / 2.0;
                for (h, host) in svg_hosts.iter().enumerate() {
                    let sx = x + h as f64 * (SQUARE + GAP);
                    let Some(libs) = lookup(&host_rows[h], &row) else {
                        continue;
                    };
                    let Some(&ns) = libs.get(*lib) else {
                        continue;
                    };
                    let Some(best) = fastest_ns(libs) else {
                        continue;
                    };
                    let ratio = ns / best;
                    let fill = svg.theme.speed[bin_of(ratio, SPEED_BINS)];
                    let proof = proof_for(verified, variant_of(lib), &row, host);
                    let mut title = format!(
                        "{}, {} on {}: {}, {ratio:.2}× the fastest",
                        label(&row),
                        column_name(lib),
                        host.host,
                        human(ns)
                    );
                    if let Some(proof) = proof {
                        title.push_str("; verified: ");
                        title.push_str(&proof.proof);
                    }
                    svg.rect(sx, y + 3.0, SQUARE, SQUARE, fill, Some(&title));
                    if proof.is_some() {
                        svg.verified(sx + 1.5, y + 4.5, SQUARE - 3.0, fill);
                    }
                }
            }
            y += ROW;
        }
    }
    svg.render(
        width,
        y + 12.0,
        "Time over the fastest library's, by operation, library, and host",
    )
}

pub fn host_svg(
    name: &str,
    host: &HostResult,
    verified: &[VerifiedEntry],
    theme: &Theme,
) -> String {
    let mut svg = Svg::new(theme);
    let cell = 92.0;
    let libs_shown = timed_columns(&[host]);
    let (label_width, top) = grid_layout();
    let mut width = label_width + cell * libs_shown.len() as f64 + 12.0;
    let x = speed_legend(&mut svg, 12.0, 18.0);
    width = width.max(x);
    let model = host
        .cpu
        .as_ref()
        .map(|cpu| cpu.model.as_str())
        .unwrap_or("");
    svg.text(
        12.0,
        38.0,
        &format!("{name}: {model}"),
        11,
        "start",
        "normal",
        "muted",
    );
    let names: Vec<String> = libs_shown
        .iter()
        .map(|lib| column_name(lib).to_string())
        .collect();
    column_headers(&mut svg, label_width, top, cell, &names);
    let rows = host_times(host);
    let mut y = top + 8.0;
    for (section, ops) in sections() {
        y += SECTION;
        svg.text(12.0, y - 8.0, section, 12, "start", "bold", "ink");
        svg.line(12.0, y - 4.0, width - 12.0, y - 4.0, "rule");
        for op in ops {
            let row = row_name(op);
            let libs = lookup(&rows, &row);
            svg.text(12.0, y + 14.0, &label(&row), 12, "start", "normal", "ink");
            for (c, lib) in libs_shown.iter().enumerate() {
                let x = label_width + c as f64 * cell + 2.0;
                let Some(libs) = libs else {
                    continue;
                };
                let Some(&ns) = libs.get(*lib) else {
                    continue;
                };
                let Some(best) = fastest_ns(libs) else {
                    continue;
                };
                let ratio = ns / best;
                let fill = svg.theme.speed[bin_of(ratio, SPEED_BINS)];
                let proof = proof_for(verified, variant_of(lib), &row, host);
                let mut title = format!(
                    "{}, {}: {}, {ratio:.2}× the fastest",
                    label(&row),
                    column_name(lib),
                    human(ns)
                );
                if let Some(proof) = proof {
                    title.push_str("; verified: ");
                    title.push_str(&proof.proof);
                }
                svg.rect(x, y + 1.0, cell - 4.0, ROW - 2.0, fill, Some(&title));
                let text = human(ns);
                let mid = x + (cell - 4.0) / 2.0 - if proof.is_some() { 7.0 } else { 0.0 };
                svg.text(mid, y + 14.0, &text, 11, "middle", "normal", ink_on(fill));
                if proof.is_some() {
                    svg.verified(
                        mid + text_width(&text, 11.0) / 2.0 + 3.0,
                        y + 4.0,
                        11.0,
                        fill,
                    );
                }
            }
            y += ROW;
        }
    }
    svg.render(
        width,
        y + 12.0,
        &format!("Times on {name}, by operation and library"),
    )
}

pub fn tier_columns(doc: &TierDocument) -> crate::Result<Vec<String>> {
    use crate::gaps::{tier_column, tier_name};
    use crate::tables::TIERS;
    let mut base = IndexMap::<String, &'static str>::new();
    for tier in &doc.tiers {
        base.insert(tier_column(tier)?, tier_name(tier)?);
    }
    let mut cols: Vec<String> = base.keys().cloned().collect();
    cols.sort_by(|a, b| {
        let ia = TIERS
            .iter()
            .position(|t| t.name == base[a])
            .unwrap_or(usize::MAX);
        let ib = TIERS
            .iter()
            .position(|t| t.name == base[b])
            .unwrap_or(usize::MAX);
        ia.cmp(&ib)
    });
    Ok(cols)
}

pub fn tier_cells(
    doc: &TierDocument,
) -> crate::Result<IndexMap<(String, String), (String, TierPoint)>> {
    use crate::gaps::{tier_column, tier_points, tier_row};
    let mut cells = IndexMap::new();
    for tier in &doc.tiers {
        let column = tier_column(tier)?;
        for (key, point) in tier_points(tier) {
            let Some(row) = tier_row(&key)? else {
                continue;
            };
            let slot = cells
                .entry((row.to_string(), column.clone()))
                .or_insert_with(|| (key.clone(), point.clone()));
            if point.ratio > slot.1.ratio {
                *slot = (key, point);
            }
        }
    }
    Ok(cells)
}

pub fn tiers_svg(doc: &TierDocument, theme: &Theme) -> crate::Result<String> {
    let mut svg = Svg::new(theme);
    let cells = tier_cells(doc)?;
    let columns = tier_columns(doc)?;
    let cell = 74.0;
    let label_width = TIER_ROWS
        .iter()
        .map(|(name, _)| text_width(name, 12.0))
        .fold(0.0, f64::max)
        + 16.0;
    let top = 52.0;
    let mut width = label_width + cell * columns.len() as f64 + 12.0;
    let mut x = 12.0;
    for (i, name) in TIER_LABELS.iter().enumerate() {
        svg.rect(x, 8.0, 12.0, 12.0, svg.theme.tier[i], None);
        svg.text(x + 16.0, 18.0, name, 11, "start", "normal", "muted");
        x += 16.0 + text_width(name, 11.0) + 12.0;
    }
    width = width.max(x);
    column_headers(&mut svg, label_width, top, cell, &columns);
    let mut y = top + 10.0;
    for (row, _) in TIER_ROWS {
        svg.text(12.0, y + 14.0, row, 12, "start", "normal", "ink");
        for (c, column) in columns.iter().enumerate() {
            let Some((key, point)) = cells.get(&(row.to_string(), column.clone())) else {
                continue;
            };
            let fill = svg.theme.tier[bin_of(point.ratio, TIER_BINS)];
            let title = format!(
                "{row} on {column}: {key} takes {} with rind, {} with {}",
                human(point.rind),
                human(point.best_ns),
                point.best
            );
            let x = label_width + c as f64 * cell + 2.0;
            svg.rect(x, y + 1.0, cell - 4.0, ROW - 2.0, fill, Some(&title));
            svg.text(
                x + (cell - 4.0) / 2.0,
                y + 14.0,
                &format!("{:.2}", point.ratio),
                11,
                "middle",
                "normal",
                ink_on(fill),
            );
        }
        y += ROW;
    }
    Ok(svg.render(
        width,
        y + 12.0,
        "rind's time over the fastest of aws-lc-rs and ring, by CPU tier",
    ))
}
