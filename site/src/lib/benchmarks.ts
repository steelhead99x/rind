// The benchmarks page's data: `admin/bench-report render` writes
// benchmarks/report.json, which decides what counts as the fastest, a proof,
// or a gap, so the page only lays it out.
import { lex, link, section } from "./markdown";
import type { Page } from "./pages";
import { read, repoUrl } from "./repo";

// A proof's index in `verified`; the same for a proof limited to an OS other
// than the host's; or why there is none.
export type VerifiedCell = number | { other_os: number } | "unproven" | "untimed" | "refused";

// A time as the report writes it, its speed bin, and its time over the fastest's.
export type Cell = [time: string, bin: number, ratio: number] | null;

interface Times {
	// The libraries timed, in the order of each row's cells.
	libraries: string[];
	times: Record<string, Cell[]>;
	// The library that counts as the fastest, where another library times the row too.
	fastest: Record<string, string>;
	// The index into `gaps` of the decision on rind's gap, by row.
	gaps: Record<string, number>;
}

export interface Host extends Times {
	name: string;
	cpu: string;
	arch: string;
	logical_cpus: number;
	os: string;
	rustc: string;
	date: string;
	commit: string;
	noisy: boolean;
	note: string | null;
	scaling: string | null;
	// The CPU features a library requires that this host lacks, by library.
	refused: Record<string, string[]>;
	// The index into `verified` of each proof, by row and library.
	proofs: Record<string, Record<string, number>>;
	// The host's OS, as a proof's `os` names it.
	os_kind: "linux" | "macos";
	// What each library's code shows for every operation here, timed or not, for the verified page.
	grid: Record<string, Record<string, VerifiedCell>>;
	build?: Build | { reason: string };
}

export interface Build {
	date: string;
	rustc: string;
	cc: string;
	jobs: string;
	builds: {
		name: string;
		library: string;
		seconds: number;
		low: number;
		high: number;
		cpu_seconds: number;
		stripped_mb: number;
		tools: string[];
		crates: number;
	}[];
}

export interface Tier extends Times {
	// The column's name, which names the AES-GCM path the runner drew.
	name: string;
	// The tier's name, as benchmarks/gaps.toml names it.
	tier: string;
	cpu: string;
	// The libraries its fastest is drawn from, which it may not have timed.
	rivals: string[];
}

export interface Gap {
	// A host's row, with its label, or a weekly benchmark ID, with none.
	operations: { id: string; label: string | null }[];
	on: { name: string; host: boolean }[];
	low: number;
	high: number;
	fastest: string[];
	quest: { path: string; title: string } | null;
	// Markdown.
	reason: string | null;
}

export interface Report {
	schema: 1;
	slower: number;
	// What earns a ✓, which BENCHMARKS.md and the verified page both state.
	rule: string;
	bins: { to: number | null; label: string; color: string }[];
	// rind's times that are the fastest or within 10%, and of how many.
	standing: [number, number];
	libraries: { id: string; name: string; variant_of: string | null }[];
	sections: { name: string; operations: { id: string; label: string }[] }[];
	hosts: Host[];
	unmeasured: string[];
	tiers: {
		// The libraries any tier's fastest is drawn from.
		rivals: string[];
		run: number;
		url: string;
		date: string;
		commit: string;
		columns: Tier[];
		groups: { name: string; benchmarks: string[] }[];
	} | null;
	gaps: Gap[];
	verified: {
		library: string;
		operations: string[];
		platform: string;
		os?: "linux" | "macos";
		proof: string;
		link: string;
	}[];
}

export const report = JSON.parse(read("benchmarks/report.json")) as Report;
if (report.schema !== 1) throw new Error(`benchmarks/report.json has schema ${report.schema}; the page reads 1`);
if (report.tiers === null) throw new Error("benchmarks/report.json has no CPU tiers");
export const tiers = report.tiers;

const names = new Map(report.libraries.map((l) => [l.id, l.name]));
export const libraryName = (id: string) => names.get(id) ?? id;

// Every library some host or tier times, in the report's order.
export const libraries = report.libraries.filter((l) =>
	[...report.hosts, ...tiers.columns].some((t) => t.libraries.includes(l.id)),
);

// A CPU a visitor picks: every host at once, one host, or one weekly tier.
export type Cpu = { id: string; label: string; detail: string } & (
	| { kind: "all" }
	| { kind: "host"; host: Host }
	| { kind: "tier"; tier: Tier }
);

// A CPU model as people say it: "Intel(R) Core(TM) i7-8700 CPU @ 3.20GHz" is
// "Core i7-8700", as the launch post's charts say it.
export const cpuName = (model: string) =>
	model
		.replace(/\((R|TM)\)/g, "")
		.replace(/^(Intel|AMD)\s+/, "")
		.replace(/\s+(CPU @.*|\d+-Core Processor)$/, "")
		.replace(/\s+/g, " ")
		.trim();

const slug = (name: string) =>
	name
		.toLowerCase()
		.replace(/[^a-z0-9]+/g, "-")
		.replace(/^-|-$/g, "");

export const all: Cpu = { id: "all", label: "Every host", detail: "one square per host", kind: "all" };
export const cpus: Cpu[] = [
	all,
	...report.hosts.map((host): Cpu => ({ id: host.name, label: host.name, detail: cpuName(host.cpu), kind: "host", host })),
	...tiers.columns.map((tier): Cpu => ({
		id: `ci-${slug(tier.name)}`,
		label: tier.name,
		detail: cpuName(tier.cpu),
		kind: "tier",
		tier,
	})),
];
if (new Set(cpus.map((c) => c.id)).size !== cpus.length) throw new Error("two CPUs on the benchmarks page share an id");

// The CPU a gap's place names, if the page shows it.
export const placeCpu = (place: Gap["on"][number]) =>
	cpus.find((c) => (place.host ? c.kind === "host" && c.host.name === place.name : c.kind === "tier" && c.tier.tier === place.name));

export const commitUrl = (sha: string) => `${repoUrl}/commit/${sha}`;
export const questUrl = (path: string) => `${repoUrl}/blob/main${path}`;
export const ratio = (r: number) => `${r.toFixed(2)}×`;

// What each library's cell in a row says beyond its time: whether it counts
// as the fastest, its proof, and rind's gap.
export function marks(t: Times & { proofs?: Host["proofs"] }, row: string, lib: string) {
	return {
		fastest: t.fastest[row] === lib,
		proof: t.proofs?.[row]?.[lib],
		gap: lib === "rind" ? t.gaps[row] : undefined,
	};
}

// What a host's rows leave out: operations it didn't time, and libraries it
// couldn't run.
export function untimed(host: Host): string[] {
	return report.sections.flatMap((s) => s.operations.filter((o) => !(o.id in host.times)).map((o) => o.label));
}

// The libraries any weekly tier's fastest is drawn from, in prose; the portable tier leaves verified-garbage out, as the paragraph quoted below says.
const tierLibraries = tiers.rivals.map(libraryName);
const tierNames = `${tierLibraries.slice(0, -1).join(", ")}, and ${tierLibraries.at(-1)}`;

// The report's paragraph on what each weekly tier denies, quoted up to where
// it turns to its own heatmap, which the page draws as a table per tier instead.
const benchmarksMd = lex(read("BENCHMARKS.md"));
const tierIntro = section(benchmarksMd, "CPU tiers").find((t) => t.type === "paragraph");
if (!tierIntro) throw new Error("BENCHMARKS.md's CPU tiers section has no paragraph");
const heatmapStart = tierIntro.raw.indexOf(" Each cell is ");
if (heatmapStart < 0) throw new Error("BENCHMARKS.md's CPU tiers paragraph no longer says where its cells begin");
export const tierMarkdown = `${tierIntro.raw.slice(0, heatmapStart).trim()} Each tier's table gives every benchmark it runs, each time with its time over the fastest of ${tierNames}; ring sits out a tier that denies a feature, since it can't be denied one; a benchmark a tier lacks runs the same code as the tier before it, so it isn't timed.`;

export const reportUrl = `${repoUrl}/blob/main/BENCHMARKS.md`;

// --- The Markdown twin -------------------------------------------------------

// A table cell's Markdown with each pipe it hasn't escaped escaped, so the cell holds it.
export const escapeCell = (c: string) =>
	c.replace(/(\\*)\|/g, (_, slashes: string) => (slashes.length % 2 ? `${slashes}|` : `${slashes}\\|`));
const row = (cells: string[]) => `| ${cells.map(escapeCell).join(" | ")} |`;
const table = (head: string[], rows: string[][]) =>
	[row(head), `|${"---|".repeat(head.length)}`, ...rows.map(row)].join("\n");

function cellText(t: Times & { proofs?: Host["proofs"] }, r: string, lib: string, cell: Cell): string {
	if (cell === null) return "-";
	const m = marks(t, r, lib);
	const parts = [m.fastest ? `**${cell[0]}**` : cell[0]];
	if (!m.fastest && t.fastest[r]) parts.push(`(${ratio(cell[2])})`);
	if (m.proof !== undefined) parts.push("✓");
	if (m.gap !== undefined) parts.push(`gap ${m.gap + 1}`);
	return parts.join(" ");
}

function timesTable(t: Times & { proofs?: Host["proofs"] }, rows: { id: string; label: string }[]): string {
	return table(
		["Operation", ...t.libraries.map(libraryName)],
		rows
			.filter((r) => r.id in t.times)
			.map((r) => [r.label, ...t.times[r.id].map((c, i) => cellText(t, r.id, t.libraries[i], c))]),
	);
}

export const hostMeasured = (h: Host) =>
	`${h.date} at ${link(h.commit.slice(0, 8), commitUrl(h.commit))}${h.noisy ? ", noisy" : ""}`;

export function decision(g: Gap): string {
	return g.quest ? link(g.quest.title, questUrl(g.quest.path)) : (g.reason ?? "");
}

export const gapOperations = (g: Gap) => g.operations.map((o) => o.label ?? `\`${o.id}\``).join(", ");
export const gapPlaces = (g: Gap) => g.on.map((p) => (p.host ? `\`${p.name}\`` : `${p.name} tier`)).join(", ");
export const gapRatio = (g: Gap) =>
	`${ratio(g.low)}${g.high - g.low >= 0.005 ? ` to ${ratio(g.high)}` : ""} (${g.fastest.join(", ")})`;

export const title = "Benchmarks";
export const lead = `How long rind and the usual Rust crypto libraries take for the same operations, on ${report.hosts.length} machines and ${tiers.columns.length} CPU tiers of GitHub's runners. Each library runs its native path on each CPU. The fastest time is in bold, every other says how far it trails, and one within ${Math.round((report.slower - 1) * 100)}% of the fastest counts as level with it, in the fastest's colour.`;
export const standingLine = `rind is the fastest, or within ${Math.round((report.slower - 1) * 100)}% of it, in ${report.standing[0]} of its ${report.standing[1]} timings on the hosts that another library also times.`;

function markdown(): string {
	const hosts = report.hosts.flatMap((h) => {
		const build = h.build;
		return [
			`### \`${h.name}\`: ${h.cpu}`,
			`Measured ${hostMeasured(h)}, on ${h.os} with ${h.rustc}.`,
			...(h.note ? [h.note] : []),
			...(untimed(h).length ? [`Not timed on \`${h.name}\`: ${untimed(h).join(", ")}.`] : []),
			...(h.scaling ? [h.scaling] : []),
			...Object.entries(h.refused).map(
				([lib, features]) =>
					`${libraryName(lib)} isn't timed on \`${h.name}\`: it requires ${features.join(", ")}, which this CPU lacks.`,
			),
			timesTable(
				h,
				report.sections.flatMap((s) => s.operations),
			),
			`#### Build cost on \`${h.name}\``,
			build === undefined
				? "Not measured."
				: "reason" in build
					? `Not measured: ${build.reason}`
					: [
							`Measured ${build.date} with ${build.rustc}, ${build.cc}, and ${build.jobs} jobs.`,
							table(
								["Build", "Wall s (range)", "CPU s", "Stripped MB", "Tools needed", "Crates"],
								build.builds.map((b) => [
									b.name,
									`${b.seconds.toFixed(1)} (${b.low.toFixed(1)} to ${b.high.toFixed(1)})`,
									`${b.cpu_seconds}`,
									b.stripped_mb.toFixed(2),
									b.tools.join(", ") || "none",
									`${b.crates}`,
								]),
							),
						].join("\n\n"),
		];
	});
	const tierTables = tiers.columns.flatMap((t) => [
		`### ${t.name}`,
		`On ${t.cpu}.`,
		timesTable(
			t,
			tiers.groups.flatMap((g) => g.benchmarks.map((id) => ({ id, label: `\`${id}\` (${g.name})` }))),
		),
	]);
	return `${[
		`# ${title}`,
		lead,
		standingLine,
		`Each cell is the library's time, then its time over the fastest's where it is not the fastest. The fastest is in bold, ✓ marks code a published formal proof covers, and "gap N" names rind's gap in Known gaps. The full report, with its method, is [BENCHMARKS.md](${reportUrl}).`,
		"## Hosts",
		table(
			["Host", "CPU", "OS", "Measured"],
			report.hosts.map((h) => [`\`${h.name}\``, h.cpu, h.os, hostMeasured(h)]),
		),
		...(report.unmeasured.length ? [`Not measured yet: ${report.unmeasured.map((n) => `\`${n}\``).join(", ")}.`] : []),
		...hosts,
		"## CPU tiers",
		tierMarkdown,
		`From ${link(`run ${tiers.run}`, tiers.url)}, ${tiers.date} at ${link(tiers.commit.slice(0, 8), commitUrl(tiers.commit))}.`,
		...tierTables,
		"## Known gaps",
		"Each operation where another library is more than 10% faster than rind, and what is decided: a quest that closes it, or the reason it stays.",
		table(
			["Gap", "Operation", "On", "rind's time over the fastest", "Decision"],
			report.gaps.map((g, i) => [`${i + 1}`, gapOperations(g), gapPlaces(g), gapRatio(g), decision(g)]),
		),
		"## Verified code",
		"A ✓ means a published, machine-checked proof shows that all the code computing the operation, as that library runs it on that host, gives the specified result for every input.",
		table(
			["Library", "Operations", "Platform", "Proof"],
			report.verified.map((v) => [
				libraryName(v.library),
				v.operations.map((o) => `\`${o}\``).join(", "),
				v.platform,
				link(v.proof, v.link),
			]),
		),
	].join("\n\n")}\n`;
}

// The libraries rind is timed against, in prose.
function others(): string {
	const names = libraries.filter((l) => l.id !== "rind" && l.variant_of === null).map((l) => l.name);
	return `${names.slice(0, -1).join(", ")}, and ${names.at(-1)}`;
}

export const benchmarks: Page = {
	path: "/benchmarks",
	title,
	answers: `How fast rind is against ${others()} on each measured CPU and CI tier, where it is slower and why, and which of the timed code is formally verified.`,
	markdown,
};
