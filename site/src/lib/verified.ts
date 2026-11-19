// The verified page's data: which operations run proven code on which of the
// benchmark hosts, for each library. `admin/bench-report render` matches
// benchmarks/verified.toml's proofs to the hosts and writes the result into
// benchmarks/report.json, beside the benchmarks page's data, so the rule is
// written once, in Python, and the page only draws it.
import type { Host as ReportHost, VerifiedCell as Cell } from "./benchmarks";
import { report } from "./benchmarks";
import { link } from "./markdown";
import { repoUrl } from "./repo";

export type { Cell };

export interface Host {
	name: string;
	cpu: string;
	arch: string;
	os: "linux" | "macos";
	os_name: string;
	// The CPU features each library that refuses to start here requires.
	refused: Record<string, string[]>;
}

export interface Proof {
	library: string;
	operations: string[];
	platform: string;
	os?: "linux" | "macos";
	proof: string;
	link: string;
}

export const { rule } = report;

const measured: ReportHost[] = report.hosts;
export const hosts: Host[] = measured.map((h) => ({
	name: h.name,
	cpu: h.cpu,
	arch: h.arch,
	os: h.os_kind,
	os_name: h.os,
	refused: h.refused,
}));

// A library has a column when some host's grid has a cell for it.
export const libraries = report.libraries.filter((l) =>
	measured.some((h) => Object.values(h.grid).some((cells) => l.id in cells)),
);
const names = new Map(report.libraries.map((l) => [l.id, l.name]));

export const sections: { title: string; rows: { label: string; cells: Record<string, Cell[]> }[] }[] =
	report.sections.map((s) => ({
		title: s.name,
		rows: s.operations.map((op) => ({
			label: op.label,
			cells: Object.fromEntries(libraries.map((l) => [l.id, measured.map((h) => h.grid[op.id][l.id])])),
		})),
	}));

export const proofs: Proof[] = report.verified.map((p) => ({ ...p, library: names.get(p.library) ?? p.library }));

export const osName = { linux: "Linux", macos: "macOS" } as const;

// The anchor of a proof on the page.
export const proofId = (index: number) => `proof-${index + 1}`;

export interface Shown {
	// What the cell says: a ✓ only where a proof covers the operation here.
	text: string;
	// The cell's kind, which its style follows.
	kind: "proven" | "other-os" | "unproven" | "untimed" | "refused";
	// The proof the cell names, if any.
	proof?: number;
	// What the cell means, in words.
	title: string;
}

// What a library's cell for an operation on a host shows.
export function show(cell: Cell, host: Host, library: string): Shown {
	if (typeof cell === "number") {
		const os = proofs[cell].os;
		return {
			text: `✓ ${cell + 1}${os ? `, ${osName[os]} only` : ""}`,
			kind: "proven",
			proof: cell,
			title: `proven on ${host.name}${os ? `, on ${osName[os]} only` : ""}: ${proofs[cell].proof}`,
		};
	}
	if (typeof cell === "object") {
		const os = proofs[cell.other_os].os ?? host.os;
		return {
			text: `${osName[os]} only (${cell.other_os + 1})`,
			kind: "other-os",
			proof: cell.other_os,
			title: `proven on this CPU under ${osName[os]}, but not under ${osName[host.os]}, which ${host.name} runs`,
		};
	}
	if (cell === "refused") {
		const lacks = (host.refused[library] ?? []).map((f) => f.toUpperCase()).join(", ");
		return { text: "won't run", kind: "refused", title: `refuses to start on ${host.name}, which lacks ${lacks}` };
	}
	if (cell === "untimed") {
		return { text: "not timed", kind: "untimed", title: `no proof, and no time on ${host.name}` };
	}
	return { text: "no proof", kind: "unproven", title: `runs on ${host.name}, with no proof` };
}

// The number of operations a proof covers on a host, by library.
export const provenCount = (library: string, host: number) =>
	sections.flatMap((s) => s.rows).filter((r) => typeof r.cells[library][host] === "number").length;

export const operationCount = sections.reduce((n, s) => n + s.rows.length, 0);

// What rind's proofs trust, and the record of the proofs themselves.
export const trustBase = `${repoUrl}/blob/main/proofs/README.md#trust-base`;
export const verifiedToml = `${repoUrl}/blob/main/benchmarks/verified.toml`;
export const benchmarksMd = `${repoUrl}/blob/main/BENCHMARKS.md`;

// A host's column heading.
export const hostHeading = (h: Host) => `${h.name}: ${h.cpu}, ${osName[h.os]}`;

// The page's prose, which its HTML and its Markdown twin both say.
export const title = "Verified code, by CPU";
export const intro = [
	`Each operation the [benchmarks](${benchmarksMd}) time, for each library, on each benchmark host. A ✓ links the published formal proof that covers it there; every other cell says why it has none.`,
	rule,
	`A proof can be limited to an OS, where the bytes it checks are those of one OS's build: "Linux only" marks a ✓ that holds on that CPU under Linux and not under macOS, whose build [nothing checks yet](${repoUrl}/blob/main/quest/m4/verified/apple-bytes.md). rind's proofs trust the tools and specifications its [trust base](${trustBase}) lists. The proofs come from [\`benchmarks/verified.toml\`](${verifiedToml}), and a proof that lands there shows here on the next build.`,
];
export const legend: [string, string][] = [
	["✓ 7", "a proof covers the operation on this host: the seventh under Proofs, below"],
	["✓ 7, Linux only", "the seventh proof covers it here, under the OS it names and no other"],
	["Linux only (7)", "the seventh proof covers this CPU under the OS it names, which this host doesn't run"],
	["no proof", "the library runs the operation here, and nothing proves its code"],
	["not timed", "no proof, and the host has no time for it: the library doesn't offer it, or the host's results predate its benchmark"],
	["won't run", "the library refuses to start on this CPU, lacking a feature it requires"],
];
export const proofsLead =
	"Each proof, as `benchmarks/verified.toml` gives it. One for rind's portable backend, which runs where rind has no assembly, has no host column, since every host runs rind's assembly.";

// The page as Markdown, saying what its HTML says.
export function markdown(): string {
	const out = [`# ${title}`, ...intro, "## Legend", legend.map(([m, d]) => `- **${m}**: ${d}`).join("\n")];
	out.push(
		"## Summary",
		`Operations a proof covers, of the ${operationCount} the benchmarks time, by library and host.`,
		table(
			["Library", ...hosts.map(hostHeading)],
			libraries.map((lib) => [lib.name, ...hosts.map((_, i) => String(provenCount(lib.id, i)))]),
		),
	);
	for (const lib of libraries) {
		out.push(`## ${lib.name}`);
		for (const s of sections) {
			out.push(
				`### ${lib.name}: ${s.title}`,
				table(
					["Operation", ...hosts.map((h) => h.name)],
					s.rows.map((r) => [
						r.label,
						...r.cells[lib.id].map((c, i) => {
							const shown = show(c, hosts[i], lib.id);
							return shown.proof === undefined ? shown.text : link(shown.text, `#${proofId(shown.proof)}`);
						}),
					]),
				),
			);
		}
	}
	out.push(
		"## Proofs",
		proofsLead,
		proofs
			.map(
				(p, i) =>
					`${i + 1}. <a id="${proofId(i)}"></a>**${p.library}**, ${p.operations.map((o) => `\`${o}\``).join(", ")}, on ${p.platform}: ${link(p.proof, p.link)}`,
			)
			.join("\n"),
	);
	return `${out.join("\n\n")}\n`;
}

// A Markdown table, with pipes in cells escaped.
function table(head: string[], rows: string[][]): string {
	const line = (cells: string[]) => `| ${cells.map((c) => c.replaceAll("|", "\\|")).join(" | ")} |`;
	return [line(head), `|${"---|".repeat(head.length)}`, ...rows.map(line)].join("\n");
}
