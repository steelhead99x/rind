// Which README an adapter's page quotes: the one its newest crates.io release
// shipped, so the page's steps and dependency lines describe the same code, or
// `main`'s, with the line that takes the crate from git, where that release
// predates the structure a page needs or there is no release.
import { type Tokens, type TokensList, walkTokens } from "marked";
import { blocks, lex, link } from "./markdown";
import type { Release } from "./registry";

// The heading every adapter README gives the list of what rind cannot back.
export const cannotBack = "What rind cannot back";

// What `parse` says first of a README that has the structure but is broken, as
// against one that lacks it.
const malformed = "it is malformed: ";

// The parts of an adapter README a page needs.
export interface Readme {
	// The README as its source wrote it.
	text: string;
	tokens: TokensList;
	// The blocks after the README's title, logo, and badges, up to its license line.
	body: Tokens.Generic[];
	// Each version requirement its `toml` blocks put on the crate.
	requirements: string[];
}

// An adapter README's parts, or what it lacks that a page needs.
export function parse(text: string, crate: string): Readme | string {
	const tokens = lex(text);
	const all = tokens.filter((t) => t.type !== "space");
	let start = 0;
	while (all[start]?.type === "html") start++;
	// The badges: a paragraph of linked images alone.
	const badges = all[start];
	if (
		badges?.type === "paragraph" &&
		(badges as Tokens.Paragraph).tokens.every(
			(t) => (t.type === "link" && t.tokens?.every((i) => i.type === "image")) || /^\s*$/.test(t.raw),
		)
	) {
		start++;
	}
	if (start === 0) return "it opens with no title or badges";
	let end = all.length;
	if (all[end - 1]?.type === "paragraph" && all[end - 1].raw.startsWith("License:")) end--;
	const body = all.slice(start, end);
	// A release's README is a stranger's text (anyone may publish a crate not yet
	// released), and a page shows it only as Markdown, never as markup.
	let markup = false;
	walkTokens(body, (t) => void (t.type === "html" && (markup = true)));
	if (markup) return `${malformed}its body holds raw HTML`;
	if (!body.some((t) => t.type === "heading" && t.depth === 2 && t.text === cannotBack)) {
		return `it has no "## ${cannotBack}" section`;
	}
	let requirements: string[];
	try {
		requirements = body
			.filter((t): t is Tokens.Code => t.type === "code" && t.lang === "toml")
			.flatMap((t) => requirementsOn(Bun.TOML.parse(t.text), crate));
	} catch (e) {
		return `${malformed}${e instanceof Error ? e.message : e}`;
	}
	if (requirements.length === 0) return `no toml block in it depends on ${crate}`;
	return { text, tokens, body, requirements };
}

// The version requirements a Cargo.toml fragment puts on `crate`, under any
// table, renamed or not. One with no version, such as a path, is refused.
function requirementsOn(toml: unknown, crate: string): string[] {
	if (typeof toml !== "object" || toml === null) return [];
	return Object.entries(toml).flatMap(([key, spec]) => {
		const named = typeof spec === "object" && spec !== null && "package" in spec ? spec.package === crate : key === crate;
		if (!named) return requirementsOn(spec, crate);
		const version = typeof spec === "string" ? spec : (spec as { version?: unknown }).version;
		if (typeof version !== "string") throw new Error(`a toml block names ${crate} without a version`);
		return [version];
	});
}

// Whether `version` meets a Cargo requirement, where a bare version means `^`.
export function meets(version: string, requirement: string): boolean {
	const range = requirement
		.split(",")
		.map((part) => part.trim())
		.map((part) => (/^\d/.test(part) ? `^${part}` : part))
		.join(" ");
	return Bun.semver.satisfies(version, range);
}

function requireMet(crate: string, version: string, readme: Readme, which: string) {
	for (const req of readme.requirements) {
		if (!meets(version, req)) throw new Error(`${which} README asks for ${crate} "${req}", which ${version} does not meet`);
	}
}

export interface Main {
	readme: string;
	// The version `main`'s manifest gives the crate.
	version: string;
	// The commit the build reads.
	commit: string;
	repo: string;
}

// The README a page quotes, the git ref (a tag, or the build's commit) its relative links point into, and the
// note that opens the page saying which code it describes. The two READMEs are
// compared as written, since the links in each would differ by ref alone.
export function choose(crate: string, main: Main, release: Release | null): { readme: Readme; ref: string; note: string } {
	const ours = parse(main.readme, crate);
	if (typeof ours === "string") throw new Error(`${crate}/README.md cannot make its page: ${ours}`);
	// The patch reaches the README's requirements only where `main`'s version meets them.
	requireMet(crate, main.version, ours, "main's");
	const fromGit = ["```toml", `${crate} = { git = "${main.repo}", rev = "${main.commit}" }`, "```"].join("\n");
	// A lockfile that already holds the release keeps it until the crate is updated.
	const steps = `add this line under the \`[patch.crates-io]\` table of your workspace's root \`Cargo.toml\` (add the table if it has none), then run \`cargo update -p ${crate}\`:\n\n${fromGit}\n\nThat moves every crate in your tree that depends on ${crate}, and \`cargo tree -i ${crate}\` then shows it from \`git+${main.repo}\`.`;

	const published = release ? parse(release.readme, crate) : "there is no release";
	if (release && typeof published !== "string") {
		requireMet(crate, release.version, published, `${crate} ${release.version}'s`);
		const note = `This page is the README of ${crate} ${release.version}, its newest release on crates.io.`;
		// release-plz tags each crate's release `<crate>-v<version>`.
		const ref = `${crate}-v${release.version}`;
		if (blocks(published.body) === blocks(ours.body)) return { readme: published, ref, note };
		const there = link("its README", `${main.repo}/blob/main/${crate}/README.md`);
		return {
			readme: published,
			ref,
			note: `${note} \`main\` has changed it since. To build against \`main\`, as ${there} describes it, ${steps}`,
		};
	}
	const lead = release
		? `This page describes ${crate} as \`main\` has it, ahead of ${link(`${crate} ${release.version}`, `https://crates.io/crates/${crate}/${release.version}`)} on crates.io. Until its next release, take it from git at the commit this page describes`
		: `${crate} is unreleased: this page describes it as \`main\` has it. Until its first release, take it from git at the commit this page describes`;
	// A release README that has the structure but is broken is said to be, so a
	// page that falls back to `main` does not look as if it only predates it.
	const flaw =
		release && typeof published === "string" && published.startsWith(malformed)
			? ` ${crate} ${release.version}'s README is malformed (${published.slice(malformed.length)}), so this page does not quote it.`
			: "";
	return {
		readme: ours,
		ref: main.commit,
		note: `${lead}.${flaw} Beside the lines below, ${steps}`,
	};
}
