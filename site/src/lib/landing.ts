// The landing page's words, quoted from the README, so the README stays the one
// place to correct them.
import type { Token, Tokens } from "marked";
import { hrefs, lex, section } from "./markdown";
import { read, repoUrl } from "./repo";

export const readme = lex(read("README.md"));

// A reference link the README defines, such as `[docs]`.
function ref(name: string): string {
	const link = readme.links[name];
	if (!link) throw new Error(`the README defines no [${name}] link`);
	return link.href;
}

// The headline and the line under it, from the README's centered HTML block.
const intro = readme
	.filter((t): t is Tokens.HTML => t.type === "html")
	.map((t) => t.raw.match(/<strong>(.+?)<\/strong><br>\s*(.+?)\s*<\/p>/s))
	.find((m) => m !== null);
if (!intro) throw new Error("the README has no <strong> headline with a line under it");
export const headline = intro[1];
export const subline = intro[2];

// The site's page for a claim's proof, where it has one; the rest stay in BENCHMARKS.md.
const proofPages: Record<string, string> = {
	[`${repoUrl}/blob/main/BENCHMARKS.md`]: "/benchmarks",
	[`${repoUrl}/blob/main/BENCHMARKS.md#verified-code`]: "/verified",
};

export interface Claim {
	// The emoji the README opens the claim with.
	icon: string;
	title: string;
	// The claim's proof: its one link into BENCHMARKS.md, or the site's page for it.
	proof: string;
	body: Token[];
}

// The README's three claims: its first list, each item an emoji, a bold title, and the rest.
const list = readme.find((t): t is Tokens.List => t.type === "list");
if (!list) throw new Error("the README has no list of claims");
export const claims: Claim[] = list.items.map((item) => {
	const blocks = item.tokens.filter((t) => t.type !== "space");
	// A loose list's item holds a paragraph, a tight one's bare text.
	if (blocks.length !== 1 || (blocks[0].type !== "text" && blocks[0].type !== "paragraph")) {
		throw new Error(`a README claim must be one paragraph, which the page lays out as one: ${item.raw}`);
	}
	const spans = (blocks[0] as Tokens.Text | Tokens.Paragraph).tokens ?? [];
	const [lead, strong, ...body] = spans;
	if (lead?.type !== "text" || strong?.type !== "strong") {
		throw new Error(`a README claim must open with an emoji and a bold title: ${item.raw}`);
	}
	const proofs = hrefs(body).filter((href) => href.startsWith(`${repoUrl}/blob/main/BENCHMARKS.md`));
	if (proofs.length !== 1) {
		throw new Error(`a README claim must link BENCHMARKS.md once, as its proof: ${item.raw}`);
	}
	return { icon: lead.text.trim(), title: strong.text, proof: proofPages[proofs[0]] ?? proofs[0], body };
});
if (claims.length !== 3) throw new Error(`the README makes ${claims.length} claims; the page lays out three`);

// "With an agent": the paragraph introducing the prompt, the prompt, and the
// paragraph after it, which names the manual route.
export const agent = section(readme, "With an agent").filter((t) => t.type !== "space");
const [lead, code, ...after] = agent;
if (lead?.type !== "paragraph" || code?.type !== "code" || after.length === 0) {
	throw new Error("the README's With an agent section must be a paragraph, the prompt, and what follows");
}
export const agentLead: Token[] = [lead];
export const prompt = code.text;
export const agentAfter: Token[] = after;

export const candorTitle = "Before you depend on it";
export const candor = section(readme, candorTitle);

export const footer = [
	{ label: "GitHub", href: repoUrl },
	{ label: "crates.io", href: "https://crates.io/crates/rind" },
	{ label: "docs.rs", href: ref("docs") },
	{ label: "Launch post", href: ref("launch-post") },
	{ label: "MoQ", href: "https://moq.dev" },
];
export const builtBy = { label: "Kixel", href: "https://kixel.ai" };
