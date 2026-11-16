// Every page the site has. Each gets a Markdown twin at its path with `.md`, a
// line in llms.txt, and a sitemap entry; scripts/check.ts fails a built page
// that is missing from here.
import * as landing from "./landing";
import { blocks, definitions, link, spans } from "./markdown";

export const origin = "https://rind.kixel.ai";

export interface Page {
	// The page's path, without a trailing slash.
	path: string;
	title: string;
	// What the page answers, for llms.txt and the page's description.
	answers: string;
	// The page's content as Markdown, saying what its HTML says.
	markdown: () => string;
}

// The Markdown twin's path: `/` has no name of its own, so it is `/index.md`.
export const twinPath = (page: Page) => (page.path === "/" ? "/index.md" : `${page.path}.md`);

export const home: Page = {
	path: "/",
	title: "rind",
	answers: `What rind is, the evidence for its claims, how to switch to it, and what to weigh before depending on it.`,
	markdown: () => {
		// The README's own words, with the definitions of the reference links they use.
		const quoted = [...landing.claims.flatMap((c) => c.body), ...landing.agent, ...landing.candor];
		return `${[
			definitions(quoted, landing.readme),
			"# rind",
			`**${landing.headline}**\n${landing.subline}`,
			...landing.claims.map((c) => `## ${c.icon} ${link(c.title, c.proof)}\n\n${spans(c.body)}`),
			"## Switch with an agent",
			blocks(landing.agent),
			`## ${landing.candorTitle}`,
			blocks(landing.candor),
			"## Links",
			landing.footer.map((l) => `- ${link(l.label, l.href)}`).join("\n"),
			`Built by ${link(landing.builtBy.label, landing.builtBy.href)}.`,
		]
			.filter((b) => b !== "")
			.join("\n\n")}\n`;
	},
};

export const pages: Page[] = [home];
