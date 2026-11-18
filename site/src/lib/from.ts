// A page per library rind stands in for, at /from/<slug>, each its adapter's
// README as src/lib/readme.ts chooses it, and /from, which lists them with
// MIGRATING.md's survey of the crates that pick a crypto backend for you.
import { type Token, type Tokens, walkTokens } from "marked";
import * as landing from "./landing";
import { blocks, definitions, lex, link, rebase, section, slugger } from "./markdown";
import type { Page } from "./pages";
import { choose, parse } from "./readme";
import { newest } from "./registry";
import { commit, read, repoUrl } from "./repo";
import { type Route, routes } from "./routes";

// A README with its relative links pointing at its directory on GitHub at
// `ref`, since the page is not there; a link within the README stays.
const absolute = (readme: string, crate: string, ref: string) =>
	rebase(readme, (href) =>
		/^[a-z][a-z0-9+.-]*:/i.test(href) || href.startsWith("#") ? href : new URL(href, `${repoUrl}/blob/${ref}/${crate}/`).href,
	);

// What one route's page quotes, and the note that opens it.
async function source(route: Route) {
	const { crate } = route;
	const manifest = Bun.TOML.parse(read(`${crate}/Cargo.toml`)) as { package: { version: string } };
	const main = { readme: read(`${crate}/README.md`), version: manifest.package.version, commit, repo: repoUrl };
	const chosen = choose(crate, main, await newest(crate));
	const readme = parse(absolute(chosen.readme.text, crate, chosen.ref), crate);
	// `choose` accepted this README, and only link destinations have changed.
	if (typeof readme === "string") throw new Error(`${crate}'s README lost its structure when its links were resolved: ${readme}`);
	return { readme, note: chosen.note };
}

// A link on a page to another page of the site.
const pageLink = (r: Route) => link(r.upstream, `/from/${r.slug}`);

// The agent prompt, from the README's "With an agent", which covers every route here.
const agent = ["## Switch with an agent", blocks(landing.agent)].join("\n\n");

async function page(route: Route): Promise<Page> {
	const { readme, note } = await source(route);
	const body = readme.body;
	const others = routes.filter((r) => r !== route);
	const markdown = [
		definitions(body, readme.tokens),
		definitions(landing.agent, landing.readme),
		`# ${route.title}`,
		note,
		blocks(body),
		agent,
		"## Other libraries",
		[...others.map((r) => `- ${pageLink(r)}`), `- ${link("Crates with their own crypto backend", "/from")}`].join("\n"),
	]
		.filter((b) => b !== "")
		.join("\n\n");
	return {
		path: `/from/${route.slug}`,
		title: route.title,
		answers: `${route.title}, through ${route.crate}: the Cargo.toml lines, the code that changes, and what rind cannot back.`,
		markdown: () => `${markdown}\n`,
	};
}

// MIGRATING.md's survey, with each link to one of its own headings kept where
// the survey has that heading, sent to the site's page where the heading is an
// adapter's, such as `#rind-ring`, and to GitHub otherwise, as are its
// relative paths.
const survey = "Crates with their own crypto backend";
function guide(): string {
	const text = read("MIGRATING.md");
	const doc = lex(text);
	const slug = slugger();
	const anchors = new Map<Token, string>();
	walkTokens(doc, (t) => void (t.type === "heading" && anchors.set(t, slug(t as Tokens.Heading))));
	const head = doc.find((t) => t.type === "heading" && t.text === survey);
	const kept = new Set([head, ...section(doc, survey)].flatMap((t) => anchors.get(t as Token) ?? []));
	const tokens = lex(
		rebase(text, (href) => {
			if (/^[a-z][a-z0-9+.-]*:/i.test(href) || href.startsWith("/")) return href;
			if (!href.startsWith("#")) return `${repoUrl}/blob/main/${href}`;
			const route = routes.find((r) => `#${r.crate}` === href);
			if (route) return `/from/${route.slug}`;
			return kept.has(href.slice(1)) ? href : `${repoUrl}/blob/main/MIGRATING.md${href}`;
		}),
	);
	const quoted = section(tokens, survey);
	return [definitions(quoted, tokens), `## ${survey}`, blocks(quoted)].filter((b) => b !== "").join("\n\n");
}

const index: Page = {
	path: "/from",
	title: "Move to rind from the library you use",
	answers:
		"Which page says how to move each library to rind, and which crates, such as reqwest, quinn, and sqlx, pick a crypto backend for you and how each moves.",
	markdown: () =>
		`${[
			definitions(landing.agent, landing.readme),
			"# Move to rind from the library you use",
			"Each page gives the change for one library: the `Cargo.toml` lines, the code that changes, and what rind cannot back.",
			routes.map((r) => `- ${pageLink(r)}`).join("\n"),
			`This survey is ${link("MIGRATING.md", `${repoUrl}/blob/main/MIGRATING.md`)}'s, as \`main\` has it.`,
			guide(),
			agent,
		].join("\n\n")}\n`,
};

export const fromPages: Page[] = [index, ...(await Promise.all(routes.map(page)))];
