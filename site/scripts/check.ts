// Checks the built site in dist/, offline: every page has its Markdown twin, a
// line in llms.txt, and a sitemap entry; every page carries the
// Content-Security-Policy that keeps it to its own origin and the social card
// it names; a Markdown twin links the site's pages by their twins; and every
// link into the site or the repository resolves, anchors included. And
// inputs.txt, which sh/dispatch.sh reads to run the site's check only on diffs
// that can change it, lists every repository file the build reads, and every
// one the build, or a routed adapter's README as its next release will publish
// it, links with an anchor or line range.
import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import path from "node:path";
import { Lexer, type Tokens, walkTokens } from "marked";
import { hrefs, lex, slugger } from "../src/lib/markdown";
import { origin, pages, twinPath } from "../src/lib/pages";
import { read, repoUrl, root, sources } from "../src/lib/repo";
import { routes } from "../src/lib/routes";

const dist = path.resolve("dist");
const errors = new Set<string>();
const fail = (msg: string) => void errors.add(msg);

function walk(dir: string): string[] {
	return readdirSync(dir).flatMap((name) => {
		const full = path.join(dir, name);
		return statSync(full).isDirectory() ? walk(full) : [full];
	});
}
const files = walk(dist).map((f) => `/${path.relative(dist, f).split(path.sep).join("/")}`);
const text = (file: string) => readFileSync(path.join(dist, file), "utf8");

// The repository files whose edits run the site's check, besides site/ itself.
const inputs = new Set(
	readFileSync("inputs.txt", "utf8")
		.split("\n")
		.filter((line) => line !== "" && !line.startsWith("#")),
);
for (const file of sources) if (!inputs.has(file)) fail(`inputs.txt lacks ${file}, which the build reads`);
// An edit to a file a link names with a fragment can break the link.
const anchored = (from: string, file: string) =>
	inputs.has(file) || fail(`${from}: links ${file} with an anchor or line range, so inputs.txt must list it`);

// Pages, and what lists them.
const built = files
	.filter((f) => f.endsWith(".html"))
	.map((f) => (f === "/index.html" ? "/" : f.slice(0, -".html".length)));
const listed = new Set(pages.map((p) => p.path));
for (const page of built) if (!listed.has(page)) fail(`${page} is built but missing from src/lib/pages.ts`);
const llms = text("/llms.txt");
const sitemap = text("/sitemap.xml");
for (const page of pages) {
	if (!built.includes(page.path)) fail(`${page.path} is listed in src/lib/pages.ts but not built`);
	if (!files.includes(twinPath(page))) fail(`${page.path} has no Markdown twin at ${twinPath(page)}`);
	if (!llms.includes(`](${origin}${twinPath(page)})`)) fail(`llms.txt does not list ${twinPath(page)}`);
	if (!sitemap.includes(`<loc>${origin}${page.path}</loc>`)) fail(`sitemap.xml does not list ${page.path}`);
}

// The ids a built page's anchors can name: the ids in its HTML, or in a
// Markdown twin's, plus the anchors of the twin's headings.
function ids(file: string): Set<string> {
	const out = new Set(
		[...tags(text(file))].flatMap(([, attrs]) => attrs.filter(([name]) => name === "id").map(([, value]) => value)),
	);
	if (file.endsWith(".md")) {
		const slug = slugger();
		walkTokens(lex(text(file)), (t) => void (t.type === "heading" && out.add(slug(t as Tokens.Heading))));
	}
	return out;
}

// GitHub's anchor for each heading of a repository Markdown file, and each id
// or name its HTML gives, such as `<a name="x">`.
function anchors(file: string): Set<string> {
	const slug = slugger();
	const out = new Set<string>();
	const tokens = Lexer.lex(readFileSync(path.join(root, file), "utf8"));
	// Every heading in document order, nested ones included, as each takes a slug.
	walkTokens(tokens, (t) => void (t.type === "heading" && out.add(slug(t as Tokens.Heading))));
	walkTokens(tokens, (t) => {
		if (t.type !== "html") return;
		for (const [, attrs] of tags(t.raw)) {
			for (const [name, value] of attrs) if (name === "id" || name === "name") out.add(value);
		}
	});
	return out;
}

const blob = new RegExp(`^${repoUrl}/(?:blob|tree)/main/([^#?]+)`);
const raw = /^https:\/\/raw\.githubusercontent\.com\/kixel-ai\/rind\/main\/([^#?]+)/;

// The repository file on `main` a URL names, if it names one.
function repoFile(u: URL): string | undefined {
	const located = `${u.origin}${u.pathname}`;
	const repoPath = located.match(blob)?.[1] ?? located.match(raw)?.[1];
	return repoPath === undefined ? undefined : decodeURIComponent(repoPath).replace(/\/$/, "");
}

// The links in Markdown, which include URLs written bare in prose, as GFM
// autolinks them, and URLs quoted in code, such as the prompt, as a reader
// copies them, up to whitespace or a quote.
function links(markdown: string): string[] {
	const tokens = lex(markdown);
	const out = hrefs(tokens);
	walkTokens(tokens, (t) => {
		if (t.type !== "code" && t.type !== "codespan") return;
		for (const m of t.text.matchAll(/https?:\/\/[^\s"'`<>]+/g)) out.push(m[0]);
	});
	return out;
}

// Check one link found in `from`, resolved against it as a browser would.
function check(from: string, url: string) {
	let u: URL;
	let target: string;
	let fragment: string;
	try {
		u = new URL(url, `${origin}${from}`);
		target = decodeURIComponent(u.pathname);
		fragment = decodeURIComponent(u.hash.slice(1));
	} catch {
		return fail(`${from}: ${url} is not a valid URL`);
	}
	if (u.origin === origin) {
		const file = target.endsWith("/") ? `${target}index.html` : target;
		const found = [file, `${file}.html`].find((f) => files.includes(f));
		if (!found) return fail(`${from}: ${url} is not in the build`);
		if (from.endsWith(".md") && found.endsWith(".html")) fail(`${from}: ${url} is a page, so a twin links its Markdown`);
		if (fragment && !ids(found).has(fragment)) fail(`${from}: ${found} has no id "${fragment}"`);
		return;
	}
	if (u.protocol === "data:") return;
	if (u.protocol !== "https:") return fail(`${from}: ${url} is neither on this site nor https`);
	const file = repoFile(u);
	if (file === undefined) return;
	if (fragment) anchored(from, file);
	if (!existsSync(path.join(root, file))) return fail(`${from}: ${url} names ${file}, which the repository lacks`);
	if (fragment && !(file.endsWith(".md") ? anchors(file).has(fragment) : hasLines(file, fragment))) {
		fail(`${from}: ${url} names an anchor ${file} lacks`);
	}
}

// Whether a file GitHub shows as source has the line, or range, `#L5` or
// `#L5-L9` names.
function hasLines(file: string, fragment: string): boolean {
	const full = path.join(root, file);
	const range = fragment.match(/^L(\d+)(?:-L(\d+))?$/);
	if (range === null || statSync(full).isDirectory()) return false;
	const text = readFileSync(full, "utf8");
	const count = text === "" ? 0 : text.split("\n").length - (text.endsWith("\n") ? 1 : 0);
	return range.slice(1).every((n) => n === undefined || (Number(n) >= 1 && Number(n) <= count));
}

// A numeric character reference's character, or U+FFFD where HTML gives one
// for zero, a surrogate, or a value past Unicode.
const codePoint = (n: number) =>
	n === 0 || n > 0x10ffff || (n >= 0xd800 && n <= 0xdfff) ? "\ufffd" : String.fromCodePoint(n);

// Each start tag's lowercased name and attributes, however their values are
// quoted, with character references in the values decoded.
function* tags(html: string): Generator<[string, [string, string][]]> {
	const decode = (v: string) =>
		v.replace(/&(?:#(\d+)|#x([\da-f]+)|(amp|quot|apos|lt|gt));/gi, (_, dec, hex, named) =>
			dec || hex
				? codePoint(Number.parseInt(dec ?? hex, dec ? 10 : 16))
				: { amp: "&", quot: '"', apos: "'", lt: "<", gt: ">" }[named.toLowerCase() as "amp"],
		);
	const tag = /<([a-z][^\s/>]*)((?:\s*[^\s"'>/=]+(?:\s*=\s*(?:"[^"]*"|'[^']*'|[^\s"'=<>`]+))?)*)\s*\/?>/gi;
	const attr = /([^\s"'>/=]+)(?:\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s"'=<>`]+)))?/g;
	// Script and style bodies are raw text, and comments hold no tags.
	const markup = html
		.replace(/<!--[\s\S]*?-->/g, "")
		.replace(/(<(script|style)\b[^>]*>)[\s\S]*?<\/\2\s*>/gi, "$1");
	for (const m of markup.matchAll(tag)) {
		const attrs = [...m[2].matchAll(attr)].map((a): [string, string] => [
			a[1].toLowerCase(),
			decode(a[2] ?? a[3] ?? a[4] ?? ""),
		]);
		yield [m[1].toLowerCase(), attrs];
	}
}

// The browser refuses whatever a page's policy does not allow, so each page
// must carry one that allows its own origin and the inline code whose hashes
// Astro adds, and nothing else. It covers only what follows it, and Astro puts
// it after the layout's own head tags, so those may only be ones that load
// nothing from off the page.
const allowed = /^(?:'self'|'none'|'sha(?:256|384|512)-[A-Za-z0-9+/]+={0,2}')$/;
function inert(tag: string, attr: Map<string, string>): boolean {
	const rel = attr.get("rel")?.toLowerCase();
	if (["html", "head", "title"].includes(tag)) return true;
	if (tag === "meta") return !attr.has("http-equiv");
	if (tag !== "link") return false;
	return rel === "canonical" || rel === "alternate" || (rel === "icon" && !!attr.get("href")?.startsWith("data:"));
}
function policy(file: string, html: string) {
	for (const [tag, attrs] of tags(html)) {
		const attr = new Map(attrs);
		if (tag === "meta" && attr.get("http-equiv")?.toLowerCase() === "content-security-policy") {
			const directives = (attr.get("content") ?? "").split(";").map((d) => d.trim().split(/\s+/));
			if (!directives.some(([name, ...sources]) => name === "default-src" && sources.join(" ") === "'self'")) {
				fail(`${file}: its Content-Security-Policy lacks default-src 'self'`);
			}
			for (const [name, ...sources] of directives) {
				for (const source of sources) {
					if (!allowed.test(source)) fail(`${file}: its Content-Security-Policy lets ${name} load ${source}`);
				}
			}
			return;
		}
		if (!inert(tag, attr)) {
			return fail(`${file}: <${tag}> comes before the Content-Security-Policy, which covers only what follows it`);
		}
	}
	fail(`${file}: has no Content-Security-Policy`);
}

for (const file of files) {
	if (file.endsWith(".html")) {
		const html = text(file);
		policy(file, html);
		for (const [tag, attrs] of tags(html)) {
			for (const [name, value] of attrs) if (name === "href") check(file, value);
			// The card a pasted link shows is read from the page, so it must be in the build.
			if (tag === "meta" && attrs.some(([n, v]) => n === "property" && v === "og:image")) {
				check(file, attrs.find(([n]) => n === "content")?.[1] ?? "");
			}
		}
	} else if (file.endsWith(".md") || file.endsWith(".txt")) {
		for (const href of links(text(file))) check(file, href);
	}
}
// A page can quote an adapter's README from crates.io rather than this
// checkout, so a release can change the site's links with no change here. A
// README's relative links resolve into its release's tag, which this check
// does not follow, so only those that reach `main` count.
for (const { crate } of routes) {
	const from = `${crate}/README.md`;
	for (const href of links(read(from))) {
		let u: URL;
		try {
			// As src/lib/from.ts resolves it on a release's page.
			u = new URL(href, `${repoUrl}/blob/${crate}-v0.0.0/${crate}/`);
		} catch {
			continue;
		}
		let file: string | undefined;
		try {
			file = repoFile(u);
		} catch {
			fail(`${from}: ${href} is not a valid URL`);
			continue;
		}
		if (file !== undefined && u.hash.length > 1) anchored(from, file);
	}
}
for (const m of sitemap.matchAll(/<loc>([^<]+)<\/loc>/g)) check("/sitemap.xml", m[1]);

if (errors.size > 0) {
	for (const e of errors) console.error(`error: ${e}`);
	process.exit(1);
}
console.log(`site: ${built.length} page(s), ${files.length} files, and every link checked`);
