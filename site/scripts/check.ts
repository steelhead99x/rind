// Checks the built site in dist/, offline: every page has its Markdown twin, a
// line in llms.txt, and a sitemap entry; every page carries the
// Content-Security-Policy that keeps it to its own origin; and every link into
// the site or the repository resolves, anchors included.
import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import path from "node:path";
import { Lexer, type Token, type Tokens, walkTokens } from "marked";
import { hrefs, lex } from "../src/lib/markdown";
import { origin, pages, twinPath } from "../src/lib/pages";
import { repoUrl, root } from "../src/lib/repo";

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

// The ids a built page's anchors can name.
const ids = (file: string) =>
	new Set([...tags(text(file))].flatMap(([, attrs]) => attrs.filter(([name]) => name === "id").map(([, value]) => value)));

// GitHub's anchor for each heading of a repository Markdown file, and each id
// or name its HTML gives, such as `<a name="x">`.
function anchors(file: string): Set<string> {
	// A heading's text, without the tags of any HTML in it, as GitHub reads it.
	const plain = (tokens: Token[]): string =>
		tokens
			.map((t) => (t.type === "html" ? "" : "tokens" in t && t.tokens ? plain(t.tokens) : "text" in t ? t.text : ""))
			.join("");
	// A repeated slug takes the next `-n` no earlier anchor holds, as github-slugger does,
	// so `Foo`, `Foo`, `Foo-1` are `foo`, `foo-1`, `foo-1-1`.
	const counts = new Map<string, number>();
	const out = new Set<string>();
	const tokens = Lexer.lex(readFileSync(path.join(root, file), "utf8"));
	// Every heading in document order, nested ones included, as each takes a slug.
	const headings: Tokens.Heading[] = [];
	walkTokens(tokens, (t) => void (t.type === "heading" && headings.push(t as Tokens.Heading)));
	for (const t of headings) {
		const base = plain(t.tokens)
			.toLowerCase()
			.replace(/[^\p{L}\p{M}\p{N}\p{Pc} -]/gu, "")
			.replaceAll(" ", "-");
		let slug = base;
		while (out.has(slug)) {
			const n = (counts.get(base) ?? 0) + 1;
			counts.set(base, n);
			slug = `${base}-${n}`;
		}
		out.add(slug);
	}
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
		if (fragment && !ids(found).has(fragment)) fail(`${from}: ${found} has no id "${fragment}"`);
		return;
	}
	if (u.protocol === "data:") return;
	if (u.protocol !== "https:") return fail(`${from}: ${url} is neither on this site nor https`);
	const located = `${u.origin}${u.pathname}`;
	const repoPath = located.match(blob)?.[1] ?? located.match(raw)?.[1];
	if (repoPath === undefined) return;
	const file = decodeURIComponent(repoPath).replace(/\/$/, "");
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
		for (const [, attrs] of tags(html)) {
			for (const [name, value] of attrs) if (name === "href") check(file, value);
		}
	} else if (file.endsWith(".md") || file.endsWith(".txt")) {
		// Links, which include URLs written bare in prose, as GFM autolinks them,
		// and URLs quoted in code, such as the prompt, as a reader copies them, up
		// to whitespace or a quote.
		const tokens = lex(text(file));
		for (const href of hrefs(tokens)) check(file, href);
		walkTokens(tokens, (t) => {
			if (t.type !== "code" && t.type !== "codespan") return;
			for (const m of t.text.matchAll(/https?:\/\/[^\s"'`<>]+/g)) check(file, m[0]);
		});
	}
}
for (const m of sitemap.matchAll(/<loc>([^<]+)<\/loc>/g)) check("/sitemap.xml", m[1]);

if (errors.size > 0) {
	for (const e of errors) console.error(`error: ${e}`);
	process.exit(1);
}
console.log(`site: ${built.length} page(s), ${files.length} files, and every link checked`);
