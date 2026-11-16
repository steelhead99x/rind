import { Lexer, Parser, type Token, type Tokens, type TokensList, walkTokens } from "marked";

// Parse a Markdown document, resolving its reference links.
export function lex(source: string): TokensList {
	return Lexer.lex(source, { gfm: true });
}

// The blocks under the heading named `title`, up to the next heading as deep or shallower.
export function section(tokens: Token[], title: string): Token[] {
	const start = tokens.findIndex((t) => t.type === "heading" && t.text === title);
	if (start < 0) throw new Error(`the README has no heading "${title}"`);
	const depth = (tokens[start] as Tokens.Heading).depth;
	const rest = tokens.slice(start + 1);
	const end = rest.findIndex((t) => t.type === "heading" && t.depth <= depth);
	return end < 0 ? rest : rest.slice(0, end);
}

export const html = (blocks: Token[]): string => Parser.parse(blocks);
export const inlineHtml = (inline: Token[]): string => Parser.parseInline(inline);

// Blocks as their source wrote them, so a fragment of a document says exactly
// what the document does.
export const blocks = (tokens: Token[]): string =>
	tokens
		.filter((t) => t.type !== "space")
		.map((t) => t.raw.replace(/\n+$/, ""))
		.join("\n\n");

// Spans as their source wrote them.
export const spans = (tokens: Token[]): string =>
	tokens
		.map((t) => t.raw)
		.join("")
		.trim();

// The definitions in `source`, wherever it nests them, of the links `tokens`
// resolve, so a fragment of it reads on its own. They are matched by target, so
// no label needs parsing; one an inline link happens to share is harmless. They
// are the definitions that won in `source`, so they go before the fragment,
// since the first of a label's definitions wins over any the fragment repeats.
export function definitions(tokens: Token[], source: TokensList): string {
	const targets = new Set(links(tokens).map((t) => target(t.href, t.title)));
	return Object.entries(source.links)
		.filter(([, def]) => targets.has(target(def.href, def.title)))
		.map(([tag, def]) => `[${tag}]: ${target(def.href, def.title)}`)
		.join("\n");
}

// A link's destination and title as Markdown writes them: an empty destination,
// or one with spaces, parentheses, or angle brackets, goes between escaped angle
// brackets.
function target(href: string, title?: string | null): string {
	const dest = href === "" || /[\s()<>\\]/.test(href) ? `<${href.replace(/[<>\\]/g, "\\$&")}>` : href;
	return `${dest}${title ? ` "${title.replace(/["\\]/g, "\\$&")}"` : ""}`;
}

// A Markdown link to `href`, which may hold any character.
export const link = (label: string, href: string, title?: string | null): string =>
	`[${label}](${target(href, title)})`;

// Every link and image in some tokens, nested ones included.
function links(tokens: Token[]): (Tokens.Link | Tokens.Image)[] {
	const found: (Tokens.Link | Tokens.Image)[] = [];
	walkTokens(tokens, (t) => {
		if (t.type === "link" || t.type === "image") found.push(t as Tokens.Link | Tokens.Image);
	});
	return found;
}

// Every link target in some tokens, nested ones included.
export const hrefs = (tokens: Token[]): string[] =>
	links(tokens)
		.filter((t) => t.type === "link")
		.map((t) => t.href);
