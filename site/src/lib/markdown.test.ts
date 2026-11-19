import { expect, test } from "bun:test";
import { blocks, cell, definitions, hrefs, html, lex, rebase, section, segments, spans } from "./markdown";

// A section quoted with its definitions renders as it does inside its document.
test.each([
	// Reference links, full, collapsed, and shortcut, each alone, with their
	// definitions elsewhere.
	"[a][R]",
	"[r][]",
	"[r]",
	"[a\\]b][r]",
	"[a][multi  word]",
	"[Guide][a\\]b]",
	"[e]",
	// A definition the document nests in a blockquote outside the section.
	"[n]",
	// Spans and blocks the source wrote in a form a writer could get wrong.
	"_a*b_ and __a**b__",
	"[a\\]b](/guide)",
	"3. three\n4. four",
	"10. parent\n    - child",
	"- [ ] todo",
	"````text\n```\n````",
	"    value  ",
	// A definition between two lists keeps them apart.
	"- a\n\n[r]: /r\n\n- b",
	// One the fragment repeats, nested, loses to the document's first.
	"> [r]: /wrong\n\n[Guide][r]",
])("%s", (body) => {
	const doc = lex(
		`[r]: https://example.com/r\n[multi word]: </m (x)> "t"\n[a\\]b]: /guide\n[e]: <>\n\n> [n]: /nested\n\n## S\n\n${body}\n\n## T\n`,
	);
	const quoted = section(doc, "S");
	const twin = `${definitions(quoted, doc)}\n\n${blocks(quoted)}`;
	expect(html(lex(twin))).toBe(html(quoted));
});

test("spans quote inline source as written", () => {
	const [paragraph] = lex("a _b*c_ [d][r]\n\n[r]: /r");
	expect(spans((paragraph as { tokens: never[] }).tokens)).toBe("a _b*c_ [d][r]");
});

// Links in table cells, header and body, are found like any other.
test("hrefs reads table cells", () => {
	expect(hrefs(lex("| [Head](/head) |\n| --- |\n| [Missing](/missing) |"))).toEqual(["/head", "/missing"]);
});

// A rewritten link goes where it was sent, in each form Markdown writes one.
test("rebase rewrites inline links and definitions", () => {
	const source = '[a](x.md) [b](<x.md> "t") [c][d] [f](#x.md)\n\n[d]: x.md\n';
	const out = rebase(source, (href) => (href === "x.md" ? "https://example.com/x.md" : href));
	expect(hrefs(lex(out))).toEqual(["https://example.com/x.md", "https://example.com/x.md", "https://example.com/x.md", "#x.md"]);
});

// A destination is inserted as written, `$` and all.
test("rebase inserts a destination holding dollar signs literally", () => {
	const out = rebase("[a](x.md)\n\n[n]: x.md\n", () => "https://example.com/$$-$&.md");
	expect(hrefs(lex(out))).toEqual(["https://example.com/$$-$&.md"]);
});

// A definition may sit in a block quote, and its destination may start on the next line.
test("rebase finds definitions in a block quote and with the destination on the next line", () => {
	const out = rebase(
		"> [n]: x.md\n\nSee [n].\n\n[m]:\n  y.md\n\nAnd [m].\n\n> [k]:\n> z.md\n\n[k]\n",
		(href) => `https://example.com/${href}`,
	);
	expect(hrefs(lex(out))).toEqual(["https://example.com/x.md", "https://example.com/y.md", "https://example.com/z.md"]);
});

// A label may hold an escaped bracket, and keeps the case it was written in.
test("rebase keeps a definition's label", () => {
	const out = rebase("[Guide][a\\]B]\n\n[a\\]B]: guide.md\n", (href) => `/${href}`);
	expect(out).toBe("[Guide][a\\]B]\n\n[a\\]b]: /guide.md\n");
	expect(hrefs(lex(out))).toEqual(["/guide.md"]);
});

// The lexer drops a destination's backslash escapes, so the source spells it differently.
test("rebase finds a destination written with escapes", () => {
	const out = rebase("[a](x\\(1\\).md) [b](<x\\(1\\).md>)", (href) => `https://example.com/${href}`);
	expect(hrefs(lex(out))).toEqual(["https://example.com/x(1).md", "https://example.com/x(1).md"]);
});

// The label's escapes are the document's, not the token's.
test("rebase finds the destination after a label with an escaped bracket", () => {
	expect(rebase("[a\\]b](x.md)", (href) => `/${href}`)).toBe("[a\\]b](/x.md)");
});

// A badge is an image in a link, and each destination moves.
test("rebase reaches an image inside a link and a title", () => {
	const out = rebase('[![b](i.svg "t")](x.md "u")', (href) => `/${href}`);
	expect(out).toBe('[![b](/i.svg "t")](/x.md "u")');
});

// A list item's continuation lines lose their indentation in the token, not in the document.
test("rebase finds a link whose text wraps inside a list item", () => {
	const out = rebase("- see [a\n  b](x.md)\n", (href) => `/${href}`);
	expect(out).toBe("- see [a\n  b](/x.md)\n");
});

// Code that quotes a link is not a link, however early it comes.
test("rebase leaves code that quotes a link alone", () => {
	const out = rebase("`[e](x.md)` and [a](x.md)\n\n```md\n[e](x.md)\n```\n", () => "y.md");
	expect(out).toBe("`[e](x.md)` and [a](y.md)\n\n```md\n[e](x.md)\n```\n");
});

// GitHub slugs the heading as rendered, so `&amp;` is `&`, which the slug drops; a code span is literal.
test("a heading's anchor decodes character references outside code", () => {
	const html = (segments(lex("## A &amp; B\n\n## `&amp;` &eacute;\n"))[0] as { html: string }).html;
	expect(html).toContain('id="a--b"');
	expect(html).toContain('id="amp-é"');
	// An unterminated reference is literal text.
	expect((segments(lex("## &copycat\n"))[0] as { html: string }).html).toContain('id="copycat"');
});

// Each heading's id is GitHub's anchor for it.
test("segments give headings GitHub's anchors and set code apart", () => {
	const parts = segments(lex("# A b\n\n## A b\n\n```toml\nx = 1\n```\n\n## Ä_c?\n"));
	expect(parts).toEqual([
		{ html: '<h1 id="a-b">A b</h1>\n<h2 id="a-b-1">A b</h2>\n' },
		{ code: "x = 1", lang: "toml" },
		{ html: '<h2 id="ä_c">Ä_c?</h2>\n' },
	]);
});

// A cell's Markdown is inline, whatever it starts with.
test("cell reads one line inline", () => {
	expect(cell("- not [a](/a) `b`")).toBe('- not <a href="/a">a</a> <code>b</code>');
	expect(cell("# a | b")).toBe("# a | b");
});
