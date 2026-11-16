import { expect, test } from "bun:test";
import { blocks, definitions, hrefs, html, lex, section, spans } from "./markdown";

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
