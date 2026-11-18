// The card a pasted link shows: the wordmark on the site's dark background, drawn
// from admin/ so a change to the wordmark changes the card. Most link previews
// refuse SVG, so it is a PNG, rendered by resvg's WebAssembly build, which runs
// the same on every runner.
import { readFileSync } from "node:fs";
import path from "node:path";
import { Resvg, initWasm } from "@resvg/resvg-wasm";
import type { APIRoute } from "astro";
import { card } from "../lib/card";
import { read } from "../lib/repo";

// The dev server loads this module again on each edit, and the renderer starts once per process.
await initWasm(readFileSync(path.resolve("node_modules/@resvg/resvg-wasm/index_bg.wasm"))).catch((e) => {
	if (!String(e).includes("Already initialized")) throw e;
});

export const GET: APIRoute = () => {
	const source = read("admin/wordmark.svg");
	const box = source.match(/viewBox="0 0 (\d+) (\d+)"/);
	if (!box) throw new Error("admin/wordmark.svg has no viewBox of the form 0 0 <width> <height>");
	const wordmark = Buffer.from(source).toString("base64");
	const height = 500;
	const width = Math.round((height * Number(box[1])) / Number(box[2]));
	const svg = `<svg xmlns="http://www.w3.org/2000/svg" width="${card.width}" height="${card.height}">
<rect width="100%" height="100%" fill="#12140d"/>
<image x="${(card.width - width) / 2}" y="${(card.height - height) / 2}" width="${width}" height="${height}" href="data:image/svg+xml;base64,${wordmark}"/>
</svg>`;
	const png = new Resvg(svg).render().asPng();
	return new Response(png, { headers: { "Content-Type": "image/png" } });
};
