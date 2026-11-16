// The index an agent reads first, in llmstxt.org's format: each page's
// Markdown twin and what it answers.
import type { APIRoute } from "astro";
import { headline, subline } from "../lib/landing";
import { origin, pages, twinPath } from "../lib/pages";

export const GET: APIRoute = () =>
	new Response(
		[
			"# rind",
			`> ${headline} ${subline}`,
			"## Pages",
			pages.map((p) => `- [${p.title}](${origin}${twinPath(p)}): ${p.answers}`).join("\n"),
		].join("\n\n") + "\n",
	);
