import type { APIRoute } from "astro";
import { origin, pages } from "../lib/pages";

export const GET: APIRoute = () =>
	new Response(
		[
			'<?xml version="1.0" encoding="UTF-8"?>',
			'<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">',
			...pages.map((p) => `<url><loc>${origin}${p.path}</loc></url>`),
			"</urlset>",
			"",
		].join("\n"),
	);
