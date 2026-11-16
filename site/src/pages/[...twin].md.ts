// Each page's Markdown twin, at its path with `.md`.
import type { APIRoute, GetStaticPaths } from "astro";
import { type Page, pages, twinPath } from "../lib/pages";

export const getStaticPaths = (() =>
	pages.map((page) => ({
		params: { twin: twinPath(page).slice(1, -".md".length) },
		props: { page },
	}))) satisfies GetStaticPaths;

export const GET: APIRoute<{ page: Page }> = ({ props }) =>
	new Response(props.page.markdown(), { headers: { "Content-Type": "text/markdown; charset=utf-8" } });
