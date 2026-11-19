// admin/'s wordmarks, served from the site: white `ind` for dark backgrounds.
import type { APIRoute } from "astro";
import { read } from "../lib/repo";

export const GET: APIRoute = () =>
	new Response(read("admin/wordmark.svg"), { headers: { "Content-Type": "image/svg+xml" } });
