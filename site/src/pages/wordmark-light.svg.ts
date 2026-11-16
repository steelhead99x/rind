// admin/'s wordmark with dark `ind`, for light backgrounds.
import type { APIRoute } from "astro";
import { read } from "../lib/repo";

export const GET: APIRoute = () =>
	new Response(read("admin/wordmark-light.svg"), { headers: { "Content-Type": "image/svg+xml" } });
