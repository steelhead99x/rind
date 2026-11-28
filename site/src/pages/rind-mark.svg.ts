import type { APIRoute } from "astro";
import { peelSvg } from "../lib/favicon";

export const GET: APIRoute = () => new Response(peelSvg, { headers: { "Content-Type": "image/svg+xml" } });
