import type { APIRoute } from "astro";
import { readBytes } from "../lib/repo";

export const GET: APIRoute = () =>
	new Response(new Uint8Array(readBytes("rind-devbench/android/res/drawable-nodpi/kixel_mark.png")), {
		headers: { "Content-Type": "image/png" },
	});
