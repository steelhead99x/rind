// RFC 9116's security.txt: where to report a vulnerability. The RFC requires
// an expiry under a year away, so each build sets one 180 days on, and every
// merge to main deploys a build.
import type { APIRoute } from "astro";
import { origin } from "../../lib/pages";
import { repoUrl } from "../../lib/repo";

const days = 180;

export const GET: APIRoute = () =>
	new Response(
		[
			`Contact: ${repoUrl}/security/advisories/new`,
			`Expires: ${new Date(Date.now() + days * 24 * 60 * 60 * 1000).toISOString()}`,
			"Preferred-Languages: en",
			`Canonical: ${origin}/.well-known/security.txt`,
			`Policy: ${repoUrl}/blob/main/SECURITY.md`,
		].join("\n") + "\n",
	);
