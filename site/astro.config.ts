import path from "node:path";
import svelte from "@astrojs/svelte";
import { defineConfig } from "astro/config";
import { root, sources } from "./src/lib/repo";

export default defineConfig({
	site: "https://rind.kixel.ai",
	output: "static",
	// `/` writes index.html, and a later `/from/ring` writes from/ring.html,
	// beside its twin from/ring.md.
	build: { format: "file" },
	integrations: [svelte()],
	devToolbar: { enabled: false },
	// The browser refuses anything not from the site itself. Astro writes the
	// policy as a <meta> on each page, adding the hashes of its inline scripts
	// and styles; scripts/check.ts holds every page to it, and
	// scripts/browser.ts loads each under it.
	security: {
		csp: { directives: ["default-src 'self'", "base-uri 'none'", "form-action 'none'"] },
	},
	vite: {
		plugins: [
			{
				// The dev server watches only site/, and the modules that read a
				// repository file keep what they read, so a change to one re-runs
				// them all and reloads the page.
				name: "repo-sources",
				configureServer(server) {
					const files = sources.map((f) => path.join(root, f));
					server.watcher.add(files);
					server.watcher.on("change", (file) => {
						if (!files.includes(file)) return;
						for (const env of Object.values(server.environments)) env.moduleGraph.invalidateAll();
						server.ws.send({ type: "full-reload" });
					});
				},
			},
		],
	},
});
