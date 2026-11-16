import { existsSync, readFileSync } from "node:fs";
import path from "node:path";

// Astro builds from site/, so the repository is its parent.
export const root = path.resolve(process.cwd(), "..");
if (!existsSync(path.join(root, "site", "package.json"))) {
	throw new Error(`run the site's build from site/, not ${process.cwd()}`);
}

// Where the repository's files are on GitHub, as the README links them.
export const repoUrl = "https://github.com/kixel-ai/rind";

// The repository files the build reads, each through `read`, which the dev
// server watches so an edit to one reloads the page.
export const sources = ["README.md", "admin/wordmark.svg", "admin/wordmark-light.svg"] as const;

// Read one of `sources`.
export function read(file: (typeof sources)[number]): string {
	return readFileSync(path.join(root, file), "utf8");
}
