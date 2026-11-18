import { execFileSync } from "node:child_process";
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import { routes } from "./routes";

// Astro builds from site/, so the repository is its parent.
export const root = path.resolve(process.cwd(), "..");
if (!existsSync(path.join(root, "site", "package.json"))) {
	throw new Error(`run the site's build from site/, not ${process.cwd()}`);
}

// Where the repository's files are on GitHub, as the README links them.
export const repoUrl = "https://github.com/kixel-ai/rind";

// The repository files the build reads, each through `read`, which the dev
// server watches so an edit to one reloads the page.
export const sources = [
	"README.md",
	"BENCHMARKS.md",
	"MIGRATING.md",
	"benchmarks/report.json",
	"admin/wordmark.svg",
	"admin/wordmark-light.svg",
	...routes.flatMap((r) => [`${r.crate}/README.md`, `${r.crate}/Cargo.toml`]),
];

// Read one of `sources`.
export function read(file: string): string {
	if (!sources.includes(file)) throw new Error(`${file} is missing from src/lib/repo.ts's sources`);
	return readFileSync(path.join(root, file), "utf8");
}

// The commit the build reads, which a page about unreleased code pins.
export const commit = execFileSync("git", ["rev-parse", "HEAD"], { cwd: root, encoding: "utf8" }).trim();
