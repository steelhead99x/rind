// What crates.io has published, read when the site builds, so a page names
// only a version the registry lists and quotes the README that version shipped.
import { createHash } from "node:crypto";
import { gunzipSync } from "node:zlib";

export interface Release {
	version: string;
	// The README.md inside the published crate.
	readme: string;
}

// The crate's file in the sparse index, laid out as Cargo's registry docs say
// (https://doc.rust-lang.org/cargo/reference/registry-index.html#index-files).
function indexPath(name: string): string {
	const n = name.toLowerCase();
	if (n.length <= 2) return `${n.length}/${n}`;
	if (n.length === 3) return `3/${n[0]}/${n}`;
	return `${n.slice(0, 2)}/${n.slice(2, 4)}/${n}`;
}

// A GET that gives up on a stalled connection, and tries three times where the
// registry or the network fails for a moment (a 429, a 5xx, no answer, or a
// body cut short), so one blip does not fail a deploy of a site that did not
// change. Any other status, a 404 apart, fails at once. A 404 has no body.
async function get(url: string): Promise<{ status: number; body: Uint8Array }> {
	let failure = "";
	for (let attempt = 1; attempt <= 3; attempt++) {
		try {
			const res = await fetch(url, { signal: AbortSignal.timeout(30_000) });
			if (res.status === 404) return { status: 404, body: new Uint8Array() };
			if (res.ok) return { status: res.status, body: new Uint8Array(await res.arrayBuffer()) };
			failure = `answered ${res.status}`;
			if (res.status < 500 && res.status !== 429) break;
		} catch (e) {
			failure = `failed: ${e instanceof Error ? e.message : e}`;
		}
		// A rate limit or a short outage outlasts an immediate retry.
		if (attempt < 3) await Bun.sleep(1000 * attempt);
	}
	throw new Error(`${url} ${failure}`);
}

const cache = new Map<string, Promise<Release | null>>();

// The newest version of `name` that is neither yanked nor a pre-release, with
// its README, or null when crates.io has none.
export function newest(name: string): Promise<Release | null> {
	let found = cache.get(name);
	if (!found) {
		found = fetchNewest(name);
		cache.set(name, found);
	}
	return found;
}

async function fetchNewest(name: string): Promise<Release | null> {
	const index = await get(`https://index.crates.io/${indexPath(name)}`);
	if (index.status === 404) return null;
	const entries: { vers: string; cksum: string; yanked: boolean }[] = new TextDecoder()
		.decode(index.body)
		.trim()
		.split("\n")
		.map((line) => JSON.parse(line));
	const live = entries.filter((e) => !e.yanked && !e.vers.includes("-"));
	if (live.length === 0) return null;
	const top = live.reduce((a, b) => (Bun.semver.order(a.vers, b.vers) >= 0 ? a : b));

	const url = `https://static.crates.io/crates/${name}/${name}-${top.vers}.crate`;
	const res = await get(url);
	if (res.status === 404) throw new Error(`${url} is missing, though the index lists ${name} ${top.vers}`);
	const crate = res.body;
	const sum = createHash("sha256").update(crate).digest("hex");
	if (sum !== top.cksum) throw new Error(`${url} hashes to ${sum}, not the index's ${top.cksum}`);
	const readme = untar(gunzipSync(crate), `${name}-${top.vers}/README.md`);
	// A release with no README is the stranger's or the maintainer's to fix, not a
	// reason to stop the site: an empty one has no structure, so the page falls back to `main`.
	return { version: top.vers, readme: readme ?? "" };
}

// One file from a tar archive, as `cargo package` writes them, with GNU or
// POSIX headers. A GNU long name, which a README's short path never needs, is
// an entry of its own and skipped over.
export function untar(tar: Uint8Array, want: string): string | undefined {
	const field = (block: Uint8Array, start: number, len: number) => {
		const bytes = block.subarray(start, start + len);
		const end = bytes.indexOf(0);
		return new TextDecoder().decode(end < 0 ? bytes : bytes.subarray(0, end));
	};
	for (let at = 0; at + 512 <= tar.length; ) {
		const header = tar.subarray(at, at + 512);
		if (header.every((b) => b === 0)) return undefined;
		const sizeField = field(header, 124, 12).trim() || "0";
		// A size is octal digits; a GNU archive writes a huge one in base 256, which a README never needs.
		if (!/^[0-7]+$/.test(sizeField)) {
			throw new Error(`the crate archive is corrupt: ${JSON.stringify(sizeField)} is not an entry's octal size`);
		}
		const size = Number.parseInt(sizeField, 8);
		// Only POSIX ustar keeps a path prefix there; GNU keeps times.
		const prefix = field(header, 257, 6) === "ustar" ? field(header, 345, 155) : "";
		const name = prefix ? `${prefix}/${field(header, 0, 100)}` : field(header, 0, 100);
		const body = at + 512;
		if (name === want && (header[156] === 0x30 || header[156] === 0)) {
			return new TextDecoder().decode(tar.subarray(body, body + size));
		}
		at = body + Math.ceil(size / 512) * 512;
	}
	return undefined;
}
