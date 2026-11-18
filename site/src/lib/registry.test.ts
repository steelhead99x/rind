import { expect, test } from "bun:test";
import { untar } from "./registry";

// One ustar entry: a 512-byte header, then the body padded to 512.
function entry(name: string, body: string, size = body.length.toString(8).padStart(11, "0")): Uint8Array {
	const header = new Uint8Array(512);
	const put = (text: string, at: number) => header.set(new TextEncoder().encode(text), at);
	put(name, 0);
	put(`${size}\0`, 124);
	header[156] = 0x30;
	const data = new Uint8Array(Math.ceil(body.length / 512) * 512);
	data.set(new TextEncoder().encode(body));
	return Uint8Array.from([...header, ...data]);
}
const archive = (...entries: Uint8Array[]) => Uint8Array.from([...entries.flatMap((e) => [...e]), ...new Uint8Array(1024)]);

test("untar reads the wanted file after others", () => {
	const tar = archive(entry("x/Cargo.toml", "a".repeat(600)), entry("x/README.md", "# Hi\n"));
	expect(untar(tar, "x/README.md")).toBe("# Hi\n");
});

test("untar says a missing file is missing", () => {
	expect(untar(archive(entry("x/Cargo.toml", "a")), "x/README.md")).toBeUndefined();
});

test("untar calls a size that is not octal a corrupt archive", () => {
	expect(() => untar(archive(entry("x/Cargo.toml", "a", "zzzz"), entry("x/README.md", "b")), "x/README.md")).toThrow(
		"the crate archive is corrupt",
	);
});
