import { expect, test } from "bun:test";
import { escapeCell } from "./benchmarks";

// A pipe already escaped stays as it is; a bare one, or one after an escaped
// backslash, is escaped.
test("escapeCell escapes only bare pipes", () => {
	expect(escapeCell("a | b")).toBe("a \\| b");
	expect(escapeCell("a \\| b")).toBe("a \\| b");
	expect(escapeCell("a \\\\| b")).toBe("a \\\\\\| b");
});
