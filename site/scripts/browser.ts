// Loads each built page in headless Chrome under its Content-Security-Policy
// and fails if the policy refuses anything, a request fails, or a copy button
// does not put its code block, on the landing page the prompt, on the clipboard.
import path from "node:path";
import { cpus, libraries } from "../src/lib/benchmarks";
import { prompt } from "../src/lib/landing";
import { pages } from "../src/lib/pages";

const dist = path.resolve("dist");
const server = Bun.serve({
	hostname: "127.0.0.1",
	port: 0,
	async fetch(req) {
		const { pathname } = new URL(req.url);
		const name = pathname === "/" ? "/index.html" : pathname;
		for (const file of [name, `${name}.html`]) {
			const body = Bun.file(path.join(dist, path.normalize(file)));
			if (await body.exists()) return new Response(body);
		}
		return new Response("not found", { status: 404 });
	},
});

// Spawn a fresh Chrome, never one already running with remote debugging, such
// as a signed-in browser. Its sandbox guards against hostile pages, but this
// page comes from the checkout whose code the build already ran, and Nix's
// Chromium cannot sandbox itself where Ubuntu's AppArmor denies it user
// namespaces.
const view = new Bun.WebView({ backend: { type: "chrome", url: false, argv: ["--no-sandbox"] } });
const errors: string[] = [];
// The page whose requests the network listeners are seeing.
let current = "about:blank";

// Click one copy button and check that it put `expected` on the clipboard.
async function copies(button: string, expected: string) {
	// The button appears once its island hydrates, which the policy must allow.
	await view.scrollTo(button, { timeout: 5000 });
	// Watch the label from before the click: the button resets it to "Copy" two
	// seconds after, so a check that starts late would miss the result.
	await view.evaluate(`void (window.__label = new Promise((resolve) => {
		const button = document.querySelector(${JSON.stringify(button)});
		const observer = new MutationObserver(() => {
			if (button.textContent !== "Copy") resolve(button.textContent);
		});
		observer.observe(button, { childList: true, characterData: true, subtree: true });
		setTimeout(() => resolve(button.textContent), 5000);
	}))`);
	// Empty the clipboard first, so what it holds after is this click's doing.
	await view.evaluate(`navigator.clipboard.writeText("")`);
	await view.click(button, { timeout: 5000 });
	const label = await view.evaluate("window.__label");
	if (label !== "Copied") throw new Error(`${button} says "${label}"`);
	const copied = await view.evaluate("navigator.clipboard.readText()");
	if (copied !== expected) throw new Error(`${button} copied ${JSON.stringify(copied)}, not ${JSON.stringify(expected)}`);
}

// Every copy button on the page, each of which must copy the code beside it,
// and on the landing page the prompt.
async function copiesAll(path: string) {
	// Buttons hydrate after the page loads, so count the blocks they sit beside.
	const blocks = (await view.evaluate(`[...document.querySelectorAll(".code pre, .prompt pre")].map((pre, i) => {
		pre.parentElement.dataset.copy = i;
		return pre.textContent;
	})`)) as string[];
	if (path === "/" && (blocks.length !== 1 || blocks[0] !== prompt)) {
		throw new Error(`the landing page's one code block is not the prompt: ${JSON.stringify(blocks)}`);
	}
	for (const [i, text] of blocks.entries()) await copies(`[data-copy="${i}"] button`, text);
}

// The benchmarks page shows the view its address links, and a pick rewrites
// the address: only the picked CPU's view, and only the picked libraries'
// columns, are displayed.
async function picks(base: string) {
	const [first, second] = cpus.filter((c) => c.kind === "host").map((c) => c.id);
	const shown = ["rind", "aws-lc-rs"];
	const more = [...shown, "ring"];
	for (const id of more) if (!libraries.some((l) => l.id === id)) throw new Error(`the benchmarks page has no library ${id}`);
	const displayed = `({
		views: [...document.querySelectorAll(".view")].filter((v) => getComputedStyle(v).display !== "none").map((v) => v.id),
		libs: [...new Set([...document.querySelectorAll(".view th[data-lib]")]
			.filter((th) => th.offsetParent !== null).map((th) => th.dataset.lib))],
		search: location.search,
	})`;
	const expect = async (want: { views: string[]; libs: string[]; search: string }) => {
		const got = await view.evaluate(displayed);
		if (JSON.stringify(got) !== JSON.stringify(want)) {
			throw new Error(`the benchmarks page shows ${JSON.stringify(got)}, not ${JSON.stringify(want)}`);
		}
	};
	// The island applies a linked view once it hydrates, when Astro drops its
	// `ssr` attribute; one that never does fails the check rather than stall it.
	const hydrated = `new Promise((resolve, reject) => {
		const observer = new MutationObserver(() => done());
		const timer = setTimeout(() => {
			observer.disconnect();
			reject(new Error("the picker never hydrated"));
		}, 5000);
		const done = () => {
			if (document.querySelector("astro-island[ssr]")) return;
			clearTimeout(timer);
			observer.disconnect();
			resolve(true);
		};
		observer.observe(document, { attributes: true, subtree: true });
		done();
	})`;
	await view.navigate(`${base}?cpu=${first}&libs=${shown.join(",")}`);
	await view.evaluate(hydrated);
	await expect({ views: [`view-${first}`], libs: shown, search: `?cpu=${first}&libs=${shown.join(",")}` });
	// Back within the page restores the controls with the address: an in-page
	// link pushes an entry, a pick rewrites that entry, and Back returns to the
	// earlier one.
	await view.evaluate(`location.hash = "times"`);
	await view.scrollTo(`#cpu-${second}`, { timeout: 5000 });
	await view.click(`#cpu-${second}`, { timeout: 5000 });
	await expect({ views: [`view-${second}`], libs: shown, search: `?cpu=${second}&libs=${shown.join(",")}` });
	await view.evaluate(`new Promise((resolve) => {
		addEventListener("popstate", () => setTimeout(resolve, 100), { once: true });
		history.back();
	})`);
	await expect({ views: [`view-${first}`], libs: shown, search: `?cpu=${first}&libs=${shown.join(",")}` });
	await view.scrollTo(`#cpu-${second}`, { timeout: 5000 });
	await view.click(`#cpu-${second}`, { timeout: 5000 });
	await expect({ views: [`view-${second}`], libs: shown, search: `?cpu=${second}&libs=${shown.join(",")}` });
	await view.scrollTo("#lib-ring", { timeout: 5000 });
	await view.click("#lib-ring", { timeout: 5000 });
	await expect({ views: [`view-${second}`], libs: more, search: `?cpu=${second}&libs=${more.join(",")}` });

	// A gap's place picks its CPU in place, keeping the libraries.
	const id = await view.evaluate(
		`[...document.querySelectorAll(".gaps label.place")].map((l) => l.htmlFor.slice(4)).find((c) => c !== ${JSON.stringify(second)})`,
	);
	const target = cpus.find((c) => c.id === id);
	if (!target || target.kind === "all") throw new Error(`the benchmarks page's gaps name no CPU but ${second}`);
	const timed = (target.kind === "host" ? target.host : target.tier).libraries.filter((l) => more.includes(l));
	const place = `.gaps label[for="cpu-${target.id}"]`;
	await view.scrollTo(place, { timeout: 5000 });
	await view.click(place, { timeout: 5000 });
	await expect({ views: [`view-${target.id}`], libs: timed, search: `?cpu=${target.id}&libs=${more.join(",")}` });
	// And from the keyboard: Enter on the place picks it again after another pick.
	await view.click(`#cpu-${second}`, { timeout: 5000 });
	await view.evaluate(`document.querySelector(${JSON.stringify(place)}).focus()`);
	await view.cdp("Input.dispatchKeyEvent", { type: "keyDown", key: "Enter", code: "Enter", windowsVirtualKeyCode: 13 });
	await view.cdp("Input.dispatchKeyEvent", { type: "keyUp", key: "Enter", code: "Enter", windowsVirtualKeyCode: 13 });
	await expect({ views: [`view-${target.id}`], libs: timed, search: `?cpu=${target.id}&libs=${more.join(",")}` });
	const name = await view.evaluate(`document.querySelector("#cpu-${target.id}").getAttribute("aria-label")`);
	if (typeof name !== "string" || name.length === 0) throw new Error(`#cpu-${target.id} has no accessible name of its own`);

	// With JavaScript off, the CSS alone shows what the inputs pick.
	// WebView's click waits on the page's scripts, so these click through
	// Chrome's input events instead.
	const press = async (selector: string) => {
		await view.scrollTo(selector, { timeout: 5000 });
		const [x, y] = (await view.evaluate(
			`(() => { const r = document.querySelector(${JSON.stringify(selector)}).getBoundingClientRect(); return [r.x + r.width / 2, r.y + r.height / 2]; })()`,
		)) as [number, number];
		for (const type of ["mousePressed", "mouseReleased"]) {
			await view.cdp("Input.dispatchMouseEvent", { type, x, y, button: "left", clickCount: 1 });
		}
	};
	await view.cdp("Emulation.setScriptExecutionDisabled", { value: true });
	try {
		await view.navigate(base);
		await press(place);
		await press("#lib-ring");
		const libs = (target.kind === "host" ? target.host : target.tier).libraries.filter((l) => l !== "ring");
		await expect({ views: [`view-${target.id}`], libs, search: "" });
	} finally {
		await view.cdp("Emulation.setScriptExecutionDisabled", { value: false });
	}

	// A list naming no library the page has, such as a renamed one, shows them all.
	await view.navigate(`${base}?cpu=${first}&libs=renamed`);
	await view.evaluate(hydrated);
	const host = cpus.find((c) => c.id === first);
	if (host?.kind !== "host") throw new Error(`${first} is not a host`);
	await expect({ views: [`view-${first}`], libs: host.host.libraries, search: `?cpu=${first}` });
}

try {
	await view.navigate("about:blank");
	// Recorded by a script the policy does not govern, before the page's own.
	await view.cdp("Page.enable");
	await view.cdp("Page.addScriptToEvaluateOnNewDocument", {
		source: `window.__violations = [];
			document.addEventListener("securitypolicyviolation", (e) =>
				window.__violations.push(e.effectiveDirective + " refused " + (e.blockedURI || "inline code")));`,
	});
	// Every request a page makes must succeed, so a missing image or chunk fails too.
	await view.cdp("Network.enable");
	view.addEventListener("Network.responseReceived", (e) => {
		const { response } = (e as MessageEvent).data;
		if (response.status >= 400) errors.push(`${current}: ${response.url} returned ${response.status}`);
	});
	const urls = new Map<string, string>();
	// The policy's hashes would also admit a third-party script carrying a matching
	// `integrity`, so every request, each redirect included, must stay on the site.
	view.addEventListener("Network.requestWillBeSent", (e) => {
		const { requestId, request } = (e as MessageEvent).data;
		urls.set(requestId, request.url);
		const url = new URL(request.url);
		if (url.protocol !== "data:" && url.origin !== server.url.origin) {
			errors.push(`${current}: ${request.url} loads from a third party`);
		}
	});
	view.addEventListener("Network.loadingFailed", (e) => {
		const { requestId, errorText, blockedReason, canceled } = (e as MessageEvent).data;
		// Chrome cancels a request it stops needing, such as the <img> fallback of
		// a <picture> whose <source> matched once styles were known; a missing
		// file still fails above, with its status.
		if (canceled && !blockedReason) return;
		errors.push(`${current}: ${urls.get(requestId)} failed: ${blockedReason ?? errorText}`);
	});
	await view.cdp("Browser.grantPermissions", {
		origin: server.url.origin,
		permissions: ["clipboardReadWrite", "clipboardSanitizedWrite"],
	});

	// Each page in both colour schemes, since a <picture> requests only the
	// variant whose media query matches.
	for (const scheme of ["light", "dark"]) {
		await view.cdp("Emulation.setEmulatedMedia", { features: [{ name: "prefers-color-scheme", value: scheme }] });
		for (const page of pages) {
			current = `${page.path} (${scheme})`;
			await view.navigate(new URL(page.path, server.url).href);
			try {
				// The buttons once, in the first scheme: they draw nothing a scheme changes.
				if (scheme === "light") await copiesAll(page.path);
				if (page.path === "/benchmarks") await picks(new URL(page.path, server.url).href);
			} catch (e) {
				errors.push(`${current}: ${e instanceof Error ? e.message : e}`);
			}
			for (const v of (await view.evaluate("window.__violations")) as string[]) {
				errors.push(`${current}: the Content-Security-Policy's ${v}`);
			}
		}
	}
} finally {
	view.close();
	server.stop();
}

if (errors.length > 0) {
	for (const e of errors) console.error(`error: ${e}`);
	process.exit(1);
}
console.log(
	`site: ${pages.length} page(s) load in both colour schemes under their policy, each copy button copies its block, and the benchmarks page shows what its address and picks name`,
);
