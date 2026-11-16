// Loads each built page in headless Chrome under its Content-Security-Policy
// and fails if the policy refuses anything, a request fails, or the landing
// page's copy button does not put the prompt on the clipboard.
import path from "node:path";
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

// Click the copy button and read back what it put on the clipboard.
async function copies() {
	// The button appears once its island hydrates, which the policy must allow.
	await view.scrollTo("button", { timeout: 5000 });
	// Watch the label from before the click: the button resets it to "Copy" two
	// seconds after, so a check that starts late would miss the result.
	await view.evaluate(`void (window.__label = new Promise((resolve) => {
		const button = document.querySelector("button");
		const observer = new MutationObserver(() => {
			if (button.textContent !== "Copy") resolve(button.textContent);
		});
		observer.observe(button, { childList: true, characterData: true, subtree: true });
		setTimeout(() => resolve(button.textContent), 5000);
	}))`);
	// Empty the clipboard first, so what it holds after is this click's doing.
	await view.evaluate(`navigator.clipboard.writeText("")`);
	await view.click("button", { timeout: 5000 });
	const label = await view.evaluate("window.__label");
	if (label !== "Copied") throw new Error(`the copy button says "${label}"`);
	const copied = await view.evaluate("navigator.clipboard.readText()");
	if (copied !== prompt) throw new Error(`the copy button copied ${JSON.stringify(copied)}`);
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
			if (page.path === "/") {
				try {
					await copies();
				} catch (e) {
					errors.push(`${current}: ${e instanceof Error ? e.message : e}`);
				}
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
console.log(`site: ${pages.length} page(s) load in both colour schemes under their policy, and the copy button copies the prompt`);
