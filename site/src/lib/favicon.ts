// The favicon: the wordmark's peel, the curled r, alone in a square, which
// reads on dark and light tabs alike. It is a data: URI because the page's
// Content-Security-Policy follows the icon's <link>, so a fetched icon would
// load before the policy covers it.
import { read } from "./repo";

const peel = read("admin/wordmark.svg").match(/^ {2}<g id="peel">\n[\s\S]*?\n {2}<\/g>$/m);
if (!peel) throw new Error('admin/wordmark.svg has no <g id="peel"> group for the favicon');

export const peelSvg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="80 100 1050 1050">${peel[0].replace(/\n\s*/g, "")}</svg>`;
export const favicon = `data:image/svg+xml,${encodeURIComponent(peelSvg)}`;
