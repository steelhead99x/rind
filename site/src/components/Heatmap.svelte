<script lang="ts">
	// Every operation for every library, a square per host colored by its time
	// over the fastest library's there, as BENCHMARKS.md's overview draws it.
	// Ported from the rind launch post's chart (moq-dev/moq.dev,
	// src/components/rind/timings.tsx, MIT or Apache-2.0) to a table, so a
	// library a visitor hides takes its column with it. It renders on the
	// server only; each square's title holds its time.
	import { type Host, libraryName, ratio, report } from "../lib/benchmarks";

	interface Props {
		libraries: string[];
		hosts: Host[];
	}
	const { libraries, hosts }: Props = $props();

	const cell = (host: Host, row: string, lib: string) => {
		const i = host.libraries.indexOf(lib);
		return i < 0 ? null : (host.times[row]?.[i] ?? null);
	};
	// A square's speed bin, ringed when its code is verified.
	const square = (host: Host, row: string, lib: string) => {
		const c = cell(host, row, lib);
		if (c === null) return "none";
		return host.proofs[row]?.[lib] !== undefined ? `b${c[1]} v` : `b${c[1]}`;
	};
	const title = (host: Host, row: string, lib: string) => {
		const c = cell(host, row, lib);
		if (c === null) return `${host.name}: not timed`;
		const proof = host.proofs[row]?.[lib] !== undefined ? ", verified" : "";
		const over = host.fastest[row] && host.fastest[row] !== lib ? `, ${ratio(c[2])} the fastest` : "";
		return `${host.name}: ${c[0]}${over}${proof}`;
	};
</script>

<div class="heat-scroll">
	<table class="heat">
		<thead>
			<tr>
				<th></th>
				{#each libraries as lib (lib)}
					<th data-lib={lib} class={lib === "rind" ? "me" : undefined}>{libraryName(lib)}</th>
				{/each}
			</tr>
		</thead>
		{#each report.sections as section (section.name)}
			<tbody>
				<tr><th colspan={libraries.length + 1} class="section">{section.name}</th></tr>
				{#each section.operations.filter((o) => hosts.some((h) => o.id in h.times)) as op (op.id)}
					<tr>
						<th scope="row">{op.label}</th>
						{#each libraries as lib (lib)}
							<td data-lib={lib} class={lib === "rind" ? "me" : undefined}>
								{#each hosts as host (host.name)}
									<i class={square(host, op.id, lib)} title={title(host, op.id, lib)}></i>
								{/each}
							</td>
						{/each}
					</tr>
				{/each}
			</tbody>
		{/each}
	</table>
</div>
<p class="heat-fine">Squares, left to right: {hosts.map((h) => h.name).join(", ")}. A ringed square is verified code; a blank one, not timed.</p>

<style>
	/* Global, under .heat, since a scoped style marks each of the thousands of squares. */
	:global {
		.heat-scroll {
			overflow-x: auto;
		}
		.heat {
			border-collapse: collapse;
			font-size: 0.85rem;
		}
		.heat th {
			font-weight: normal;
			text-align: left;
			white-space: nowrap;
			padding: 0 0.75rem 0 0;
		}
		.heat thead th {
			font-weight: 600;
			writing-mode: vertical-rl;
			transform: rotate(180deg);
			padding: 0.25rem 0;
			vertical-align: bottom;
		}
		.heat .section {
			font-weight: 600;
			padding-top: 0.75rem;
		}
		.heat td {
			padding: 1px 0.5rem 1px 0;
			white-space: nowrap;
			line-height: 0;
		}
		.heat .me {
			background: var(--surface);
		}
		.heat i {
			display: inline-block;
			width: 0.8rem;
			height: 0.8rem;
			margin-right: 1px;
			border-radius: 2px;
			box-sizing: border-box;
		}
		.heat i.none {
			border: 1px solid var(--border);
		}
		.heat i.v {
			outline: 2px solid var(--fg);
			outline-offset: -2px;
		}
		.heat-fine {
			color: var(--muted);
			font-size: 0.85rem;
		}
	}
</style>
