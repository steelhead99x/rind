// The libraries rind stands in for, each with its page at /from/<slug> and the
// rind crate whose README the page renders.
export interface Route {
	slug: string;
	// The library a reader moves from, as they would search for it.
	upstream: string;
	// The page's heading.
	title: string;
	// The rind crate that stands in for it, in the repository directory of the same name.
	crate: string;
}

export const routes: Route[] = [
	{ slug: "ring", upstream: "ring", title: "Move from ring to rind", crate: "rind-ring" },
	{ slug: "aws-lc-rs", upstream: "aws-lc-rs", title: "Move from aws-lc-rs to rind", crate: "rind-aws-lc-rs" },
	{ slug: "rustls", upstream: "rustls", title: "Run rustls on rind", crate: "rind-rustls" },
	{ slug: "rcgen", upstream: "rcgen", title: "Run rcgen on rind", crate: "rind-rcgen" },
	{ slug: "jsonwebtoken", upstream: "jsonwebtoken", title: "Run jsonwebtoken on rind", crate: "rind-jsonwebtoken" },
	{ slug: "dimpl", upstream: "dimpl", title: "Run dimpl on rind", crate: "rind-dimpl" },
	{ slug: "str0m", upstream: "str0m", title: "Run str0m on rind", crate: "rind-str0m" },
	{ slug: "object_store", upstream: "object_store", title: "Run object_store on rind", crate: "rind-object-store" },
	{ slug: "openmls", upstream: "openmls", title: "Run openmls on rind", crate: "rind-openmls" },
];

// The landing page's way to a reader's own library: a link to each page, and to
// the list of crates that pick a backend for you.
export const picker = {
	title: "Switch from the library you use",
	links: [
		...routes.map((r) => ({ label: r.upstream, href: `/from/${r.slug}` })),
		{ label: "another crate", href: "/from" },
	],
};
