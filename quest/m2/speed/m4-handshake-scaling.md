# [S] rind-rustls's handshakes scale across the Apple M4's cores as well as aws-lc-rs's

## Goal

On `kixtop` (Apple M4, 4 performance and 6 efficiency cores), rind-rustls's full and resumed X25519 handshakes on every logical CPU reach at least the multiple of their one-thread rate that aws-lc-rs's provider reaches, or the PR records why rind's cannot.

## Plan

Found by the 0.4 report refresh ([kixel-ai/rind#991](https://github.com/kixel-ai/rind/pull/991)), the first run to time `kixtop`'s every-logical-CPU rows, whose Plan reads them against each host's last run and against aws-lc-rs.

- At `3f76a53f`, rind-rustls ran 5.01 times its one-thread rate for full handshakes and 4.61 for resumed ones, against aws-lc-rs's 5.32 and 5.00 and ring's 5.16 and 4.81. rind still led on every CPU (26.5 µs a full handshake against aws-lc-rs's 34.8, 12.6 against 18.5 resumed), so this is about what the efficiency cores gain, not a loss. The x86_64 hosts show no such trail: `nixos` and `fedora` scaled better than aws-lc-rs in their last runs, and the 4-vCPU VPSes level within their run-to-run noise.
- Likely causes to test: rind's code running relatively slower on the efficiency cores than aws-lc's (time a one-thread handshake on each core class; macOS offers no core pinning, so steer the run with its QoS, `taskpolicy -b` for the efficiency cores and the default for the performance cores, and keep only runs that `sudo powermetrics --samplers cpu_power` shows on that cluster alone), DIT's cost differing between core classes, or shared state between threads in rind-rustls or rind (a lock, an atomic, a shared cache line) that the other providers lack.
- Fix what is rind's; if the gap is the cores' alone, record the per-core-class numbers in the PR and delete this quest.

## Hosts

- macos - the Apple M4 (`kixtop`) is the host that shows it
