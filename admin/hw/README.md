# Hardware runs

Measurements that need a CPU or device the shared hosts and CI lack, one
script each, for the owner to run when the machine is free. Each script's
header names the host it needs, how long it takes, and what it writes, and
refuses any other host; `--preflight` runs only those checks.

| Script | For | Host |
|---|---|---|
| `admin/hw/avx-ifma.sh` | [steelhead99x/rind#178](https://github.com/steelhead99x/rind/pull/178), X25519 and Ed25519 verify | idle Linux, AVX-IFMA without AVX-512 (Arrow Lake P-core) |
| `admin/hw/avx-ifma-windows.sh` | #178, the Windows run | Windows (Git Bash), AVX-IFMA without AVX-512 |
| `admin/hw/ristretto255-avx2.sh` | [steelhead99x/rind#256](https://github.com/steelhead99x/rind/pull/256), the `oprf` bench | idle Linux, AVX2 without ADX (Haswell) |
| `admin/hw/ipad-dit-matrix.sh` | [steelhead99x/rind#277](https://github.com/steelhead99x/rind/pull/277), the A/B/C/D matrix | a Mac with Xcode, and the iPads |
| `admin/hw/mldsa-sign-vg.sh` | [steelhead99x/rind#315](https://github.com/steelhead99x/rind/pull/315), ML-DSA without AVX2 against verified-garbage | idle dedicated Linux x86_64 with AVX2 |

The x86_64 scripts follow the A/B rules: each revision is built in its own
checkout and target dir, binaries of different commits must not hash equal,
every variant runs pinned to one CPU (`RIND_PINNED_CPUS`, as in
`admin/bench-report`) once per round in an order rotated each round, and a
round counts only when the host stayed idle by `admin/bench-report`'s limit
and the control (aws-lc-rs in the same process, or a second run of the base
binary) moved at most 1.02. They run until 5 rounds count for every row, or
stop after 12 and say the result is incomplete. `admin/hw/ab` runs the rounds
and writes `ab.md`, the comment for the PR, beside the raw criterion
estimates. Results go under `.tmp/hw/`, and the last lines printed are the
next step.
