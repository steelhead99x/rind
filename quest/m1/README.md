# m1: MoQ coverage

## Goal

rind carries everything [MoQ](https://github.com/moq-dev/moq) needs to take
all its cryptography from rind, on every target MoQ releases, and MoQ switched
in [moq-dev/moq#8250](https://github.com/moq-dev/moq/pull/8250).
Its last open question, which AES-GCM tier Zen 2 runs, waits on an outside
measurement in [m3](/quest/m3/quic-path.md) (maintainer, 2026-11-09: ✅ m3;
rejected: keep it here, where it held m1 open).
The Bun half was dropped on 2026-11-11 (maintainer, /quest-unblock): rind
files no upstream PRs to get itself adopted.
m1 also holds the agent hosts' smaller costs that slow every proof task
(maintainer, 2026-11-12).
