# [XS] rind-rustls offers SecP384r1MLKEM1024

## Goal

rind-rustls offers RFC 10024's `SecP384r1MLKEM1024` key exchange group (`0x11ED`), for TLS 1.3, beside its X25519MLKEM768 and SecP256r1MLKEM768, once rustls's aws-lc-rs provider offers it.

## Plan

From [the scope](/quest/m4/pq/README.md), 2026-11-06.

- It's an RFC 10024 hybrid like the two rind-rustls already composes in `kx_group/hybrid.rs`: ECDH share first, then ML-KEM-1024, and an 80-byte secret.
- Waits for rustls ✅ (rejected: offering it now by its raw codepoint, `NamedGroup::Unknown(0x11ED)`, as rind-rustls's own addition, which the maintainer chose on 2026-11-07). The adapter rule the maintainer set a day later wins: `AGENTS.md` has an adapter offer exactly the API of the provider its upstream ships, adding nothing, and the maintainer decided that with no exceptions on 2026-11-08, removing `kx_group::SECP521R1` from rind-rustls for the same reason. rustls 0.23.46's provider has `MLKEM768`, `MLKEM1024`, `SECP256R1MLKEM768`, and `X25519MLKEM768` (`src/crypto/aws_lc_rs/mod.rs:247`) and its `NamedGroup` has no variant for this group.
- Mirror upstream when it lands: the same static name in `kx_group`, in or out of the default groups as upstream has it (RFC 10024 marks the group not recommended), and no exclusion in `aws_lc_rs_parity`.
- Test it in `tests/pair.rs` against itself and against rustls's own provider.

## Waiting

- rustls/rustls: a release whose aws-lc-rs provider offers the group. Check that `SECP384R1MLKEM1024` appears in [`rustls::crypto::aws_lc_rs::kx_group`](https://docs.rs/rustls/latest/rustls/crypto/aws_lc_rs/kx_group/index.html), in the rustls version rind-rustls adapts.

