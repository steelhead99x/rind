# [S] Verify rind-rustls QUIC multipath packet keys

## Goal

noq seals and opens a QUIC packet with rind-rustls's `encrypt_in_place_for_path` and `decrypt_in_place_for_path`, and Kyle has said whether to send that fix to kixel-ai/rind.

## Plan

rustls 0.23.46's `PacketKey` defaults return `EncryptError` and `DecryptError`. noq calls the multipath methods on every packet, so the first packet panics. The nonce is the IV XOR the 32-bit path id and the 64-bit packet number, both big-endian, which is `Nonce::for_path` (draft-ietf-quic-multipath-11). rustls's ring provider, which its aws-lc-rs provider reuses, already does this. Path id 0 is the single-path nonce.

The fork PR that adds this quest implements both methods on rind-rustls and checks them three ways: rind's own keys reject a wrong path id, packet number, header, or short tag, and an empty plaintext round-trips; path id 0 matches `encrypt_in_place`; a QUIC handshake seals and opens path ids 0, 1, and 7 against rustls's aws-lc-rs and ring providers.

Done on the PR:

- `cargo test -p rind-rustls --locked --all-targets` passes with fork main merged in (a28f9913, plus the `Vec` import main's `no_std` needs).
- moq-noq 2.0.5, built on rind-rustls alone (no ring or aws-lc-rs, rind's HMAC as the reset key and AES-256-GCM as the token key), completes a handshake and echoes a bidirectional stream with the fix. Against fork main without it, the first packet panics in moq-noq-proto's `crypto/rustls.rs` with `EncryptError`.

Still to do:

- Re-run the noq smoke test above on the head that lands, if anything in rind-rustls changes first.
- Do not open a pull request on kixel-ai/rind until the Waiting item is decided.

## Waiting

- Maintainer: say whether to open the upstream pull request on kixel-ai/rind. Options: send it once the noq packet path passes (recommended: a published rind-rustls that keeps rustls's default breaks every stack that calls these methods, including moq's noq), or keep the fix on this fork. An agent cannot send it. Kyle has to approve first. Check: a comment on [steelhead99x/rind#312](https://github.com/steelhead99x/rind/pull/312) that says to send it or not.

## Related

- [steelhead99x/rind#312](https://github.com/steelhead99x/rind/pull/312) - the multipath methods and this quest
