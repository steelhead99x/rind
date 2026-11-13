# Vector files

Copies of the vector files in [aws-lc] and [BoringSSL] that cover an
algorithm rind offers. `admin/sync-vectors` fetches them, unmodified, from the
revisions it pins, and lists every file. Both repositories are hundreds of
megabytes, so rind keeps these copies rather than submodules.

The aws-lc and BoringSSL directories each hold their upstream's `LICENSE`.
To update, bump a revision in `admin/sync-vectors` and rerun it.

The tests read them through `rind/src/test/file_test.rs`, which parses the
FileTest format both projects share.

`rfc9180/test-vectors.json` holds [RFC 9180]'s HPKE vectors, from the
CFRG draft's repository at the revision `admin/sync-vectors` pins: the base
mode's, one per line, for the KEMs rind offers. The revision in
[hpkewg/hpke] repeats them unchanged. They are IETF contributions, under
[BCP 78].

`rfc9380/` holds [RFC 9380]'s hash-to-curve vectors, its Appendix J and K,
from the CFRG draft's `poc/vectors` at the revision `admin/sync-vectors`
pins: the `expand_message_xmd` files and the P-256, P-384, and P-521
`_RO_` suites, named without the colons Windows cannot check out. They are
IETF contributions too.

`rfc9474/test-vectors.json` holds [RFC 9474]'s four RSABSSA vectors, from
[blind-rsa-signatures] at the revision `admin/sync-vectors` pins, as the
CFRG draft's repository holds stale ones. They are IETF contributions, under
[BCP 78].

`rfc9591/` holds [RFC 9591]'s appendix E vectors, the CFRG draft's `poc` JSON
for FROST(Ed25519, SHA-512), FROST(ristretto255, SHA-512), and FROST(P-256,
SHA-256), at the revision `admin/sync-vectors` pins. They are IETF
contributions too.

`rfc9497/allVectors.json` holds [RFC 9497]'s OPRF vectors, its Appendix A,
from the CFRG draft's `poc/vectors` at the revision `admin/sync-vectors`
pins: the OPRF and VOPRF modes of the ristretto255, P-256, P-384, and P-521
suites, without decaf448 and the POPRF mode, which rind does not offer.
They are IETF contributions, under [BCP 78].

[aws-lc]: https://github.com/aws/aws-lc
[BoringSSL]: https://boringssl.googlesource.com/boringssl
[RFC 9180]: https://www.rfc-editor.org/rfc/rfc9180.html
[RFC 9380]: https://www.rfc-editor.org/rfc/rfc9380.html
[hpkewg/hpke]: https://github.com/hpkewg/hpke
[RFC 9474]: https://www.rfc-editor.org/rfc/rfc9474.html
[RFC 9591]: https://www.rfc-editor.org/rfc/rfc9591.html
[RFC 9497]: https://www.rfc-editor.org/rfc/rfc9497.html
[blind-rsa-signatures]: https://github.com/jedisct1/rust-blind-rsa-signatures
[BCP 78]: https://www.rfc-editor.org/info/bcp78
