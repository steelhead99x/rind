# Vector files

Copies of the vector files rind's tests read from [aws-lc], [BoringSSL],
[Wycheproof], NIST's [CAVP] through the [ctz/cavp] mirror, and [CCTV].
`admin/sync-vectors` fetches them, unmodified, from the revisions it pins,
and lists every file. The tests read a small part of each repository, so
rind keeps these copies rather than submodules, and a plain clone runs every
test. Each test opens its files by name and fails on a missing one.

Each upstream's directory keeps its upstream's paths, a `REVISION` file
naming the commit it was copied from, and its license: aws-lc's, BoringSSL's,
and Wycheproof's `LICENSE` (Apache 2.0 for Wycheproof); CAVP's `README.md`,
which names NIST's sources, whose sample files are U.S. government works;
CCTV's `ed25519/LICENSE` for its Ed25519 vectors, and `ML-KEM/README.md`,
which puts its ML-KEM vectors under CC0 1.0.
To update, bump a revision in `admin/sync-vectors` and rerun it.

The tests read the aws-lc and BoringSSL files through
`rind/src/test/file_test.rs`, which parses the FileTest format both projects
share.

`rfc9180/test-vectors.json` holds [RFC 9180]'s HPKE vectors, from the
CFRG draft's repository at the revision `admin/sync-vectors` pins: the base
mode's, one per line, for the KEMs rind offers. The revision in
[hpkewg/hpke] repeats them unchanged, and adds an appendix of edge-case
vectors (rejection sampling in `DeriveKeyPair`, and empty and zero-byte
inputs) in Markdown only, so `admin/sync-vectors` cannot fetch them: they are
copied by hand into `rind/src/high/hpke.rs`'s tests from its `e298f94`, and a
later revision of that appendix means checking those copies again. They are
IETF contributions, under [BCP 78].

`xwing/spec/test-vectors.json` holds the three vectors of
[draft-connolly-cfrg-xwing-kem]'s Appendix C, from the draft's repository at
the revision `admin/sync-vectors` pins. `hpke-pq/test-vectors.json` holds
[draft-ietf-hpke-pq]'s base-mode vectors for MLKEM768-X25519 (KEM 0x647A),
one per line, from its repository at the revision `admin/sync-vectors` pins.
They are IETF contributions, under [BCP 78].

`rfc9380/` holds [RFC 9380]'s hash-to-curve vectors, its Appendix J and K,
from the CFRG draft's `poc/vectors` at the revision `admin/sync-vectors`
pins: the `expand_message_xmd` files and the P-256, P-384, and P-521
`_RO_` suites, named without the colons Windows cannot check out. They are
IETF contributions too.

`rfc9909/` holds [RFC 9909]'s appendix C examples, an SLH-DSA-SHA2-128s
public key, private key, and self-signed certificate, decoded from the RFC's
PEM to DER by hand, since no repository publishes them. They too are IETF
contributions, under [BCP 78].

`rfc9474/test-vectors.json` holds [RFC 9474]'s four RSABSSA vectors, from
[blind-rsa-signatures] at the revision `admin/sync-vectors` pins, as the
CFRG draft's repository holds stale ones. They are IETF contributions, under
[BCP 78].

`rfc9497/allVectors.json` holds [RFC 9497]'s OPRF vectors, its Appendix A,
from the CFRG draft's `poc/vectors` at the revision `admin/sync-vectors`
pins: the OPRF and VOPRF modes of the ristretto255, P-256, P-384, and P-521
suites, without decaf448 and the POPRF mode, which rind does not offer.
They are IETF contributions, under [BCP 78].

`rfc9591/` holds [RFC 9591]'s FROST vectors, its Appendix E, from the CFRG
draft's `poc` at the revision `admin/sync-vectors` pins: the Ed25519,
ristretto255, and P-256 suites, without Ed448 and secp256k1, which rind does
not offer. They are IETF contributions, under [BCP 78].

[aws-lc]: https://github.com/aws/aws-lc
[Wycheproof]: https://github.com/C2SP/wycheproof
[CAVP]: https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program
[ctz/cavp]: https://github.com/ctz/cavp
[CCTV]: https://github.com/C2SP/CCTV
[BoringSSL]: https://boringssl.googlesource.com/boringssl
[RFC 9180]: https://www.rfc-editor.org/rfc/rfc9180.html
[RFC 9380]: https://www.rfc-editor.org/rfc/rfc9380.html
[RFC 9909]: https://www.rfc-editor.org/rfc/rfc9909.html
[hpkewg/hpke]: https://github.com/hpkewg/hpke
[RFC 9474]: https://www.rfc-editor.org/rfc/rfc9474.html
[RFC 9497]: https://www.rfc-editor.org/rfc/rfc9497.html
[RFC 9591]: https://www.rfc-editor.org/rfc/rfc9591.html
[blind-rsa-signatures]: https://github.com/jedisct1/rust-blind-rsa-signatures
[draft-connolly-cfrg-xwing-kem]: https://datatracker.ietf.org/doc/draft-connolly-cfrg-xwing-kem/
[draft-ietf-hpke-pq]: https://datatracker.ietf.org/doc/draft-ietf-hpke-pq/
[BCP 78]: https://www.rfc-editor.org/info/bcp78
