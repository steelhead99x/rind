# pyrind 0.4 shape fixes

Difficulty: 6/10 (estimate)


## Goal

pyrind's enum hashing is consistent, RSA public-key paths are tested, and the shim's error handling and duplication are cleaned up.

## Plan

Upstream draft #799, fork branch `fork/799-gaps` at `b27ca30e`. Score 8/10. Push the branch and open a fork PR first.

Mediums:
- `eq_int` enums hash differently from the ints they equal. Fix the hash or drop the equality.
- The RSA public-key paths have no edge tests.

Lows:
- A below-floor RSA key raises `InvalidSignature` in the shim. Make it a key error and test it.
- The RSA private key builds its public key eagerly.
- `kem` and `agreement` do not cache the public key.
- The key-wrapping code is duplicated.
- The shim builds an SPKI by hand.
- A doc still names the removed `pyrind.signature.verify`.
