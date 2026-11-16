# HPKE edge vectors

Difficulty: 6/10 (estimate)


## Goal

HPKE DeriveKeyPair rejection and range handling are tested against the real code, with vectors tied to a known source revision.

## Plan

Upstream draft #798, fork branch `fork/798-gaps` at `df02622c`. Score 8/10. No fork PR yet; push the branch and open one first.

- Add ctgrind on DeriveKeyPair's candidate-rejection path with a secret `ikm`.
- Test the range check at 0, n−1 and n.
- Check `kdf_id` and `aead_id` against real suite values.
- The rejection test copies the candidate loop; make it run the real one.
- Record hpkewg revision `e298f94` and tie the copied vectors to that source.
