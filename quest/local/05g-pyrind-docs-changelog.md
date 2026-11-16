# [XS] Update pyrind docs and the CHANGELOG rename table

## Goal

On the branch of https://github.com/kixel-ai/rind/pull/799, `rind-python/README.md` and `rind-python/CHANGELOG.md` describe the new module shape, and the CHANGELOG has a table from each old name to its new one, as MIGRATING.md has for rind. No 0.2.0 release is published.

## Plan

Continue on the #799 branch. Touch `rind-python/README.md` and `rind-python/CHANGELOG.md` only. Do not bump a published version or cut a release.

Success check: `git grep -n pyrind.ecdsa HEAD -- rind-python/README.md rind-python/CHANGELOG.md` prints a match in both files, and `git tag --list 'rind-python-v0.2.0'` prints nothing.

## Required

- [Point pyrind-cryptography internals at the new pyrind API](/quest/local/05f-pyrind-cryptography.md) - the API the docs describe is finished
