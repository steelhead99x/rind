# [M] Mont four row products

## Goal

Montgomery row products check their lengths for real, reduction rows are blocked consistently, and timing docs reflect current measurements.

## Plan

Difficulty: 6/10 (estimate).

Fork PR #76, head `b587afaa`. Score 7/10. Upstream twin #780. Builds on upstream #702.

Mediums:
- `mul_add` only `debug_assert`s the length; make it a real assert.
- Block the u·m reduction row too.
- Re-measure the RSA timing in `ALGORITHMS.md`.
- Add tests for 32-bit limbs and mixed carries.

Lows:
- Drop the p0–p3 helper unless it measures faster.
- The `mul_add2` doc is stale.
