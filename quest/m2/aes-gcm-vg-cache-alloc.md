# [S] Zen 5 AES-GCM falls back when its optional cache cannot allocate

## Goal

On Zen 5, the optional AES-GCM cache `rind/src/low/x86_64/aes_gcm_vg.rs` allocates for records of 6 KiB and more is allocated fallibly, and a failed allocation runs the existing BoringSSL kernel instead of aborting the process, including for a record whose tag turns out invalid.

## Plan

- Found by the full review of steelhead99x/rind#349, which brought this file in unchanged from kixel-ai/rind (kixel-ai/rind#1139). The owner decided (2026-11-28) to land the sync as is and plan this here.
- Replace the `Box::new` with a fallible allocation (`Box::try_new` where stable, else `alloc` with a null check) and take the BoringSSL path on failure, deciding it once per key rather than per record.
- A test with an allocator that refuses the cache's size checks the fallback seals and opens correctly.
- Report it upstream through [upstream-reports](/quest/m2/upstream-reports.md) once the fix exists.
