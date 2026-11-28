# [M] HKDF's conversion to AEAD keys is proven on aarch64

## Goal

On aarch64, `From<Okm<&'static aead::Algorithm>> for aead::Key`, the step QUIC's and TLS 1.3's key schedules take from HKDF-Expand to an AEAD key, is proven to hold AES-GCM and ChaCha20-Poly1305 for the HKDF bytes, as `proofs/Rind/X86_64/HkdfAead.lean` proves it on x86_64, so the HKDF-to-AEAD path earns on aarch64 the coverage it has on x86_64.

## Plan

- Already proven on aarch64: HKDF and its conversions to `hmac::Key`, `Prk`, and header-protection keys (the copies of `Hkdf.lean` and `HkdfAes.lean` `admin/prove` makes), AES-GCM's `aead::Key::new` and AEAD API (`Rind/Aarch64/AesGcmAead.lean`), and ChaCha20-Poly1305's (`ChaCha20Poly1305Api`, which aarch64 shares).
- Left: aarch64's KDF translation does not reach the AEAD key's conversion: `admin/prove` deletes the `-- BEGIN aead` block from the aarch64 copy of `Kdf/FunsExternal.lean`, and writes no aarch64 copy of `HkdfAead.lean`. Extend aarch64's `extract_kdf` to reach it, then copy `HkdfAead.lean` as `admin/prove` copies `GcmKey.lean`, passing `RunsAesGcm` the key's algorithm, since aarch64's takes it (AES-192 on cores with SHA3 runs aws-lc's unproven eight-way kernels).
- Update `proofs/README.md`'s HKDF section, which says `HkdfAead.lean` is x86_64's alone, and pin the new theorems' axioms in `Rind/Aarch64/Axioms.lean`.

## Related

- [aarch64's eight-way AES-192-GCM kernels are proven](/quest/m4/verified/aes-gcm-aarch64-192.md) - lifts the AES-192 exception this conversion inherits on cores with SHA3
