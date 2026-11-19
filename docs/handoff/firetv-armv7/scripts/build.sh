#!/usr/bin/env bash
# Cross-builds rind-bench's binaries and rind-cpuid for armv7-linux-androideabi into ./pkg.
# Usage (from the repo root): docs/handoff/firetv-armv7/scripts/build.sh [bench ...]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=env-android.sh
source "$HERE/env-android.sh" # shellcheck disable=SC1091
BENCHES=("$@")
[ ${#BENCHES[@]} -gt 0 ] || BENCHES=(aes_gcm chacha20poly1305 xchacha20poly1305 cipher sha1 sha2 sha3 md5 hkdf hmac x25519 ed25519 p256 p384 p521 mlkem768 mldsa hpke oprf vrf spake2plus rsa_pub rsa_priv blind_rsa argon2)
ARGS=(); for b in "${BENCHES[@]}"; do ARGS+=(--bench "$b"); done
MSG="$(mktemp)"
cargo bench -p rind-bench --features __bench_openssl,openssl-sys/vendored \
  --target armv7-linux-androideabi "${ARGS[@]}" --no-run --message-format=json > "$MSG"
cargo build -p rind-cpuid --release --target armv7-linux-androideabi
mkdir -p pkg && rm -f pkg/*
python3 - "$MSG" "$CARGO_TARGET_DIR" <<'PY'
import json, shutil, sys
for line in open(sys.argv[1]):
    try: ev = json.loads(line)
    except ValueError: continue
    if ev.get("reason") == "compiler-artifact" and ev.get("executable") and "bench" in ev["target"]["kind"]:
        shutil.copy2(ev["executable"], "pkg/" + ev["target"]["name"])
shutil.copy2(sys.argv[2] + "/armv7-linux-androideabi/release/rind-cpuid", "pkg/rind-cpuid")
PY
for f in pkg/*; do "$LLVM_STRIP" "$f"; done
ls -la pkg
# rind-bench's rsa_gen needs `NOISY_BENCHMARKS=1` at *compile* time (option_env!) or it lists no rows.
# rustls reads its test keys at the compile-time CARGO_MANIFEST_DIR; see the handoff doc.
