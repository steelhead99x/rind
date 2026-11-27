#!/usr/bin/env bash
# steelhead99x/rind#326's IRAM-unrolled SHA-512 row: the ESP-IDF firmware.
#
# The S3 workshop firmware is xtensa-esp32s3-none-elf, where
# `esp32s3-sha512-unrolled` keeps the unrolled body in ordinary flash; only
# xtensa-esp32s3-espidf places it in IRAM (`.iram1.text`) and K in internal
# DRAM (`.dram1.rodata`). So the board A/B's IRAM-unrolled row is measured
# here, on admin/hw/esp32s3-idf-sha512, the ESP-IDF image, built with that
# feature at the PR's base and head:
#
#   1. Builds four images: base and head, each at 80 and 240 MHz.
#   2. Checks each ELF's placement: rind's unrolled sha512_compress_block in
#      the S3's internal IRAM (0x40370000..0x403e0000) and sha512's K in its
#      internal DRAM (0x3fc88000..0x3fd00000). A build where either is
#      elsewhere is not the IRAM row, and fails here.
#   3. With RIND_S3_PORT set, flashes the images interleaved with espflash,
#      base first and between every head image (base, head, base, ...,
#      base: RIND_FW_HEADS head images, 5 by default), at 80 MHz and then
#      240 MHz, capturing RIND_FW_CAPTURE seconds (60) of the console after
#      each flash. A capture counts only if every known answer in it reads
#      PASS; its first round is dropped, and its time at each size is the
#      median over the rest. Without RIND_S3_PORT it stops after step 2 and
#      names the images to flash.
#
# Host: Linux x86_64 with the espup toolchain the board uses (`cargo +esp`),
#   ldproxy (`cargo install ldproxy`), python3, git, network for ESP-IDF
#   v5.5.1's first download into ~/.espressif, the xtensa-esp-elf binutils
#   (admin/esp32s3-toolchain.sh), and espflash plus the board on
#   RIND_S3_PORT for step 3.
# Takes: about 20 minutes to build the first time (ESP-IDF itself), a few per
#   image after; step 3 about 2 * (2 * RIND_FW_HEADS + 1) * (RIND_FW_CAPTURE
#   + 20) seconds.
# Writes: .tmp/hw/esp32s3-sha512-idf-<time>/ with summary.md (the comment
#   for #326), placement.txt, build-<image>.log, cap-<n>-<image>.log,
#   images/<image>.elf, run.log.
# Exits: 0 when every image is placed in IRAM and, with RIND_S3_PORT, every
#   capture's known answers passed; 1 otherwise, after writing summary.md.
#   The timings are reported, not judged.
#
# Usage: [RIND_S3_PORT=/dev/ttyACM0] admin/hw/esp32s3-sha512-idf.sh [--preflight]
# Pin the commits of an earlier run with HW_BASE_REV and HW_HEAD_REV.
set -euo pipefail
# shellcheck source=admin/hw/lib.sh
source "$(dirname "$0")/lib.sh"
hw_args "$@"

[[ $(uname -s) == Linux && $(uname -m) == x86_64 ]] ||
    hw_refuse "the espup toolchain here is Linux x86_64, not $(uname -s) $(uname -m)"
hw_need_tools git python3 ldproxy rustup
rustup run esp rustc --version >/dev/null 2>&1 ||
    hw_refuse "the espup toolchain \`esp\` is not installed (espup install)"
# shellcheck source=admin/esp32s3-toolchain.sh
. "$HW_ROOT/admin/esp32s3-toolchain.sh"
[[ -x $nm ]] || hw_refuse "$nm is missing; install the xtensa-esp-elf binutils (admin/esp32s3-toolchain.sh)"
port=${RIND_S3_PORT:-}
if [[ -n $port ]]; then
    hw_need_tools espflash stty timeout
    [[ -c $port ]] || hw_refuse "RIND_S3_PORT=$port is not a serial device"
fi
heads=${RIND_FW_HEADS:-5}
capture=${RIND_FW_CAPTURE:-60}
[[ $heads =~ ^[1-9][0-9]*$ && $capture =~ ^[1-9][0-9]*$ ]] ||
    hw_die "RIND_FW_HEADS and RIND_FW_CAPTURE are positive integers"
hw_preflight_done

hw_setup
base=$(hw_rev refs/heads/main "${HW_BASE_REV:-}")
head=$(hw_rev refs/pull/326/head "${HW_HEAD_REV:-}")
hw_say "base $base, head $head"
fw_src=$HW_ROOT/admin/hw/esp32s3-idf-sha512
mkdir -p "$HW_RUN/images"

# Step 1: the firmware is this checkout's, its rind each revision's.
failed=0
built=()
for name in base head; do
    sha=${!name}
    wt=$(hw_worktree "$name" "$sha")
    grep -q '^esp32s3-sha512-unrolled' "$wt/rind/Cargo.toml" ||
        hw_die "$name ($sha) has no esp32s3-sha512-unrolled feature"
    for mhz in 80 240; do
        image=$name-${mhz}mhz
        fw=$HW_RUN/fw/$image
        mkdir -p "$fw"
        cp -R "$fw_src/." "$fw/"
        rm -rf "$fw/target"
        sed -i "s|path = \"../../../rind\"|path = \"$wt/rind\"|" "$fw/Cargo.toml"
        grep -q "path = \"$wt/rind\"" "$fw/Cargo.toml" || hw_die "could not point $image at $wt/rind"
        defaults="$fw/sdkconfig.defaults"
        [[ $mhz == 80 ]] || defaults+=";$fw/sdkconfig.240mhz"
        hw_say "building $image"
        if (cd "$fw" && RIND_FW_LABEL="$image@${sha:0:12}" RIND_FW_MHZ=$mhz \
            ESP_IDF_SDKCONFIG_DEFAULTS="$defaults" CARGO_TARGET_DIR="$fw/target" \
            hw_gate cargo +esp build --release) >"$HW_RUN/build-$image.log" 2>&1; then
            cp "$fw/target/xtensa-esp32s3-espidf/release/rind-esp32s3-idf-sha512" "$HW_RUN/images/$image.elf"
            built+=("$image")
        else
            hw_say "$image did not build (build-$image.log)"
            failed=1
        fi
    done
done

# Step 2: the unrolled compressor in IRAM and K in DRAM, in each ELF.
: >"$HW_RUN/placement.txt"
placed=()
for image in "${built[@]}"; do
    if "$nm" -C "$HW_RUN/images/$image.elf" | python3 -c '
import re, sys
image = sys.argv[1]
fn = k = None
for line in sys.stdin:
    m = re.match(r"^([0-9a-f]+) \S (.*)$", line.strip())
    if not m:
        continue
    addr, sym = int(m.group(1), 16), re.sub(r"(::h[0-9a-f]{16})?(\.llvm\.\d+)?$", "", m.group(2))
    if sym.endswith("sha512_esp32s3::unrolled::sha512_compress_block"):
        fn = addr
    elif re.search(r"generic::sha512::K$", sym):
        k = addr
ok = True
for what, addr, lo, hi, where in (("sha512_compress_block", fn, 0x40370000, 0x403E0000, "IRAM"),
                                  ("sha512::K", k, 0x3FC88000, 0x3FD00000, "DRAM")):
    if addr is None:
        print(f"{image}: {what} not found"); ok = False
    elif lo <= addr < hi:
        print(f"{image}: {what} at {addr:#010x}, internal {where}")
    else:
        print(f"{image}: {what} at {addr:#010x}, NOT internal {where}"); ok = False
sys.exit(0 if ok else 1)
' "$image" >>"$HW_RUN/placement.txt"; then
        placed+=("$image")
    else
        failed=1
    fi
done
cat "$HW_RUN/placement.txt"

# Step 3: interleaved on the board.
captures=0
if [[ -n $port ]]; then
    for mhz in 80 240; do
        order=()
        for ((i = 0; i < heads; i++)); do order+=("base-${mhz}mhz" "head-${mhz}mhz"); done
        order+=("base-${mhz}mhz")
        for image in "${order[@]}"; do
            [[ " ${placed[*]} " == *" $image "* ]] || { hw_say "skipping $image: not built and placed"; continue; }
            captures=$((captures + 1))
            cap=$HW_RUN/cap-$(printf %02d "$captures")-$image.log
            hw_say "flashing $image (capture $captures)"
            espflash flash --chip esp32s3 --port "$port" "$HW_RUN/images/$image.elf" >"$cap.flash" 2>&1 ||
                { hw_say "flashing $image failed ($cap.flash)"; failed=1; continue; }
            stty -F "$port" 115200 raw -echo -hupcl
            timeout "$capture" cat "$port" >"$cap" || true
        done
    done
fi

# The summary: per image, the median over its captures of each capture's
# median over its rounds after the first.
python3 - "$HW_RUN" "$base" "$head" "$port" "$heads" "$capture" "$(hostname)" \
    "$(date -u +%Y-%m-%dT%H:%MZ)" "$failed" >"$HW_RUN/summary.md" <<'PY' || failed=1
import glob, os, re, statistics, sys
run, base, head, port, heads, capture, host, when, failed = sys.argv[1:]
placement = open(os.path.join(run, "placement.txt")).read().strip()
out = ["### #326 on hardware: the IRAM-unrolled row (ESP-IDF image)", "",
       f"base `{base}` (main), head `{head}`; {host}, {when}. "
       "admin/hw/esp32s3-idf-sha512 with `esp32s3-sha512-unrolled` on "
       "`xtensa-esp32s3-espidf`, ESP-IDF v5.5.1, opt-level 3.", "",
       "**Placement** (step 2):", "", "```", placement or "no image built", "```", ""]
bad = failed != "0"
if not port:
    out += ["**Board A/B:** not run (RIND_S3_PORT unset). Flash images/*.elf with "
            "admin/hw/esp32s3-sha512-idf.sh and RIND_S3_PORT set, or interleave them "
            "yourself, base first and between every head image."]
else:
    per = {}  # image -> size -> [capture medians]
    rejected = []
    # What every round of admin/hw/esp32s3-idf-sha512 prints.
    KATS = {"empty", "abc", "two-block", "bench-16B", "bench-243B", "bench-1500B", "bench-16384B"}
    SIZES = {16, 243, 1500, 16384}

    def check_round(r, image):
        """Why round `r` of a capture of `image` is not whole and passing, or None."""
        want_label, want_mhz = image + "@", image.rsplit("-", 1)[1].removesuffix("mhz")
        if not r["label"].startswith(want_label) or r["mhz"] != want_mhz:
            return f"round {r['n']} booted {r['label']} at {r['mhz']} MHz, not {image}"
        names = [k[0] for k in r["kat"]]
        if sorted(names) != sorted(KATS):
            return (f"round {r['n']} has known answers {sorted(names)}, "
                    f"want each of {sorted(KATS)} once")
        if any(v != "PASS" for _, v in r["kat"]):
            return f"round {r['n']}: " + ", ".join(f"{k} {v}" for k, v in r["kat"] if v != "PASS")
        if set(r["bench"]) != SIZES or r["nbench"] != len(SIZES):
            return f"round {r['n']} timed sizes {sorted(r['bench'])}, want each of {sorted(SIZES)} once"
        return None

    for cap in sorted(glob.glob(os.path.join(run, "cap-*.log"))):
        image = re.match(r"cap-\d+-(.*)\.log$", os.path.basename(cap)).group(1)
        rounds, cur, why = [], None, None
        for line in open(cap, errors="replace"):
            line = line.strip()
            if m := re.match(r"^IDF-BENCH v1 label=(\S+) mhz=(\S+) round=(\d+)$", line):
                cur = {"label": m.group(1), "mhz": m.group(2), "n": int(m.group(3)),
                       "kat": [], "bench": {}, "nbench": 0}
            elif cur is None:
                continue
            elif m := re.match(r"^KAT sha512 (\S+) (\S+)$", line):
                cur["kat"].append((m.group(1), m.group(2)))
            elif m := re.match(r"^BENCH sha512 (\d+)B ([0-9.]+) us$", line):
                cur["bench"][int(m.group(1))] = float(m.group(2))
                cur["nbench"] += 1
            elif line == f"ROUND-END {cur['n']}":
                why = why or check_round(cur, image)
                rounds.append(cur)
                cur = None
        if why is None and len(rounds) < 3:
            why = f"{len(rounds)} whole rounds, want at least 3"
        if why is not None:
            rejected.append(f"{os.path.basename(cap)}: {why}")
            bad = True
            continue
        for size in SIZES:
            per.setdefault(image, {}).setdefault(size, []).append(
                statistics.median(r["bench"][size] for r in rounds[1:]))
    for mhz in ("80", "240"):
        b, h = per.get(f"base-{mhz}mhz", {}), per.get(f"head-{mhz}mhz", {})
        if not b or not h:
            out += [f"**{mhz} MHz:** no accepted captures of both images.", ""]
            bad = True
            continue
        out += [f"**{mhz} MHz**, rind SHA-512, IRAM-unrolled (MEASURED; medians of "
                f"{len(next(iter(b.values())))} base and {len(next(iter(h.values())))} head "
                f"captures, interleaved, {capture} s each, first round dropped):", "",
                "| size | base | head | head vs base | base spread |", "|---|---|---|---|---|"]
        for size in sorted(b):
            bm, hm = statistics.median(b[size]), statistics.median(h.get(size, [float("nan")]))
            spread = (max(b[size]) - min(b[size])) / bm * 100
            out.append(f"| {size} B | {bm:.2f} us | {hm:.2f} us | {(hm - bm) / bm * 100:+.2f}% "
                       f"| {spread:.2f}% |")
        out.append("")
    out += ["Every round of every accepted capture booted the image flashed, at its "
            "frequency, and printed all seven known answers (FIPS 180-4's three SHA-512 "
            "examples and the four bench inputs) as PASS and all four sizes' times."]
    if rejected:
        out += ["", "Rejected captures:", ""] + [f"- {r}" for r in rejected]
print("\n".join(out))
sys.exit(1 if bad else 0)
PY
cat "$HW_RUN/summary.md"
hw_follow_up 326 "$HW_RUN/summary.md"
if ((failed)); then
    echo "esp32s3-sha512-idf: an image did not build, was not placed in IRAM, or a capture failed; summary.md says which" >&2
    exit 1
fi
