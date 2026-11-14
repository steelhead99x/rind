#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
"""Check ESP32-S3 placement of the IRAM SHA-256 body.

`object` reads one relocatable file. `image` reads a linked ELF, which is
the probe this script's shell builds and the sha2 image rind-hardware
links. The block and the driver must sit in IRAM, K in `.dram1` (a DRAM
output section in the link), the block must contain no call, and no
relocation may put those sections in flash text.

opt-level 0 is not checked. A debug build may outline helpers; that is
not a cache-off promise.
"""

import re
import subprocess
import sys

BLOCK = "sha256_compress_block"
DRIVER = "sha256_update_nblocks"
K_SECTION = ".dram1.rind_sha256_k"
BLOCK_SECTION = ".iram1.rind_sha256_compress_block"
DRIVER_SECTION = ".iram1.rind_sha256_nblocks"
CALL = re.compile(r"\bcallx?(?:0|4|8|12)\b")
INSN = re.compile(
    r"^\s*([0-9a-fA-F]+):\s+[0-9a-fA-F ]+\s+([a-z][a-z0-9.]*)\b(.*)$"
)


class Fail(Exception):
    pass


def run(cmd):
    out = subprocess.run(cmd, check=False, text=True, capture_output=True)
    if out.returncode != 0:
        raise Fail(f"{' '.join(cmd)} failed\n{out.stderr}")
    return out.stdout


def sections(objdump, path):
    """Map section name to (size, vma) from `objdump -h`."""
    found = {}
    for line in run([objdump, "-h", path]).splitlines():
        parts = line.split()
        # Idx Name Size VMA LMA File off Algn
        if len(parts) >= 6 and parts[1].startswith(".") and re.fullmatch(r"[0-9a-fA-F]+", parts[2]):
            found[parts[1]] = (int(parts[2], 16), int(parts[3], 16))
    return found


def section_rows(objdump, path):
    rows = []
    for line in run([objdump, "-h", path]).splitlines():
        parts = line.split()
        if len(parts) >= 4 and parts[1].startswith("."):
            rows.append(parts[1])
    return rows


def symbols(objdump, path):
    """name -> (value, size, section). Size may be 0 when the tool omits it."""
    found = {}
    for line in run([objdump, "-t", path]).splitlines():
        parts = line.split()
        if len(parts) < 4 or not re.fullmatch(r"[0-9a-fA-F]+", parts[0]):
            continue
        # addr flags section size name    or    addr flags section name
        if re.fullmatch(r"[0-9a-fA-F]+", parts[-2]) and parts[-3].startswith("."):
            name, size, section, value = parts[-1], int(parts[-2], 16), parts[-3], int(parts[0], 16)
        elif parts[-2].startswith("."):
            name, size, section, value = parts[-1], 0, parts[-2], int(parts[0], 16)
        else:
            continue
        found.setdefault(name, (value, size, section))
    return found


def pick(syms, needle):
    # Section symbols are named after the section, so `.iram1...compress_block`
    # contains the function's name. The function or object does not.
    hits = [item for item in syms.items() if needle in item[0] and not item[0].startswith(".")]
    if len(hits) != 1:
        names = ", ".join(name for name, _ in hits) or "(none)"
        raise Fail(f"expected one symbol containing {needle}, found {names}")
    return hits[0]


def relocations(readelf, path):
    """(section being relocated) -> list of target names."""
    current = None
    found = {}
    header = re.compile(r"Relocation section '([^']+)'")
    for line in run([readelf, "-rW", path]).splitlines():
        match = header.search(line)
        if match:
            name = match.group(1)
            current = name[5:] if name.startswith(".rela") else name
            found.setdefault(current, [])
            continue
        if current is None or "R_XTENSA_" not in line:
            continue
        parts = line.split()
        # Offset Info Type Symbol'sValue Symbol'sName [+ Addend]
        if len(parts) < 5:
            continue
        target = parts[4]
        found[current].append(target)
    return found


def disassemble(objdump, path, start, size, section):
    # Unlinked objects give every section VMA 0, so an address window alone
    # mixes the block with the driver. `-j` keeps the one section.
    if size <= 0:
        raise Fail(f"empty disassembly range at {start:#x}")
    stop = start + size
    text = run(
        [
            objdump,
            "-d",
            "-j",
            section,
            "--start-address",
            hex(start),
            "--stop-address",
            hex(stop),
            path,
        ]
    )
    insns = []
    for line in text.splitlines():
        match = INSN.match(line)
        if not match:
            continue
        addr = int(match.group(1), 16)
        if start <= addr < stop:
            insns.append((addr, match.group(2), match.group(3).strip()))
    if not insns:
        raise Fail(f"no instructions in {start:#x}..{stop:#x}")
    return insns


def check_ssai(insns):
    """Every ssai is consumed before the next unrelated instruction."""
    i = 0
    while i < len(insns):
        _addr, mnem, _rest = insns[i]
        if mnem != "ssai":
            i += 1
            continue
        window = insns[i + 1 : i + 5]
        mnems = [item[1] for item in window]
        if mnems[:1] == ["src"]:
            i += 2
            continue
        # The byte swap's `srli` by 16 is the same extract the Xtensa
        # backend prints as `extui`. Neither reads SAR.
        if len(mnems) >= 4 and mnems[0] in ("srli", "extui") and mnems[1:4] == ["src", "src", "src"]:
            i += 5
            continue
        raise Fail(
            "ssai is not paired with its src: "
            + " ".join(f"{item[1]}" for item in insns[i : i + 5])
        )
    return None


def check_no_calls(insns, what):
    for addr, mnem, rest in insns:
        if CALL.search(mnem):
            raise Fail(f"{what} contains {mnem} at {addr:#x} {rest}")


def l32r_address(insns, call_index):
    """Address in the comment of the l32r that feeds this call, if printed."""
    for addr, mnem, rest in reversed(insns[:call_index]):
        if mnem != "l32r":
            continue
        # `l32r a6, ADDR <sym>` or `l32r a6, off <lit> (ADDR <sym>)`.
        paren = re.search(r"\(([0-9a-fA-F]+)\b", rest)
        if paren:
            return int(paren.group(1), 16)
        bare = re.search(r"\b([0-9a-fA-F]{6,})\b", rest)
        if bare:
            return int(bare.group(1), 16)
        return None
    return None


def check_driver_calls(insns, block_addr, block_size, linked):
    """The driver may call only the block.

    On an object the call is `callx8` through a literal. The relocation
    check is what proves that literal is the block; the address in the
    object is still zero. A linked image resolves the `l32r` comment.
    """
    saw = False
    for i, (addr, mnem, rest) in enumerate(insns):
        if not CALL.search(mnem):
            continue
        saw = True
        if mnem.startswith("callx"):
            if not linked:
                continue
            target = l32r_address(insns, i)
            if target is None:
                raise Fail(f"driver {mnem} at {addr:#x} has no resolved literal")
            if not covers(block_addr, block_size, target):
                raise Fail(f"driver calls {target:#x}, outside the block")
            continue
        match = re.search(r"([0-9a-fA-F]{6,})", rest)
        if match is None or not covers(block_addr, block_size, int(match.group(1), 16)):
            raise Fail(f"driver {mnem} at {addr:#x} is not the block: {rest}")
    if not saw:
        raise Fail("driver makes no call, so the block is not reached")


def covers(start, size, addr):
    return start <= addr < start + size


def expect_placed_object(objdump, readelf, path):
    secs = sections(objdump, path)
    for name in (
        BLOCK_SECTION,
        BLOCK_SECTION + ".literal",
        DRIVER_SECTION,
        DRIVER_SECTION + ".literal",
        K_SECTION,
    ):
        if name not in secs:
            raise Fail(f"{path} is missing {name}")
    if secs[K_SECTION][0] != 0x100:
        raise Fail(f"K is {secs[K_SECTION][0]:#x} bytes, want 0x100")
    for name in section_rows(objdump, path):
        if name.startswith(".text") and "compress_block" in name:
            raise Fail(f"{path} still has the block in {name}")
        if name.startswith(".text") and "nblocks" in name:
            raise Fail(f"{path} still has the driver in {name}")
        if name.startswith(".rodata") and name.rstrip(".").endswith("K"):
            raise Fail(f"{path} still has K in {name}")
    rel = relocations(readelf, path)

    def allowed(section, target):
        if section == BLOCK_SECTION:
            return target.startswith(BLOCK_SECTION + ".literal")
        if section == BLOCK_SECTION + ".literal":
            return target.startswith(K_SECTION) or "sha256_k" in target
        if section == DRIVER_SECTION:
            return (
                target.startswith(DRIVER_SECTION + ".literal")
                or target.startswith(BLOCK_SECTION)
                or BLOCK in target
            )
        if section == DRIVER_SECTION + ".literal":
            return target.startswith(BLOCK_SECTION) or BLOCK in target
        return None

    saw_k = False
    for section, targets in rel.items():
        for target in targets:
            ok = allowed(section, target)
            if ok is None:
                continue
            if not ok:
                raise Fail(f"relocation in {section} targets {target}")
            if section == BLOCK_SECTION + ".literal" and (
                target.startswith(K_SECTION) or "sha256_k" in target
            ):
                saw_k = True
    if not saw_k:
        raise Fail("the block's literal pool has no relocation to K")
    syms = symbols(objdump, path)
    _bname, (baddr, bsize, bsec) = pick(syms, BLOCK)
    _dname, (daddr, dsize, dsec) = pick(syms, DRIVER)
    block_insns = disassemble(objdump, path, baddr, bsize, bsec)
    check_no_calls(block_insns, "block")
    check_ssai(block_insns)
    check_driver_calls(disassemble(objdump, path, daddr, dsize, dsec), baddr, bsize, linked=False)
    report_object(secs, len(block_insns))


def expect_ordinary_object(objdump, path):
    names = section_rows(objdump, path)
    for name in names:
        if name.startswith(".iram1") or name.startswith(".dram1"):
            raise Fail(f"{path} placed {name}")
    if not any(name.startswith(".text") and "compress_block" in name for name in names):
        raise Fail(f"{path} has no .text block")
    if not any("compress_block" in name and "literal" in name for name in names):
        raise Fail(f"{path} has no literal pool for the block")
    if not any(name.startswith(".rodata") for name in names):
        raise Fail(f"{path} has no .rodata for K")


def report_object(secs, block_insns):
    order = [
        BLOCK_SECTION,
        BLOCK_SECTION + ".literal",
        DRIVER_SECTION,
        DRIVER_SECTION + ".literal",
        K_SECTION,
    ]
    iram = 0
    for name in order:
        size, _vma = secs[name]
        kind = "DRAM" if name == K_SECTION else "IRAM"
        if kind == "IRAM":
            iram += size
        print(f"  {name} {size:#x} ({size} bytes) {kind}")
    print(f"  object IRAM {iram:#x} ({iram} bytes), block instructions {block_insns}")


def output_sections(objdump, path):
    """name -> (vma, size) for allocatable sections."""
    found = {}
    for line in run([objdump, "-h", path]).splitlines():
        parts = line.split()
        if len(parts) >= 6 and parts[1].startswith(".") and re.fullmatch(r"[0-9a-fA-F]+", parts[2]):
            found[parts[1]] = (int(parts[3], 16), int(parts[2], 16))
    return found


def section_at(outputs, addr):
    for name, (vma, size) in outputs.items():
        if size and vma <= addr < vma + size:
            return name
    return None


def parse_map(path):
    """Input section -> output section, from a GNU ld map."""
    current = None
    found = {}
    out_re = re.compile(r"^(\.\S+)\s+0x[0-9a-fA-F]+\s+0x[0-9a-fA-F]+")
    interesting = (BLOCK_SECTION, DRIVER_SECTION, K_SECTION)
    for raw in open(path, encoding="utf-8", errors="replace"):
        line = raw.rstrip()
        match = out_re.match(line)
        if match and not line.startswith(" "):
            current = match.group(1)
            continue
        stripped = line.strip()
        for name in interesting:
            if stripped.startswith(name) and (len(stripped) == len(name) or stripped[len(name)] in " ."):
                if current is None:
                    raise Fail(f"{name} appears in the map before any output section")
                found.setdefault(name, current)
    return found


def expect_image(objdump, path, map_path):
    syms = symbols(objdump, path)
    bname, (baddr, bsize, bsec) = pick(syms, BLOCK)
    dname, (daddr, dsize, dsec) = pick(syms, DRIVER)
    kname, (kaddr, ksize, ksec) = pick(syms, "sha256_k")
    outputs = output_sections(objdump, path)
    b_out = section_at(outputs, baddr) or bsec
    d_out = section_at(outputs, daddr) or dsec
    k_out = section_at(outputs, kaddr) or ksec
    for label, out in (("block", b_out), ("driver", d_out)):
        if "iram" not in out:
            raise Fail(f"{label} is in {out}, not IRAM")
        if "flash" in out:
            raise Fail(f"{label} was relocated into {out}")
    if "dram" not in k_out or "flash" in k_out:
        raise Fail(f"K is in {k_out}, not DRAM")
    if ksize not in (0, 0x100):
        raise Fail(f"K symbol is {ksize:#x} bytes, want 0x100")
    placed = parse_map(map_path)
    for name, want in (
        (BLOCK_SECTION, "iram"),
        (DRIVER_SECTION, "iram"),
        (K_SECTION, "dram"),
    ):
        out = placed.get(name)
        if out is None:
            raise Fail(f"map {map_path} does not place {name}")
        if "flash" in out or want not in out:
            raise Fail(f"{name} relocated to {out}")
        if name == K_SECTION and "dram" not in out:
            raise Fail(f"{name} is {out}, not .dram1's DRAM output")
    block_insns = disassemble(objdump, path, baddr, bsize, b_out)
    check_no_calls(block_insns, "block")
    check_ssai(block_insns)
    check_driver_calls(disassemble(objdump, path, daddr, dsize, d_out), baddr, bsize, linked=True)
    # A leftover static relocation into flash text would still name that section.
    text = run([objdump, "-r", path])
    for line in text.splitlines():
        if "flash" in line and ".text" in line and (
            BLOCK in line or DRIVER in line or "sha256_k" in line or "rind_sha256" in line
        ):
            raise Fail(f"relocation to flash text: {line.strip()}")
    print(f"  block {bname} {baddr:#x} {bsize:#x} ({bsize} bytes) in {b_out}")
    print(f"  driver {dname} {daddr:#x} {dsize:#x} ({dsize} bytes) in {d_out}")
    print(f"  K {kname} {kaddr:#x} size {ksize:#x} in {k_out}")
    print(f"  map block -> {placed[BLOCK_SECTION]}")
    print(f"  map driver -> {placed[DRIVER_SECTION]}")
    print(f"  map K -> {placed[K_SECTION]} ({K_SECTION})")
    print(f"  block instructions {len(block_insns)}, no calls, ssai paired")


def main(argv):
    if len(argv) < 2 or argv[0] not in ("object", "image"):
        raise SystemExit(
            "usage: esp32s3-sha256-layout.py object OBJDUMP READELF PATH placed|ordinary\n"
            "       esp32s3-sha256-layout.py image OBJDUMP PATH MAP"
        )
    try:
        if argv[0] == "object":
            _mode, objdump, readelf, path, kind = argv
            if kind == "placed":
                expect_placed_object(objdump, readelf, path)
            elif kind == "ordinary":
                expect_ordinary_object(objdump, path)
            else:
                raise Fail(f"unknown object kind {kind}")
        else:
            _mode, objdump, path, map_path = argv
            expect_image(objdump, path, map_path)
    except Fail as exc:
        print(f"esp32s3-sha256-layout: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
