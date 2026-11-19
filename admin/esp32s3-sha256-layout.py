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
# GNU objdump separates the address, the bytes, and the mnemonic with tabs.
# Splitting on them keeps a mnemonic made of hex letters, such as `add`,
# out of the bytes column.
INSN = re.compile(r"^\s*([0-9a-fA-F]+):\t[0-9a-fA-F ]+\t([a-z][a-z0-9.]*)\b(.*)$")
# FIPS 180-4 SHA-256 rotate distances. 8 is the byte swap, not a rotate.
ROTATE_SAR = {2, 6, 7, 11, 13, 17, 18, 19, 22, 25}
REG_NAME = re.compile(r"\b[a-zA-Z]+[0-9]+\b")
# ESP32-S3 internal SRAM on the instruction and data buses (TRM, "System
# and Memory"). Code and data here stay reachable with the flash cache off.
IRAM = (0x40370000, 0x403E0000)
DRAM = (0x3FC88000, 0x3FD00000)


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
    # contains the function's name. The function or object does not. Match the
    # whole identifier: `sha256_compress_blocks`, the portable function, is a
    # different one and linking may keep both. Legacy (`_ZN...E`) and v0 (`_R...`)
    # mangling both length-prefix each path component (`21sha256_compress_block`),
    # so the prefix plus the name pins the identifier, and `22sha256_compress_blocks`
    # never contains it. Walking the prefixes from the start is wrong for v0: its
    # base62 crate disambiguator holds digits that read as a length.
    tag = f"{len(needle)}{needle}"
    hits = [item for item in syms.items() if (item[0] == needle or tag in item[0]) and not item[0].startswith(".")]
    if len(hits) != 1:
        names = ", ".join(name for name, _ in hits) or "(none)"
        raise Fail(f"expected one symbol named {needle}, found {names}")
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


def immediates(rest):
    """Integer operands, after register names such as `a14` are removed."""
    return [int(n) for n in re.findall(r"\d+", REG_NAME.sub(" ", rest))]


def check_ssai(insns):
    """Every ssai is a FIPS rotate or the big-endian byte swap.

    A rotate is `ssai` of 2, 6, 7, 11, 13, 17, 18, 19, 22, or 25, then
    `src`. The byte swap is `l32i`, `ssai 8`, `extui` of bits 16..32,
    then three `src`. Pairing alone would accept `ssai 12` or an `src`
    that consumes an older SAR, so every `src` must also belong to one of
    those two sequences.
    """
    consumed = set()
    i = 0
    while i < len(insns):
        _addr, mnem, rest = insns[i]
        if mnem != "ssai":
            i += 1
            continue
        found = immediates(rest)
        if len(found) != 1:
            raise Fail(f"ssai has no single immediate: {rest}")
        n = found[0]
        window = insns[i + 1 : i + 5]
        mnems = [item[1] for item in window]
        if n in ROTATE_SAR and mnems[:1] == ["src"]:
            consumed.add(i + 1)
            i += 2
            continue
        # The byte swap's `extui` does not read SAR.
        shift = immediates(window[0][2]) if window else []
        if (
            n == 8
            and i > 0
            and insns[i - 1][1] == "l32i"
            and len(mnems) >= 4
            and mnems[0] == "extui"
            and shift == [16, 16]
            and mnems[1:4] == ["src", "src", "src"]
        ):
            consumed.update((i + 2, i + 3, i + 4))
            i += 5
            continue
        shown = " ".join(f"{item[1]} {item[2]}".strip() for item in insns[max(0, i - 1) : i + 5])
        raise Fail(f"ssai {n} is not a FIPS rotate or the byte swap: {shown}")
    for index, (addr, mnem, rest) in enumerate(insns):
        if mnem == "src" and index not in consumed:
            raise Fail(f"src at {addr:#x} {rest} does not follow its own ssai")
    return None


def check_no_calls(insns, what):
    for addr, mnem, rest in insns:
        if CALL.search(mnem):
            raise Fail(f"{what} contains {mnem} at {addr:#x} {rest}")


# Mnemonics whose first register operand is read, not written.
NO_DEST = re.compile(r"^(?:s(?:8|16|32)\w*|b\w*)(?:\.n)?$")


def l32r_address(insns, call_index, reg):
    """Address in the comment of the l32r that defines `reg` for this call.

    The nearest earlier instruction that writes `reg` must be an `l32r`
    with a printed address; any other writer, or none, is unresolved.
    """
    for _addr, mnem, rest in reversed(insns[:call_index]):
        if NO_DEST.match(mnem):
            continue
        regs = re.findall(r"\ba\d+\b", rest)
        if not regs or regs[0] != reg:
            continue
        if mnem != "l32r":
            return None
        # `l32r a6, ADDR <sym>` or `l32r a6, off <lit> (ADDR <sym>)`.
        paren = re.search(r"\(([0-9a-fA-F]+)\b", rest)
        if paren:
            return int(paren.group(1), 16)
        bare = re.search(r"\b([0-9a-fA-F]{6,})\b", rest)
        if bare:
            return int(bare.group(1), 16)
        return None
    return None


def check_driver_calls(insns, block_addr, linked):
    """The driver may call only the block, at its entry point.

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
            operand = re.findall(r"\ba\d+\b", rest)
            target = l32r_address(insns, i, operand[0]) if operand else None
            if target is None:
                raise Fail(f"driver {mnem} at {addr:#x} {rest} has no resolved literal")
            if target != block_addr:
                raise Fail(f"driver calls {target:#x}, not the block's entry {block_addr:#x}")
            continue
        match = re.search(r"([0-9a-fA-F]{6,})", rest)
        if match is None or int(match.group(1), 16) != block_addr:
            raise Fail(f"driver {mnem} at {addr:#x} is not the block: {rest}")
    if not saw:
        raise Fail("driver makes no call, so the block is not reached")



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
    check_driver_calls(disassemble(objdump, path, daddr, dsize, dsec), baddr, linked=False)
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
    # Addresses, not only names: an output named for IRAM could still be
    # linked at a flash address.
    for label, addr, size, (lo, hi) in (
        ("block", baddr, bsize, IRAM),
        ("driver", daddr, dsize, IRAM),
        ("K", kaddr, ksize, DRAM),
    ):
        if size <= 0 or not (lo <= addr and addr + size <= hi):
            raise Fail(f"{label} {addr:#x}+{size:#x} is outside internal RAM {lo:#x}..{hi:#x}")
    for label, out in (("block", b_out), ("driver", d_out)):
        if "iram" not in out:
            raise Fail(f"{label} is in {out}, not IRAM")
        if "flash" in out:
            raise Fail(f"{label} was relocated into {out}")
    if "dram" not in k_out or "flash" in k_out:
        raise Fail(f"K is in {k_out}, not DRAM")
    if ksize != 0x100:
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
    check_driver_calls(disassemble(objdump, path, daddr, dsize, d_out), baddr, linked=True)
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


# Real symbol names from rustc 1.98.1 (`-C symbol-mangling-version=v0` and
# `legacy`, crate `rind`, module `low::portable::sha256_iram`, one build per
# `-C metadata`). The v0 crate hashes with digits are the ones a greedy
# length-prefix walk misread.
V0 = "_RNvNtNtNtCs{}_4rind3low8portable11sha256_iram{}"
LEGACY = "_ZN4rind3low8portable11sha256_iram{}17h{}E"
V0_HASHES = ["1paxuMSCu6r", "30zkQqDHX6G", "51p7yVGAJlh", "600rUf00GRX", "70sRogeUpn8", "79wRi01wFOF"]
LEGACY_HASHES = ["07d5edefbe545dc7", "0c48ecaf86fb867b", "131de65c6f72ccff"]


def selftest():
    """Check `pick` on real v0 and legacy names, with the portable `blocks` function beside."""
    wanted = {BLOCK: "21" + BLOCK, DRIVER: "21" + DRIVER, "sha256_k": "8sha256_k"}
    for needle, ident in wanted.items():
        for crate in V0_HASHES:
            names = [V0.format(crate, ident), V0.format(crate, "22sha256_compress_blocks"), V0.format(crate, "21sha256_update_nblocks")]
            syms = {n: (0, 0, ".text") for n in names + [".iram1." + needle, "core3fmt5write"]}
            got = pick(syms, needle)[0]
            assert got == V0.format(crate, ident), (needle, crate, got)
        for h in LEGACY_HASHES:
            syms = {LEGACY.format(ident, h): (0, 0, ".text"), LEGACY.format("22sha256_compress_blocks", h): (0, 0, ".text")}
            assert pick(syms, needle)[0] == LEGACY.format(ident, h), (needle, h)
    # The portable `blocks` function alone is not the block, and two builds are ambiguous.
    for syms in (
        {V0.format("1paxuMSCu6r", "22sha256_compress_blocks"): (0, 0, ".text")},
        {V0.format("1paxuMSCu6r", "21" + BLOCK): (0, 0, ".text"), V0.format("30zkQqDHX6G", "21" + BLOCK): (0, 0, ".text")},
    ):
        try:
            pick(syms, BLOCK)
        except Fail:
            continue
        raise AssertionError("pick accepted a missing or ambiguous symbol")
    print("esp32s3-sha256-layout: selftest ok")


def main(argv):
    if argv == ["selftest"]:
        selftest()
        return 0
    if len(argv) < 2 or argv[0] not in ("object", "image"):
        raise SystemExit(
            "usage: esp32s3-sha256-layout.py selftest\n"
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
