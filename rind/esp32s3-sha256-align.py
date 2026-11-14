#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

"""Align libcrux-sha2's SHA-256 text to the ESP32-S3 instruction-cache stride.

ESP-IDF's default instruction cache is 16 KiB and 8-way; 32 KiB and 4-way
are the other Kconfig pairs. Their set strides are 2048, 4096, and 8192
bytes, so 8192 is a multiple of every one. A `.text` input linked ahead of
libcrux can still change HACL* SHA-256's address. With this alignment that
delta is a multiple of every stride, and the body's set mapping against
code placed earlier stays the same.

The edit changes only `sh_addralign` on executable `.text.*sha256_update*`
sections. Instruction bytes are untouched. `lto` recompiles those sections
and drops the alignment. This does not measure cycles on a board.
"""

import hashlib
import os
import struct
import subprocess
import sys
import tempfile

ALIGN = 8192
NEEDLE = "sha256_update"
SHT_PROGBITS = 1
SHF_EXECINSTR = 0x4


class ElfError(Exception):
    pass


def _u(fmt, data, offset):
    size = struct.calcsize(fmt)
    if offset < 0 or offset + size > len(data):
        raise ElfError(f"truncated ELF at {offset}")
    return struct.unpack_from(fmt, data, offset)


def align_elf(data):
    """Raise matching section alignments. Return `(changed, matched)`."""
    if len(data) < 16 or data[:4] != b"\x7fELF":
        raise ElfError("not an ELF object")
    elf_class, endian = data[4], data[5]
    if endian not in (1, 2):
        raise ElfError(f"bad ELF endian {endian}")
    order = "<" if endian == 1 else ">"
    if elf_class == 1:
        (e_shoff,) = _u(order + "I", data, 32)
        e_shentsize, e_shnum, e_shstrndx = _u(order + "HHH", data, 46)
        sh_size = 40
        name_fmt = order + "I"
        type_fmt = order + "I"
        flags_fmt = order + "I"
        align_fmt = order + "I"
        align_at = 32
    elif elf_class == 2:
        (e_shoff,) = _u(order + "Q", data, 40)
        e_shentsize, e_shnum, e_shstrndx = _u(order + "HHH", data, 58)
        sh_size = 64
        name_fmt = order + "I"
        type_fmt = order + "I"
        flags_fmt = order + "Q"
        align_fmt = order + "Q"
        align_at = 48
    else:
        raise ElfError(f"bad ELF class {elf_class}")
    if e_shentsize != sh_size:
        raise ElfError(f"unexpected section header size {e_shentsize}")
    if e_shnum == 0 or e_shstrndx >= e_shnum:
        raise ElfError("unsupported section-header encoding")

    def sh_field(index, fmt, at):
        return _u(fmt, data, e_shoff + index * sh_size + at)[0]

    str_off = sh_field(e_shstrndx, order + ("I" if elf_class == 1 else "Q"), 16 if elf_class == 1 else 24)
    str_size = sh_field(e_shstrndx, order + ("I" if elf_class == 1 else "Q"), 20 if elf_class == 1 else 32)
    if str_off + str_size > len(data):
        raise ElfError("truncated section-name table")
    names = data[str_off : str_off + str_size]

    def section_name(index):
        start = sh_field(index, name_fmt, 0)
        if start >= len(names):
            raise ElfError("section name past the string table")
        end = names.find(b"\0", start)
        if end < 0:
            raise ElfError("unterminated section name")
        return names[start:end].decode("utf-8", "replace")

    changed = 0
    matched = 0
    for index in range(e_shnum):
        name = section_name(index)
        if not (name.startswith(".text.") and NEEDLE in name):
            continue
        if sh_field(index, type_fmt, 4) != SHT_PROGBITS:
            continue
        if sh_field(index, flags_fmt, 8) & SHF_EXECINSTR == 0:
            continue
        matched += 1
        where = e_shoff + index * sh_size + align_at
        (current,) = _u(align_fmt, data, where)
        if current >= ALIGN and current % ALIGN == 0:
            continue
        struct.pack_into(align_fmt, data, where, ALIGN)
        changed += 1
        print(f"aligned {name} {current} -> {ALIGN}", file=sys.stderr)
    return changed, matched


def align_archive(data):
    """Patch ELF members of a System V archive in place. Return `(changed, matched)`."""
    if not data.startswith(b"!<arch>\n"):
        raise ElfError("not an ar archive")
    changed = 0
    matched = 0
    pos = 8
    while pos + 60 <= len(data):
        header = data[pos : pos + 60]
        if header[58:60] != b"`\n":
            raise ElfError(f"bad ar header at {pos}")
        size = int(header[48:58])
        content = pos + 60
        name = header[:16].decode("ascii", "replace")
        extra = 0
        if name.startswith("#1/"):
            extra = int(name[3:].strip())
        body = content + extra
        end = content + size
        if end > len(data):
            raise ElfError("truncated archive member")
        chunk = bytearray(data[body:end])
        if chunk.startswith(b"\x7fELF"):
            member_changed, member_matched = align_elf(chunk)
            changed += member_changed
            matched += member_matched
            data[body:end] = chunk
        nxt = end + (end & 1)
        pos = nxt
    if pos < len(data) and data[pos:] not in (b"", b"\n"):
        raise ElfError("archive did not end on a member boundary")
    return changed, matched


def align_bytes(data):
    blob = bytearray(data)
    if blob.startswith(b"!<arch>\n"):
        changed, matched = align_archive(blob)
    elif blob.startswith(b"\x7fELF"):
        changed, matched = align_elf(blob)
    else:
        raise ElfError("expected an ELF object or an ar archive")
    return blob, changed, matched


def align_file(path):
    with open(path, "rb") as handle:
        original = handle.read()
    updated, changed, matched = align_bytes(original)
    if changed and bytes(updated) != original:
        if len(updated) != len(original):
            raise ElfError("alignment changed the file size")
        with open(path, "r+b") as handle:
            handle.write(updated)
            handle.flush()
            os.fsync(handle.fileno())
    if matched == 0:
        found = text_section_names(original)
        shown = found[:40]
        extra = len(found) - len(shown)
        listed = ", ".join(shown) or "(no .text sections)"
        if extra:
            listed = f"{listed} (+{extra} more)"
        raise ElfError(
            f"{path} has no executable .text.*{NEEDLE}* section; "
            f"SHA-256 alignment was not applied. .text sections: {listed}"
        )
    return changed


def text_section_names(data):
    """`.text` section names, for the error when nothing matched."""
    names = []
    if data.startswith(b"\x7fELF"):
        names.extend(_text_names(data))
    elif data.startswith(b"!<arch>\n"):
        pos = 8
        while pos + 60 <= len(data):
            header = data[pos : pos + 60]
            if header[58:60] != b"`\n":
                break
            size = int(header[48:58])
            content = pos + 60
            name = header[:16].decode("ascii", "replace")
            extra = int(name[3:].strip()) if name.startswith("#1/") else 0
            end = content + size
            names.extend(_text_names(data[content + extra : end]))
            pos = end + (end & 1)
    return names


def _text_names(blob):
    if not blob.startswith(b"\x7fELF"):
        return []
    try:
        found = []
        elf_class, endian = blob[4], blob[5]
        if endian not in (1, 2) or elf_class not in (1, 2):
            return []
        order = "<" if endian == 1 else ">"
        if elf_class == 1:
            (e_shoff,) = _u(order + "I", blob, 32)
            e_shentsize, e_shnum, e_shstrndx = _u(order + "HHH", blob, 46)
            sh_size = 40
            off_fmt, off_at = order + "I", 16
            size_fmt, size_at = order + "I", 20
        else:
            (e_shoff,) = _u(order + "Q", blob, 40)
            e_shentsize, e_shnum, e_shstrndx = _u(order + "HHH", blob, 58)
            sh_size = 64
            off_fmt, off_at = order + "Q", 24
            size_fmt, size_at = order + "Q", 32
        if e_shentsize != sh_size or e_shnum == 0 or e_shstrndx >= e_shnum:
            return []

        def field(index, fmt, at):
            return _u(fmt, blob, e_shoff + index * sh_size + at)[0]

        str_off = field(e_shstrndx, off_fmt, off_at)
        str_size = field(e_shstrndx, size_fmt, size_at)
        table = blob[str_off : str_off + str_size]
        for index in range(e_shnum):
            start = field(index, order + "I", 0)
            end = table.find(b"\0", start)
            if end < 0:
                continue
            name = table[start:end].decode("utf-8", "replace")
            if name == ".text" or name.startswith(".text."):
                found.append(name)
        return found
    except ElfError:
        return []


def section_align(path, name):
    """Alignment of `name` as readelf reports it. Independent of align_elf."""
    text = subprocess.check_output(["readelf", "-S", "-W", path], text=True)
    for line in text.splitlines():
        if f" {name} " in f" {line} " or line.strip().endswith(name) or f"] {name} " in line:
            # readelf: index, name, type, addr, off, size, es, flags, lk, inf, align
            parts = line.split()
            if len(parts) >= 3 and parts[2] == name:
                return int(parts[-1])
    raise ElfError(f"{path} has no section {name}")


def check_elf(path, nm):
    """Fail unless every linked sha256_update text symbol is stride-aligned."""
    env = dict(os.environ)
    env["LC_ALL"] = "C"
    text = subprocess.check_output([nm, "-n", path], text=True, env=env)
    found = []
    for line in text.splitlines():
        parts = line.split()
        if len(parts) < 3:
            continue
        addr, kind, name = parts[0], parts[1], parts[2]
        if kind not in ("T", "t"):
            continue
        if NEEDLE not in name:
            continue
        value = int(addr, 16)
        found.append((name, value))
        if value % ALIGN != 0:
            raise ElfError(f"{name} at {value:#x} is not {ALIGN}-aligned")
    if not found:
        raise ElfError(f"{path} has no {NEEDLE} text symbol")
    for name, value in found:
        print(f"{name} {value:#x}")
    print("board_timing: unmeasured")
    return found


def _pack(fmt, *values):
    return struct.pack("<" + fmt, *values)


def synthetic_elf32():
    """A relocatable ELF32 with one SHA-256 text section and one SHA-512 section."""
    sha = b"\x00\x00\x00\x00"
    other = b"\x00\x00\x00\x00"
    names = (
        b"\0"
        b".text.sha256_update_nblocks\0"
        b".text.sha512_compress_block\0"
        b".shstrtab\0"
    )
    sha_name = 1
    other_name = names.find(b".text.sha512_compress_block")
    str_name = names.find(b".shstrtab")
    sha_off = 52
    other_off = sha_off + len(sha)
    str_off = other_off + len(other)
    shoff = str_off + len(names)
    if shoff % 4:
        shoff += 4 - (shoff % 4)
    # Pad the file so the name table sits at str_off.
    body = bytearray(shoff)
    body[sha_off : sha_off + len(sha)] = sha
    body[other_off : other_off + len(other)] = other
    body[str_off : str_off + len(names)] = names

    def shdr(name, sh_type, flags, off, size, align):
        return _pack("IIIIIIIIII", name, sh_type, flags, 0, off, size, 0, 0, align, 0)

    headers = b"".join(
        [
            shdr(0, 0, 0, 0, 0, 0),
            shdr(sha_name, SHT_PROGBITS, 2 | SHF_EXECINSTR, sha_off, len(sha), 4),
            shdr(other_name, SHT_PROGBITS, 2 | SHF_EXECINSTR, other_off, len(other), 4),
            shdr(str_name, 3, 0, str_off, len(names), 1),
        ]
    )
    ident = b"\x7fELF" + bytes([1, 1, 1]) + b"\0" * 9
    ehdr = ident + _pack("HHIIIIIHHHHHH", 1, 94, 1, 0, 0, shoff, 0, 52, 0, 0, 40, 4, 3)
    if len(ehdr) != 52:
        raise ElfError(f"ELF32 header is {len(ehdr)} bytes")
    return bytearray(ehdr + body[52:] + headers)


def ar_member(name, payload):
    field = f"{name}/".ljust(16).encode("ascii")
    if len(field) != 16:
        raise ElfError(f"archive name {name} does not fit")
    header = field + b"0".ljust(12) + b"0".ljust(6) + b"0".ljust(6)
    header += b"644".ljust(8) + str(len(payload)).encode("ascii").ljust(10) + b"`\n"
    pad = b"\n" if len(payload) % 2 else b""
    return header + payload + pad


def elf32_archive_test():
    elf = synthetic_elf32()
    archive = bytearray(b"!<arch>\n" + ar_member("sha.o", bytes(elf)))
    updated, changed, matched = align_bytes(archive)
    if changed != 1 or matched != 1:
        raise ElfError(f"ELF32 archive changed {changed} matched {matched}, want 1 and 1")
    # The SHA-512 section in the same object stays at its original alignment.
    member = updated[8 + 60 :]
    if len(member) % 2:
        member = member[:-1]
    if member[:4] != b"\x7fELF":
        # Trailing pad byte belongs to the archive, not the ELF. The member
        # size is even here (header 52 + body), so there is no pad.
        raise ElfError("ELF32 member lost its magic")
    again, changed_again, matched_again = align_bytes(updated)
    if changed_again != 0 or matched_again != 1 or bytes(again) != bytes(updated):
        raise ElfError("second ELF32 align was not a no-op")
    # SHA-256 alignment is 8192; SHA-512 alignment is still 4.
    sha_align = struct.unpack_from("<I", again, _elf32_align_offset(again, 1))[0]
    other_align = struct.unpack_from("<I", again, _elf32_align_offset(again, 2))[0]
    if sha_align != ALIGN or other_align != 4:
        raise ElfError(f"ELF32 alignments sha={sha_align} other={other_align}")


def _elf32_align_offset(archive, section_index):
    """Byte offset of sh_addralign for a known synthetic archive member."""
    # Archive magic + ar header, then the ELF. Section headers follow e_shoff.
    elf_at = 8 + 60
    (shoff,) = struct.unpack_from("<I", archive, elf_at + 32)
    return elf_at + shoff + section_index * 40 + 32


def gcc_link_test():
    work = tempfile.mkdtemp(prefix="sha256-align-")
    try:
        sha_c = os.path.join(work, "sha.c")
        pad_c = os.path.join(work, "pad.c")
        harness_c = os.path.join(work, "harness.c")
        with open(sha_c, "w", encoding="utf-8") as handle:
            handle.write(
                '__attribute__((section(".text.sha256_update_nblocks"), used))\n'
                "void sha256_update_nblocks(void) { __asm__ volatile(\"nop\"); }\n"
                '__attribute__((section(".text.sha512_compress_block"), used))\n'
                "void sha512_compress_block(void) { __asm__ volatile(\"nop\"); }\n"
            )
        with open(pad_c, "w", encoding="utf-8") as handle:
            handle.write(
                '__attribute__((section(".text.pad"), used))\n'
                "void padfn(void) { __asm__ volatile(\"nop; nop; nop; nop\"); }\n"
            )
        with open(harness_c, "w", encoding="utf-8") as handle:
            handle.write(
                "void sha256_update_nblocks(void);\n"
                "void harness(void) { sha256_update_nblocks(); }\n"
            )
        for src, obj in (
            (sha_c, "sha.o"),
            (pad_c, "pad.o"),
            (harness_c, "harness.o"),
        ):
            subprocess.check_call(
                ["gcc", "-c", "-O2", "-fno-asynchronous-unwind-tables", "-o", os.path.join(work, obj), src]
            )
        plain = os.path.join(work, "sha-plain.o")
        subprocess.check_call(["cp", os.path.join(work, "sha.o"), plain])
        before = section_align(os.path.join(work, "sha.o"), ".text.sha512_compress_block")
        align_file(os.path.join(work, "sha.o"))
        if section_align(os.path.join(work, "sha.o"), ".text.sha256_update_nblocks") != ALIGN:
            raise ElfError("host object SHA-256 section was not aligned")
        if section_align(os.path.join(work, "sha.o"), ".text.sha512_compress_block") != before:
            raise ElfError("host object SHA-512 section alignment changed")
        digest = hashlib.sha256(open(os.path.join(work, "sha.o"), "rb").read()).digest()
        if align_file(os.path.join(work, "sha.o")) != 0:
            raise ElfError("second host align changed a section")
        if hashlib.sha256(open(os.path.join(work, "sha.o"), "rb").read()).digest() != digest:
            raise ElfError("second host align rewrote the object")

        script = os.path.join(work, "link.ld")
        with open(script, "w", encoding="utf-8") as handle:
            handle.write(
                "SECTIONS { .text : { *harness.o(.text .text.*) *(.text .text.*) } }\n"
            )

        def link(sha_obj, with_pad, dest):
            objs = [os.path.join(work, "harness.o")]
            if with_pad:
                objs.append(os.path.join(work, "pad.o"))
            objs.append(sha_obj)
            subprocess.check_call(["ld", "-e", "harness", "-T", script, "-o", dest, *objs])

        def sym(path, name):
            text = subprocess.check_output(["nm", "-n", path], text=True, env={**os.environ, "LC_ALL": "C"})
            for line in text.splitlines():
                parts = line.split()
                if len(parts) >= 3 and parts[2] == name and parts[1] in ("T", "t"):
                    return int(parts[0], 16)
            raise ElfError(f"{path} has no {name}")

        un_plain = os.path.join(work, "un-plain")
        un_pad = os.path.join(work, "un-pad")
        al_plain = os.path.join(work, "al-plain")
        al_pad = os.path.join(work, "al-pad")
        link(plain, False, un_plain)
        link(plain, True, un_pad)
        link(os.path.join(work, "sha.o"), False, al_plain)
        link(os.path.join(work, "sha.o"), True, al_pad)
        moved = sym(un_pad, "sha256_update_nblocks") - sym(un_plain, "sha256_update_nblocks")
        if moved % ALIGN == 0:
            raise ElfError(f"unaligned SHA-256 moved by {moved:#x}, a multiple of {ALIGN}")
        for path in (al_plain, al_pad):
            check_elf(path, "nm")
        if sym(al_plain, "harness") != sym(al_pad, "harness"):
            raise ElfError("padding moved the harness")
        delta = sym(al_pad, "sha256_update_nblocks") - sym(al_plain, "sha256_update_nblocks")
        if delta % ALIGN != 0:
            raise ElfError(f"aligned SHA-256 moved by {delta:#x}")
    finally:
        subprocess.call(["rm", "-rf", work])


def self_test():
    elf32_archive_test()
    gcc_link_test()
    print("esp32s3-sha256-align: self-test ok")
    print("board_timing: unmeasured")


def main(argv):
    if len(argv) == 2 and argv[1] == "self-test":
        self_test()
        return 0
    if len(argv) == 3 and argv[1] == "align":
        try:
            align_file(argv[2])
        except (ElfError, OSError, ValueError) as err:
            print(f"esp32s3-sha256-align: {err}", file=sys.stderr)
            return 1
        return 0
    if len(argv) == 4 and argv[1] == "check-elf":
        try:
            check_elf(argv[2], argv[3])
        except (ElfError, OSError, ValueError, subprocess.CalledProcessError) as err:
            print(f"esp32s3-sha256-align: {err}", file=sys.stderr)
            return 1
        return 0
    print(
        "usage: esp32s3-sha256-align.py align FILE | self-test | check-elf ELF NM",
        file=sys.stderr,
    )
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
