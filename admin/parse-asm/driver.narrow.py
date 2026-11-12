"""The aarch64 schedules for cores whose high multiply is narrow.

s2n-bignum's `_alt` routines, which the other drivers import for aarch64,
are scheduled for cores that issue `umulh` widely. These are the twins
without that suffix. `low/aarch64/wide_mux.rs` picks at run time.
"""

import io
import os
import re

from driver import Architecture_aarch64, RustDriver, generated
from parse import parse_file

LOW = "../../rind/src/low/aarch64"
S2N = "../../thirdparty/s2n-bignum"
FN = re.compile(
    r"pub\(crate\) fn (\w+)\((.*?)\)(?: -> ([\w:]+))?\s*\{",
    re.S,
)
INOUT = re.compile(r'^\s+inout\("([^"]+)"\) (.+),$', re.M)
SOURCE = re.compile(r"Transliterated from s2n-bignum's (arm/\S+)\.S")
CONSTANT = re.compile(r"S2N_BN_SYMBOL\((\w+_constant)\)")


def proof_asserts_object(source):
    """The HOL Light file lists this object with `define_assert_from_elf`.

    Some SLOTHY routines are proven by equivalence from an asserted base
    program (`define_from_elf` of the tuned object). `admin/prove-bytes`
    checks a routine only when the proof embeds that object's bytes, so
    those stay on the `_alt` import.
    """
    path = os.path.join(S2N, "arm/proofs", os.path.basename(source) + ".ml")
    if not os.path.exists(path):
        return False
    text = open(path).read()
    obj = re.escape(f'"{source}.o"')
    return (
        re.search(
            r"define_assert(_relocs)?_from_elf\b(?:(?!;;).)*?" + obj,
            text,
            re.S,
        )
        is not None
    )
LOCAL_FN = re.compile(r"S2N_BN_FUNCTION_TYPE_DIRECTIVE\((L\w+)\)")


def hoist_label(text):
    """The last local subroutine, when one follows the routine's own return.

    The importer hoists those subroutines above that return. The label is the
    subroutine's entry: the next `ret` is its end, which is how the alt
    drivers name the same shape.
    """
    lines = text.splitlines()
    first_ret = next(
        (i for i, line in enumerate(lines) if re.search(r"\bCFI_RET\b", line)),
        None,
    )
    if first_ret is None:
        return None
    after = []
    for label in LOCAL_FN.findall(text):
        for i, line in enumerate(lines):
            if line.strip().startswith(label + ":"):
                if i > first_ret:
                    after.append(label)
                break
    return after[-1] if after else None


def signatures():
    """Each alt routine the other drivers imported, and how to import its twin."""
    found = []
    for name in sorted(os.listdir(LOW)):
        if not name.endswith(".rs"):
            continue
        text = open(os.path.join(LOW, name)).read()
        source = SOURCE.search(text)
        if not source or "_alt" not in source.group(1):
            continue
        path = source.group(1)
        if path.startswith("arm/aes_gcm/") or path.startswith("arm/sha3/"):
            continue
        fn = FN.search(text)
        assert fn, name
        args = fn.group(2).strip()
        ret = fn.group(3)
        params = [(reg, expr.strip()) for reg, expr in INOUT.findall(text)]
        # Operand order is the ABI's. A later `inout` is a clobber only if
        # the driver emitted none; these files' parameters are the `inout`s.
        assert params and params[0][0] == "x0", (name, params[:4])
        narrow = path.replace("_alt", "")
        if not proof_asserts_object(narrow):
            print("SKIP no embedded proof bytes", narrow)
            continue
        body = open(os.path.join(S2N, narrow + ".S")).read()
        found.append(
            dict(
                fn=fn.group(1),
                args=args,
                ret=ret,
                params=[expr for _, expr in params],
                source=narrow,
                hoist=hoist_label(body),
                constants=sorted(set(CONSTANT.findall(body))),
            )
        )
    return found


def emit_one(spec):
    symbol = spec["fn"]
    decl = f"fn {symbol}({spec['args']})"
    extra = {}
    if spec["ret"]:
        decl += f" -> {spec['ret']}"
        expr = "ret == 0" if spec["ret"] == "bool" else "ret"
        extra["return_value"] = ("u64", "ret", expr)
    if spec["hoist"]:
        extra["hoist"] = ["proc", spec["hoist"], "ret"]
    out = os.path.join(LOW, spec["fn"] + "_narrow.rs")
    with (
        open(os.path.join(S2N, spec["source"] + ".S")) as input,
        generated(out) as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        for constant in spec["constants"]:
            d.add_const_symbol(constant)
        d.emit_rust_function(
            symbol,
            parameter_map=[("inout", expr) for expr in spec["params"]],
            rust_decl=decl,
            **extra,
        )
        parse_file(input, d)


def expand_register_aliases(path):
    """Expand object-like `#define`/`#undef` pairs before the importer sees them.

    `bignum_emontredc_8n.S` rebinds names such as `in1` to different vector
    registers through the routine. A Rust `macro_rules` cannot be replaced
    that way, so the names are substituted here and the directives dropped.
    """
    aliases = {}
    out = []
    ident = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*\b")
    for line in open(path):
        stripped = line.lstrip()
        if stripped.startswith("#define "):
            parts = stripped.split()
            if len(parts) == 3 and re.fullmatch(r"[A-Za-z_]\w*", parts[1]):
                aliases[parts[1]] = parts[2]
                continue
        if stripped.startswith("#undef "):
            aliases.pop(stripped.split()[1], None)
            continue
        if aliases:
            line = ident.sub(lambda m: aliases.get(m.group(0), m.group(0)), line)
        out.append(line)
    buf = io.StringIO("".join(out))
    buf.name = path
    return buf


def emit_fastmul():
    """Karatsuba multiplication for RSA on a narrow core, as on x86_64."""
    extras = {
        "bignum_kmul_16_32": ["proc", "Lbignum_kmul_16_32_local_mul_8_16", "ret"],
        "bignum_kmul_32_64": ["proc", "Lbignum_kmul_32_64_local_mul_8_16", "ret"],
        "bignum_ksqr_16_32": ["proc", "Lbignum_ksqr_16_32_local_sqr_8_16", "ret"],
        "bignum_ksqr_32_64": ["proc", "Lbignum_ksqr_32_64_local_sqr_8_16", "ret"],
    }
    specs = [
        (
            "bignum_kmul_16_32",
            "fn bignum_kmul_16_32(z: &mut [u64], x: &[u64], y: &[u64], t: &mut [u64; 32])",
            [
                "z.as_mut_ptr() => _",
                "x.as_ptr() => _",
                "y.as_ptr() => _",
                "t.as_mut_ptr() => _",
            ],
            ["z.len() == 32", "x.len() == 16", "y.len() == 16"],
        ),
        (
            "bignum_kmul_32_64",
            "fn bignum_kmul_32_64(z: &mut [u64], x: &[u64], y: &[u64], t: &mut [u64; 96])",
            [
                "z.as_mut_ptr() => _",
                "x.as_ptr() => _",
                "y.as_ptr() => _",
                "t.as_mut_ptr() => _",
            ],
            ["z.len() == 64", "x.len() == 32", "y.len() == 32"],
        ),
        (
            "bignum_ksqr_16_32",
            "fn bignum_ksqr_16_32(z: &mut [u64], x: &[u64], t: &mut [u64; 24])",
            ["z.as_mut_ptr() => _", "x.as_ptr() => _", "t.as_mut_ptr() => _"],
            ["z.len() == 32", "x.len() == 16"],
        ),
        (
            "bignum_ksqr_32_64",
            "fn bignum_ksqr_32_64(z: &mut [u64], x: &[u64], t: &mut [u64; 72])",
            ["z.as_mut_ptr() => _", "x.as_ptr() => _", "t.as_mut_ptr() => _"],
            ["z.len() == 64", "x.len() == 32"],
        ),
    ]
    for name, decl, params, assertions in specs:
        with (
            open(f"{S2N}/arm/fastmul/{name}.S") as input,
            generated(f"{LOW}/{name}.rs") as output,
        ):
            d = RustDriver(output, Architecture_aarch64)
            d.emit_rust_function(
                name,
                parameter_map=[("inout", p) for p in params],
                rust_decl=decl,
                assertions=assertions,
                hoist=extras[name],
            )
            parse_file(input, d)

    with (
        expand_register_aliases(f"{S2N}/arm/fastmul/bignum_emontredc_8n.S") as input,
        generated(f"{LOW}/bignum_emontredc_8n.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_emontredc_8n",
            parameter_map=[
                ("inout", "m.len() => ret"),
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "m.as_ptr() => _"),
                ("inout", "w => _"),
            ],
            return_value=("u64", "ret", "ret"),
            assertions=["z.len() == m.len() * 2", "m.len().is_multiple_of(8)"],
            rust_decl="fn bignum_emontredc_8n(z: &mut [u64], m: &[u64], w: u64) -> u64",
        )
        parse_file(input, d)


def arg_names(args):
    names = []
    for part in args.split(","):
        part = part.strip()
        if not part:
            continue
        names.append(part.split(":", 1)[0].strip())
    return names


def write_mux(specs):
    lines = [
        "// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0",
        "",
        "//! Schedules s2n-bignum's elliptic-curve routines for this core's multiplier.",
        "//!",
        "//! The sibling modules without a `_narrow` suffix are s2n-bignum's `_alt`",
        "//! schedules, written for cores that issue `umulh` widely. The `_narrow`",
        "//! modules are the other schedules. Cortex-A76 retires a `umulh` once",
        "//! every four cycles, and there the narrow X25519 is the one aws-lc runs.",
        "//! Both are correct on every core. Linux selects narrow only for",
        "//! Cortex-A72, Cortex-A76, and Neoverse N1; every other core, including",
        "//! one this crate does not recognise, keeps `_alt`. `cpu::wide_multiplier`",
        "//! is the choice.",
        "",
    ]
    for spec in specs:
        names = arg_names(spec["args"])
        ret = f" -> {spec['ret']}" if spec["ret"] else ""
        call = ", ".join(names)
        lines.append("#[inline]")
        lines.append(f"pub(crate) fn {spec['fn']}({spec['args']}){ret} {{")
        lines.append("    if super::cpu::wide_multiplier() {")
        lines.append(f"        super::{spec['fn']}::{spec['fn']}({call})")
        lines.append("    } else {")
        lines.append(f"        super::{spec['fn']}_narrow::{spec['fn']}({call})")
        lines.append("    }")
        lines.append("}")
        lines.append("")
    lines.append(TEST)
    path = os.path.join(LOW, "wide_mux.rs")
    with open(path, "w") as output:
        output.write("\n".join(lines))
    import subprocess

    subprocess.check_call(["rustfmt", path])
    print("WROTE", path)


TEST = '''
#[cfg(test)]
mod tests {
    /// Both schedules agree. The cases live in `schedules`, which regeneration
    /// of this file does not overwrite.
    #[test]
    fn schedules_agree() {
        super::super::schedules::agree();
    }
}
'''


if __name__ == "__main__":
    specs = signatures()
    assert len(specs) == 21, len(specs)
    for spec in specs:
        emit_one(spec)
    emit_fastmul()
    write_mux(specs)
