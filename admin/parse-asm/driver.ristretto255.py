from driver import (
    Architecture_aarch64,
    Architecture_amd64,
    RustDriver,
    generated,
)
from parse import parse_file

# The field and point routines ristretto255 builds on, beyond those
# driver.ed25519.py imports.

FE = "&[u64; 4]"
FE_MUT = "&mut [u64; 4]"

# name: (arguments, whether s2n-bignum has an `_alt` form, which x86_64 runs
# without BMI2 and ADX and aarch64 runs always, as for Ed25519)
ROUTINES = {
    # Returns the Legendre symbol, -1 as `u64::MAX`.
    "bignum_invsqrt_p25519": ([("z", FE_MUT), ("x", FE)], True),
    "bignum_add_p25519": ([("z", FE_MUT), ("x", FE), ("y", FE)], False),
    "bignum_sub_p25519": ([("z", FE_MUT), ("x", FE), ("y", FE)], False),
    "bignum_mul_p25519": ([("z", FE_MUT), ("x", FE), ("y", FE)], True),
    "bignum_sqr_p25519": ([("z", FE_MUT), ("x", FE)], True),
    "edwards25519_epadd": (
        [("p3", "&mut [u64; 16]"), ("p1", "&[u64; 16]"), ("p2", "&[u64; 16]")],
        True,
    ),
    "edwards25519_epdouble": ([("p3", "&mut [u64; 16]"), ("p1", "&[u64; 12]")], True),
    "edwards25519_pdouble": ([("p3", "&mut [u64; 12]"), ("p1", "&[u64; 12]")], True),
}

# driver.ed25519.py already imports this one.
X86_ALT_ELSEWHERE = {"bignum_mul_p25519"}


def emit(arch, source, symbol, rust_name, args, output_path):
    parameter_map = [
        ("inout", f"{name}.as_{'mut_' if ty.startswith('&mut') else ''}ptr() => _")
        for name, ty in args
    ]
    decl = f"fn {rust_name}(" + ", ".join(f"{name}: {ty}" for name, ty in args) + ")"
    extra = {}
    if rust_name.startswith("bignum_invsqrt_p25519"):
        # The result comes back in the first argument's register on aarch64.
        if arch is Architecture_aarch64:
            parameter_map[0] = ("inout", "z.as_mut_ptr() => ret")
        else:
            extra["return_map"] = ("out", "ret")
        extra["return_value"] = ("u64", "ret", "ret")
        extra["hoist"] = ["proc", f"L{symbol}_nsqr_p25519", "ret"]
        decl += " -> u64"

    with (
        open(source) as input,
        generated(output_path) as output,
    ):
        d = RustDriver(output, arch)
        d.emit_rust_function(symbol, parameter_map=parameter_map, rust_decl=decl, **extra)
        parse_file(input, d)


if __name__ == "__main__":
    s2n = "../../thirdparty/s2n-bignum"
    low = "../../rind/src/low"

    for name, (args, has_alt) in ROUTINES.items():
        x86 = [name]
        if has_alt and name not in X86_ALT_ELSEWHERE:
            x86.append(name + "_alt")
        for symbol in x86:
            emit(
                Architecture_amd64,
                f"{s2n}/x86/curve25519/{symbol}.S",
                symbol,
                symbol,
                args,
                f"{low}/x86_64/{symbol}.rs",
            )

        symbol = name + "_alt" if has_alt else name
        emit(
            Architecture_aarch64,
            f"{s2n}/arm/curve25519/{symbol}.S",
            symbol,
            name,
            args,
            f"{low}/aarch64/{name}.rs",
        )
