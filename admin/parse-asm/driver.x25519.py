from driver import (
    Architecture_aarch64,
    Architecture_amd64,
    RustDriver,
    generated,
)
from parse import parse_file

if __name__ == "__main__":
    with (
        open("../../thirdparty/s2n-bignum/x86/curve25519/curve25519_x25519.S") as input,
        generated("../../rind/src/low/x86_64/curve25519_x25519.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "curve25519_x25519",
            parameter_map=[
                ("inout", "res.as_mut_ptr() => _"),
                ("inout", "scalar.as_ptr() => _"),
                ("inout", "point.as_ptr() => _"),
            ],
            rust_decl="fn curve25519_x25519(res: &mut [u64; 4], scalar: &[u64; 4], point: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/curve25519/curve25519_x25519_alt.S") as input,
        generated("../../rind/src/low/x86_64/curve25519_x25519_alt.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "curve25519_x25519_alt",
            parameter_map=[
                ("inout", "res.as_mut_ptr() => _"),
                ("inout", "scalar.as_ptr() => _"),
                ("inout", "point.as_ptr() => _"),
            ],
            rust_decl="fn curve25519_x25519_alt(res: &mut [u64; 4], scalar: &[u64; 4], point: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open(
            "../../thirdparty/s2n-bignum/x86/curve25519/curve25519_x25519base.S"
        ) as input,
        generated("../../rind/src/low/x86_64/curve25519_x25519base.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.add_const_symbol("curve25519_x25519base_constant", shared=True)
        d.emit_rust_function(
            "curve25519_x25519base",
            parameter_map=[
                ("inout", "res.as_mut_ptr() => _"),
                ("inout", "scalar.as_ptr() => _"),
            ],
            rust_decl="fn curve25519_x25519base(res: &mut [u64; 4], scalar: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open(
            "../../thirdparty/s2n-bignum/x86/curve25519/curve25519_x25519base_alt.S"
        ) as input,
        generated("../../rind/src/low/x86_64/curve25519_x25519base_alt.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.add_const_symbol(
            "curve25519_x25519base_alt_constant",
            same_as="super::curve25519_x25519base::curve25519_x25519base_constant",
        )
        d.emit_rust_function(
            "curve25519_x25519base_alt",
            parameter_map=[
                ("inout", "res.as_mut_ptr() => _"),
                ("inout", "scalar.as_ptr() => _"),
            ],
            rust_decl="fn curve25519_x25519base_alt(res: &mut [u64; 4], scalar: &[u64; 4])",
        )
        parse_file(input, d)

    # The `_byte` routines, unlike the word ones, have `_SAFE` theorems. Their
    # 32 little-endian bytes are a `[u64; 4]`'s memory on little-endian
    # aarch64, so the wrappers keep the word types every backend shares.
    with (
        open(
            "../../thirdparty/s2n-bignum/arm/curve25519/curve25519_x25519_byte_alt.S"
        ) as input,
        generated("../../rind/src/low/aarch64/curve25519_x25519.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "curve25519_x25519_byte_alt",
            parameter_map=[
                ("inout", "res.as_mut_ptr() => _"),
                ("inout", "scalar.as_ptr() => _"),
                ("inout", "point.as_ptr() => _"),
            ],
            rust_decl="fn curve25519_x25519(res: &mut [u64; 4], scalar: &[u64; 4], point: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open(
            "../../thirdparty/s2n-bignum/arm/curve25519/curve25519_x25519base_byte_alt.S"
        ) as input,
        generated("../../rind/src/low/aarch64/curve25519_x25519base.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.add_const_symbol("curve25519_x25519base_byte_alt_constant")
        d.emit_rust_function(
            "curve25519_x25519base_byte_alt",
            parameter_map=[
                ("inout", "res.as_mut_ptr() => _"),
                ("inout", "scalar.as_ptr() => _"),
            ],
            rust_decl="fn curve25519_x25519base(res: &mut [u64; 4], scalar: &[u64; 4])",
        )
        parse_file(input, d)
