from driver import (
    Architecture_aarch64,
    Architecture_amd64,
    RustDriver,
    generated,
)
from parse import parse_file

if __name__ == "__main__":
    with (
        open("../../thirdparty/s2n-bignum/x86/p256/bignum_montsqr_p256.S") as input,
        generated("../../rind/src/low/x86_64/bignum_montsqr_p256.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_montsqr_p256",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
            ],
            rust_decl="fn bignum_montsqr_p256(z: &mut [u64; 4], x: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/bignum_montsqr_p256_alt.S") as input,
        generated("../../rind/src/low/x86_64/bignum_montsqr_p256_alt.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_montsqr_p256_alt",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
            ],
            rust_decl="fn bignum_montsqr_p256_alt(z: &mut [u64; 4], x: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/bignum_montmul_p256.S") as input,
        generated("../../rind/src/low/x86_64/bignum_montmul_p256.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_montmul_p256",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
                ("inout", "y.as_ptr() => _"),
            ],
            rust_decl="fn bignum_montmul_p256(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/bignum_montmul_p256_alt.S") as input,
        generated("../../rind/src/low/x86_64/bignum_montmul_p256_alt.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_montmul_p256_alt",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
                ("inout", "y.as_ptr() => _"),
            ],
            rust_decl="fn bignum_montmul_p256_alt(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/bignum_add_p256.S") as input,
        generated("../../rind/src/low/x86_64/bignum_add_p256.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_add_p256",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
                ("inout", "y.as_ptr() => _"),
            ],
            rust_decl="fn bignum_add_p256(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/bignum_demont_p256.S") as input,
        generated("../../rind/src/low/x86_64/bignum_demont_p256.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_demont_p256",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
            ],
            rust_decl="fn bignum_demont_p256(z: &mut [u64; 4], x: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/bignum_demont_p256_alt.S") as input,
        generated("../../rind/src/low/x86_64/bignum_demont_p256_alt.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_demont_p256_alt",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
            ],
            rust_decl="fn bignum_demont_p256_alt(z: &mut [u64; 4], x: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/bignum_tomont_p256.S") as input,
        generated("../../rind/src/low/x86_64/bignum_tomont_p256.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_tomont_p256",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
            ],
            rust_decl="fn bignum_tomont_p256(z: &mut [u64; 4], x: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/bignum_tomont_p256_alt.S") as input,
        generated("../../rind/src/low/x86_64/bignum_tomont_p256_alt.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_tomont_p256_alt",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
            ],
            rust_decl="fn bignum_tomont_p256_alt(z: &mut [u64; 4], x: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/bignum_neg_p256.S") as input,
        generated("../../rind/src/low/x86_64/bignum_neg_p256.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_neg_p256",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
            ],
            rust_decl="fn bignum_neg_p256(z: &mut [u64; 4], x: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/bignum_inv_p256.S") as input,
        generated("../../rind/src/low/x86_64/bignum_inv_p256.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_inv_p256",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
            ],
            rust_decl="fn bignum_inv_p256(z: &mut [u64; 4], x: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/bignum_mod_n256_4.S") as input,
        generated("../../rind/src/low/x86_64/bignum_mod_n256.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_mod_n256_4",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
            ],
            rust_decl="fn bignum_mod_n256(z: &mut [u64; 4], x: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/generic/bignum_mux.S") as input,
        generated("../../rind/src/low/x86_64/bignum_mux.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_mux",
            parameter_map=[
                ("inout", "p => _"),
                ("inout", "z.len() => _"),
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x_if_p.as_ptr() => _"),
                ("inout", "y_if_not_p.as_ptr() => _"),
            ],
            rust_decl="fn bignum_mux(p: u64, z: &mut [u64], x_if_p: &[u64], y_if_not_p: &[u64])",
            assertions=[
                "z.len() == x_if_p.len()",
                "z.len() == y_if_not_p.len()",
            ],
        )
        parse_file(input, d)

    with (
        open(
            "../../thirdparty/s2n-bignum/x86/generic/bignum_copy_row_from_table.S"
        ) as input,
        generated("../../rind/src/low/x86_64/bignum_copy_row_from_table.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_copy_row_from_table",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "table.as_ptr() => _"),
                ("inout", "height => _"),
                ("inout", "width => _"),
                ("inout", "index => _"),
            ],
            rust_decl="fn bignum_copy_row_from_table(z: &mut [u64], table: &[u64], height: u64, width: u64, index: u64)",
            assertions=[
                "z.len() as u64 == width",
                "height.checked_mul(width) == Some(table.len() as u64)",
            ],
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/generic/bignum_modadd.S") as input,
        generated("../../rind/src/low/x86_64/bignum_modadd.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_modadd",
            parameter_map=[
                ("inout", "m.len() => _"),
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
                ("inout", "y.as_ptr() => _"),
                ("inout", "m.as_ptr() => _"),
            ],
            rust_decl="fn bignum_modadd(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64])",
            assertions=[
                "z.len() == x.len()",
                "z.len() == y.len()",
                "z.len() == m.len()",
            ],
            # `PosInt::reduce_even` calls it once or twice per bit.
            allow_inline=True,
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/generic/bignum_modinv.S") as input,
        generated("../../rind/src/low/x86_64/bignum_modinv.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_modinv",
            parameter_map=[
                ("inout", "b.len() => _"),
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "a.as_ptr() => _"),
                ("inout", "b.as_ptr() => _"),
                ("inout", "t.as_mut_ptr() => _"),
            ],
            rust_decl="fn bignum_modinv(z: &mut [u64], a: &[u64], b: &[u64], t: &mut [u64])",
            assertions=[
                "z.len() == a.len()",
                "z.len() == b.len()",
                "z.len() * 3 <= t.len()",
            ],
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/generic/bignum_montmul.S") as input,
        generated("../../rind/src/low/x86_64/bignum_montmul.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_montmul",
            parameter_map=[
                ("inout", "m.len() => _"),
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
                ("inout", "y.as_ptr() => _"),
                ("inout", "m.as_ptr() => _"),
            ],
            rust_decl="fn bignum_montmul(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64])",
            assertions=[
                "z.len() == x.len()",
                "z.len() == y.len()",
                "z.len() == m.len()",
            ],
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/generic/bignum_demont.S") as input,
        generated("../../rind/src/low/x86_64/bignum_demont.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_demont",
            parameter_map=[
                ("inout", "m.len() => _"),
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
                ("inout", "m.as_ptr() => _"),
            ],
            rust_decl="fn bignum_demont(z: &mut [u64], x: &[u64], m: &[u64])",
            assertions=[
                "z.len() == x.len()",
                "z.len() == m.len()",
            ],
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/generic/bignum_montifier.S") as input,
        generated("../../rind/src/low/x86_64/bignum_montifier.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_montifier",
            parameter_map=[
                ("inout", "m.len() => _"),
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "m.as_ptr() => _"),
                ("inout", "t.as_mut_ptr() => _"),
            ],
            rust_decl="fn bignum_montifier(z: &mut [u64], m: &[u64], t: &mut [u64])",
            assertions=[
                "z.len() == m.len()",
                "z.len() <= t.len()",
            ],
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/p256_montjadd.S") as input,
        generated("../../rind/src/low/x86_64/p256_montjadd.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "p256_montjadd",
            parameter_map=[
                ("inout", "p3.as_mut_ptr() => _"),
                ("inout", "p1.as_ptr() => _"),
                ("inout", "p2.as_ptr() => _"),
            ],
            rust_decl="fn p256_montjadd(p3: &mut [u64; 12], p1: &[u64; 12], p2: &[u64; 12])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/p256_montjadd_alt.S") as input,
        generated("../../rind/src/low/x86_64/p256_montjadd_alt.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "p256_montjadd_alt",
            parameter_map=[
                ("inout", "p3.as_mut_ptr() => _"),
                ("inout", "p1.as_ptr() => _"),
                ("inout", "p2.as_ptr() => _"),
            ],
            rust_decl="fn p256_montjadd_alt(p3: &mut [u64; 12], p1: &[u64; 12], p2: &[u64; 12])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/p256_montjmixadd.S") as input,
        generated("../../rind/src/low/x86_64/p256_montjmixadd.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "p256_montjmixadd",
            parameter_map=[
                ("inout", "p3.as_mut_ptr() => _"),
                ("inout", "p1.as_ptr() => _"),
                ("inout", "p2.as_ptr() => _"),
            ],
            rust_decl="fn p256_montjmixadd(p3: &mut [u64; 12], p1: &[u64; 12], p2: &[u64; 8])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/p256_montjmixadd_alt.S") as input,
        generated("../../rind/src/low/x86_64/p256_montjmixadd_alt.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "p256_montjmixadd_alt",
            parameter_map=[
                ("inout", "p3.as_mut_ptr() => _"),
                ("inout", "p1.as_ptr() => _"),
                ("inout", "p2.as_ptr() => _"),
            ],
            rust_decl="fn p256_montjmixadd_alt(p3: &mut [u64; 12], p1: &[u64; 12], p2: &[u64; 8])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/p256_montjdouble.S") as input,
        generated("../../rind/src/low/x86_64/p256_montjdouble.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "p256_montjdouble",
            parameter_map=[
                ("inout", "p3.as_mut_ptr() => _"),
                ("inout", "p1.as_ptr() => _"),
            ],
            rust_decl="fn p256_montjdouble(p3: &mut [u64; 12], p1: &[u64; 12])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/p256_montjdouble_alt.S") as input,
        generated("../../rind/src/low/x86_64/p256_montjdouble_alt.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "p256_montjdouble_alt",
            parameter_map=[
                ("inout", "p3.as_mut_ptr() => _"),
                ("inout", "p1.as_ptr() => _"),
            ],
            rust_decl="fn p256_montjdouble_alt(p3: &mut [u64; 12], p1: &[u64; 12])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/generic/bignum_eq.S") as input,
        generated("../../rind/src/low/x86_64/bignum_eq.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "bignum_eq",
            return_value=("u64", "ret", "ret > 0"),
            parameter_map=[
                ("inout", "x.len() => _"),
                ("inout", "x.as_ptr() => _"),
                ("inout", "y.len() => _"),
                ("inout", "y.as_ptr() => _"),
            ],
            return_map=("out", "ret"),
            rust_decl="fn bignum_eq(x: &[u64], y: &[u64]) -> bool",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/p256_scalarmul.S") as input,
        generated("../../rind/src/low/x86_64/p256_scalarmul.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "p256_scalarmul",
            parameter_map=[
                ("inout", "res.as_mut_ptr() => _"),
                ("inout", "scalar.as_ptr() => _"),
                ("inout", "point.as_ptr() => _"),
            ],
            hoist=["proc", "Lp256_scalarmul_local_p256_montjmixadd", "ret"],
            rust_decl="fn p256_scalarmul(res: &mut [u64; 8], scalar: &[u64; 4], point: &[u64; 8])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/x86/p256/p256_scalarmul_alt.S") as input,
        generated("../../rind/src/low/x86_64/p256_scalarmul_alt.rs") as output,
    ):
        d = RustDriver(output, Architecture_amd64)
        d.emit_rust_function(
            "p256_scalarmul_alt",
            parameter_map=[
                ("inout", "res.as_mut_ptr() => _"),
                ("inout", "scalar.as_ptr() => _"),
                ("inout", "point.as_ptr() => _"),
            ],
            hoist=["proc", "Lp256_scalarmul_alt_local_p256_montjmixadd", "ret"],
            rust_decl="fn p256_scalarmul_alt(res: &mut [u64; 8], scalar: &[u64; 4], point: &[u64; 8])",
        )
        parse_file(input, d)

    # aarch64
    with (
        open("../../thirdparty/s2n-bignum/arm/p256/bignum_montsqr_p256_alt.S") as input,
        generated("../../rind/src/low/aarch64/bignum_montsqr_p256.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_montsqr_p256_alt",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
            ],
            rust_decl="fn bignum_montsqr_p256(z: &mut [u64; 4], x: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/p256/bignum_montmul_p256_alt.S") as input,
        generated("../../rind/src/low/aarch64/bignum_montmul_p256.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_montmul_p256_alt",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
                ("inout", "y.as_ptr() => _"),
            ],
            rust_decl="fn bignum_montmul_p256(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/p256/bignum_add_p256.S") as input,
        generated("../../rind/src/low/aarch64/bignum_add_p256.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_add_p256",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
                ("inout", "y.as_ptr() => _"),
            ],
            rust_decl="fn bignum_add_p256(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/p256/bignum_demont_p256.S") as input,
        generated("../../rind/src/low/aarch64/bignum_demont_p256.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_demont_p256",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
            ],
            rust_decl="fn bignum_demont_p256(z: &mut [u64; 4], x: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/p256/bignum_tomont_p256.S") as input,
        generated("../../rind/src/low/aarch64/bignum_tomont_p256.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_tomont_p256",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
            ],
            rust_decl="fn bignum_tomont_p256(z: &mut [u64; 4], x: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/p256/bignum_neg_p256.S") as input,
        generated("../../rind/src/low/aarch64/bignum_neg_p256.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_neg_p256",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
            ],
            rust_decl="fn bignum_neg_p256(z: &mut [u64; 4], x: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/p256/bignum_inv_p256.S") as input,
        generated("../../rind/src/low/aarch64/bignum_inv_p256.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_inv_p256",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
            ],
            rust_decl="fn bignum_inv_p256(z: &mut [u64; 4], x: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/p256/bignum_mod_n256_4.S") as input,
        generated("../../rind/src/low/aarch64/bignum_mod_n256.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_mod_n256_4",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
            ],
            rust_decl="fn bignum_mod_n256(z: &mut [u64; 4], x: &[u64; 4])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/generic/bignum_mux.S") as input,
        generated("../../rind/src/low/aarch64/bignum_mux.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_mux",
            parameter_map=[
                ("inout", "p => _"),
                ("inout", "z.len() => _"),
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x_if_p.as_ptr() => _"),
                ("inout", "y_if_not_p.as_ptr() => _"),
            ],
            rust_decl="fn bignum_mux(p: u64, z: &mut [u64], x_if_p: &[u64], y_if_not_p: &[u64])",
            assertions=[
                "z.len() == x_if_p.len()",
                "z.len() == y_if_not_p.len()",
            ],
        )
        parse_file(input, d)

    with (
        open(
            "../../thirdparty/s2n-bignum/arm/generic/bignum_copy_row_from_table.S"
        ) as input,
        generated("../../rind/src/low/aarch64/bignum_copy_row_from_table.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_copy_row_from_table",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "table.as_ptr() => _"),
                ("inout", "height => _"),
                ("inout", "width => _"),
                ("inout", "index => _"),
            ],
            rust_decl="fn bignum_copy_row_from_table(z: &mut [u64], table: &[u64], height: u64, width: u64, index: u64)",
            assertions=[
                "z.len() as u64 == width",
                "height.checked_mul(width) == Some(table.len() as u64)",
            ],
        )
        parse_file(input, d)

    with (
        open(
            "../../thirdparty/s2n-bignum/arm/generic/bignum_copy_row_from_table_8n.S"
        ) as input,
        generated(
            "../../rind/src/low/aarch64/bignum_copy_row_from_table_8n.rs"
        ) as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_copy_row_from_table_8n",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "table.as_ptr() => _"),
                ("inout", "height => _"),
                ("inout", "width => _"),
                ("inout", "index => _"),
            ],
            rust_decl="fn bignum_copy_row_from_table_8n(z: &mut [u64], table: &[u64], height: u64, width: u64, index: u64)",
            assertions=[
                "z.len() as u64 == width",
                "height.checked_mul(width) == Some(table.len() as u64)",
                "width.is_multiple_of(8)",
            ],
        )
        parse_file(input, d)

    with (
        open(
            "../../thirdparty/s2n-bignum/arm/generic/bignum_copy_row_from_table_16.S"
        ) as input,
        generated(
            "../../rind/src/low/aarch64/bignum_copy_row_from_table_16.rs"
        ) as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_copy_row_from_table_16",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "table.as_ptr() => _"),
                ("inout", "height => _"),
                ("inout", "index => _"),
            ],
            rust_decl="fn bignum_copy_row_from_table_16(z: &mut [u64], table: &[u64], height: u64, index: u64)",
            assertions=[
                "z.len() == 16",
                "height.checked_mul(16) == Some(table.len() as u64)",
            ],
        )
        parse_file(input, d)

    with (
        open(
            "../../thirdparty/s2n-bignum/arm/generic/bignum_copy_row_from_table_32.S"
        ) as input,
        generated(
            "../../rind/src/low/aarch64/bignum_copy_row_from_table_32.rs"
        ) as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_copy_row_from_table_32",
            parameter_map=[
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "table.as_ptr() => _"),
                ("inout", "height => _"),
                ("inout", "index => _"),
            ],
            rust_decl="fn bignum_copy_row_from_table_32(z: &mut [u64], table: &[u64], height: u64, index: u64)",
            assertions=[
                "z.len() == 32",
                "height.checked_mul(32) == Some(table.len() as u64)",
            ],
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/p256/p256_montjadd_alt.S") as input,
        generated("../../rind/src/low/aarch64/p256_montjadd.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "p256_montjadd_alt",
            parameter_map=[
                ("inout", "p3.as_mut_ptr() => _"),
                ("inout", "p1.as_ptr() => _"),
                ("inout", "p2.as_ptr() => _"),
            ],
            rust_decl="fn p256_montjadd(p3: &mut [u64; 12], p1: &[u64; 12], p2: &[u64; 12])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/p256/p256_montjmixadd_alt.S") as input,
        generated("../../rind/src/low/aarch64/p256_montjmixadd.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "p256_montjmixadd_alt",
            parameter_map=[
                ("inout", "p3.as_mut_ptr() => _"),
                ("inout", "p1.as_ptr() => _"),
                ("inout", "p2.as_ptr() => _"),
            ],
            rust_decl="fn p256_montjmixadd(p3: &mut [u64; 12], p1: &[u64; 12], p2: &[u64; 8])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/p256/p256_montjdouble_alt.S") as input,
        generated("../../rind/src/low/aarch64/p256_montjdouble.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "p256_montjdouble_alt",
            parameter_map=[
                ("inout", "p3.as_mut_ptr() => _"),
                ("inout", "p1.as_ptr() => _"),
            ],
            rust_decl="fn p256_montjdouble(p3: &mut [u64; 12], p1: &[u64; 12])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/generic/bignum_eq.S") as input,
        generated("../../rind/src/low/aarch64/bignum_eq.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_eq",
            return_value=("u64", "ret", "ret > 0"),
            parameter_map=[
                ("inout", "x.len() => ret"),
                ("inout", "x.as_ptr() => _"),
                ("inout", "y.len() => _"),
                ("inout", "y.as_ptr() => _"),
            ],
            rust_decl="fn bignum_eq(x: &[u64], y: &[u64]) -> bool",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/generic/bignum_modadd.S") as input,
        generated("../../rind/src/low/aarch64/bignum_modadd.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_modadd",
            parameter_map=[
                ("inout", "m.len() => _"),
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
                ("inout", "y.as_ptr() => _"),
                ("inout", "m.as_ptr() => _"),
            ],
            rust_decl="fn bignum_modadd(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64])",
            assertions=[
                "z.len() == x.len()",
                "z.len() == y.len()",
                "z.len() == m.len()",
            ],
            # `PosInt::reduce_even` calls it once or twice per bit.
            allow_inline=True,
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/generic/bignum_modinv.S") as input,
        generated("../../rind/src/low/aarch64/bignum_modinv.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_modinv",
            parameter_map=[
                ("inout", "b.len() => _"),
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "a.as_ptr() => _"),
                ("inout", "b.as_ptr() => _"),
                ("inout", "t.as_mut_ptr() => _"),
            ],
            rust_decl="fn bignum_modinv(z: &mut [u64], a: &[u64], b: &[u64], t: &mut [u64])",
            assertions=[
                "z.len() == a.len()",
                "z.len() == b.len()",
                "z.len() * 3 <= t.len()",
            ],
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/generic/bignum_montmul.S") as input,
        generated("../../rind/src/low/aarch64/bignum_montmul.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_montmul",
            parameter_map=[
                ("inout", "m.len() => _"),
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
                ("inout", "y.as_ptr() => _"),
                ("inout", "m.as_ptr() => _"),
            ],
            rust_decl="fn bignum_montmul(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64])",
            assertions=[
                "z.len() == x.len()",
                "z.len() == y.len()",
                "z.len() == m.len()",
            ],
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/generic/bignum_demont.S") as input,
        generated("../../rind/src/low/aarch64/bignum_demont.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_demont",
            parameter_map=[
                ("inout", "m.len() => _"),
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "x.as_ptr() => _"),
                ("inout", "m.as_ptr() => _"),
            ],
            rust_decl="fn bignum_demont(z: &mut [u64], x: &[u64], m: &[u64])",
            assertions=[
                "z.len() == x.len()",
                "z.len() == m.len()",
            ],
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/generic/bignum_montifier.S") as input,
        generated("../../rind/src/low/aarch64/bignum_montifier.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "bignum_montifier",
            parameter_map=[
                ("inout", "m.len() => _"),
                ("inout", "z.as_mut_ptr() => _"),
                ("inout", "m.as_ptr() => _"),
                ("inout", "t.as_mut_ptr() => _"),
            ],
            rust_decl="fn bignum_montifier(z: &mut [u64], m: &[u64], t: &mut [u64])",
            assertions=[
                "z.len() == m.len()",
                "z.len() <= t.len()",
            ],
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/p256/p256_scalarmul_alt.S") as input,
        generated("../../rind/src/low/aarch64/p256_scalarmul.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "p256_scalarmul_alt",
            parameter_map=[
                ("inout", "res.as_mut_ptr() => _"),
                ("inout", "scalar.as_ptr() => _"),
                ("inout", "point.as_ptr() => _"),
            ],
            hoist=["proc", "Lp256_scalarmul_alt_local_p256_montjmixadd", "ret"],
            rust_decl="fn p256_scalarmul(res: &mut [u64; 8], scalar: &[u64; 4], point: &[u64; 8])",
        )
        parse_file(input, d)

    with (
        open("../../thirdparty/s2n-bignum/arm/p256/p256_scalarmulbase_alt.S") as input,
        generated("../../rind/src/low/aarch64/p256_scalarmulbase.rs") as output,
    ):
        d = RustDriver(output, Architecture_aarch64)
        d.emit_rust_function(
            "p256_scalarmulbase_alt",
            parameter_map=[
                ("inout", "res.as_mut_ptr() => _"),
                ("inout", "scalar.as_ptr() => _"),
                ("inout", "6u64 => _"),
                ("inout", "table.as_ptr() => _"),
            ],
            hoist=["proc", "Lp256_scalarmulbase_alt_local_p256_montjmixadd", "ret"],
            rust_decl="fn p256_scalarmulbase(res: &mut [u64; 8], scalar: &[u64; 4], table: &[[u64; 256]; 43])",
        )
        parse_file(input, d)
