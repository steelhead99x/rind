from driver import (
    Architecture_aarch64,
    RustDriver,
    generated,
)
from parse import assemble_and_disassemble, parse_file

if __name__ == "__main__":
    # The `_alt` kernels interleave eight blocks and need SHA3's EOR3, so they
    # take H to H^8, and return from several places.
    for bits, rounds, alt in (
        (128, 10, False),
        (128, 10, True),
        (256, 14, False),
        (256, 14, True),
    ):
        for op in ("enc", "dec"):
            name = "aes%d_gcm_%s%s" % (bits, op, "_alt" if alt else "")
            with (
                open("../../thirdparty/s2n-bignum/arm/aes_gcm/%s.S" % name) as input,
                generated("../../rind/src/low/aarch64/%s.rs" % name) as output,
            ):
                d = RustDriver(output, Architecture_aarch64)
                d.emit_rust_function(
                    name,
                    parameter_map=[
                        ("inout", "inout => _"),
                        ("inout", "blocks * 128 => _"),
                        ("inout", "inout => _"),
                        ("inout", "tag.as_mut_ptr() => _"),
                        ("inout", "ivec.as_mut_ptr() => _"),
                        ("inout", "key.as_ptr() => _"),
                        ("inout", "htable.as_ptr() => _"),
                    ],
                    func_attrs='#[target_feature(enable = "%s")]\n'
                    % ("aes,sha3" if alt else "aes"),
                    # In place, which the proofs allow: `in_p = out_p`.
                    rust_decl="unsafe fn %s(inout: *mut [u8; 16], blocks: usize, tag: &mut [u8; 16], ivec: &mut [u8; 16], key: &[core::arch::aarch64::uint8x16_t; %d], htable: &[core::arch::aarch64::uint64x2_t; %d])"
                    % (name, rounds + 1, 12 if alt else 6),
                    several_exits=alt,
                )
                # A BTI landing pad means nothing inside inline assembly.
                input = assemble_and_disassemble(
                    input, tool_prefix="aarch64-linux-gnu-", defines=["NO_IBT=1"]
                )
                parse_file(input, d)
