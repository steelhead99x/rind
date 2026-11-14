// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! MD5's compression function, from [RFC 1321](https://www.rfc-editor.org/rfc/rfc1321).
//!
//! Each step waits on the word the step before produced only through its
//! boolean function, one add, the rotate, and another add: everything else
//! sums off that critical path.

/// `v`, which the optimiser can no longer see is a sum.
///
/// Each step's `a + X[k] + T` would otherwise be reassociated to add its
/// constant after the boolean function, putting a sixth operation on the
/// critical path. `black_box` also hides it, but through memory, and measured
/// 9% slower on an i7-8700.
#[inline(always)]
#[cfg(not(any(target_family = "wasm", miri)))]
// The operand appears only in a comment, so no register width is printed.
#[allow(asm_sub_register)]
fn opaque(mut v: u32) -> u32 {
    // SAFETY: the assembly is empty, so it reads, writes, and clobbers
    // nothing but returns `v` in the register it took it in.
    unsafe {
        core::arch::asm!("/* {0} */", inout(reg) v, options(pure, nomem, nostack, preserves_flags));
    }
    v
}

// WebAssembly has no stable inline assembly or general-purpose register class,
// and Miri runs none. Keep the reassociation barrier without changing MD5's
// arithmetic.
#[inline(always)]
#[cfg(any(target_family = "wasm", miri))]
fn opaque(v: u32) -> u32 {
    core::hint::black_box(v)
}

fn md5_compress_block(state: &mut [u32; 4], block: &[u8; 64]) {
    let mut x = [0u32; 16];
    let (words, _) = block.as_chunks::<4>();
    for (x, word) in x.iter_mut().zip(words) {
        *x = u32::from_le_bytes(*word);
    }

    let [mut a, mut b, mut c, mut d] = *state;

    // One step: `$a = $b + ROTL($a + f($b, $c, $d) + X[k] + T, s)`, where
    // `T` is `floor(abs(sin(i + 1)) * 2^32)` for step `i`.
    macro_rules! step {
        ($f:ident, $a:ident, $b:ident, $c:ident, $d:ident, $k:literal, $s:literal, $t:literal) => {
            $a = $f!(opaque($a.wrapping_add(x[$k]).wrapping_add($t)), $b, $c, $d)
                .rotate_left($s)
                .wrapping_add($b);
        };
    }

    // `F(x, y, z) = (x & y) | (!x & z)`: `y` or `z`, chosen by `x`.
    macro_rules! f {
        ($sum:expr, $b:ident, $c:ident, $d:ident) => {
            $sum.wrapping_add($d ^ ($b & ($c ^ $d)))
        };
    }
    // `G(x, y, z) = (x & z) | (y & !z)`, whose halves share no bits, so each
    // adds on its own and `x` joins last.
    macro_rules! g {
        ($sum:expr, $b:ident, $c:ident, $d:ident) => {
            $sum.wrapping_add($c & !$d).wrapping_add($b & $d)
        };
    }
    macro_rules! h {
        ($sum:expr, $b:ident, $c:ident, $d:ident) => {
            $sum.wrapping_add($b ^ ($c ^ $d))
        };
    }
    macro_rules! i {
        ($sum:expr, $b:ident, $c:ident, $d:ident) => {
            $sum.wrapping_add($c ^ ($b | !$d))
        };
    }

    step!(f, a, b, c, d, 0, 7, 0xd76aa478);
    step!(f, d, a, b, c, 1, 12, 0xe8c7b756);
    step!(f, c, d, a, b, 2, 17, 0x242070db);
    step!(f, b, c, d, a, 3, 22, 0xc1bdceee);
    step!(f, a, b, c, d, 4, 7, 0xf57c0faf);
    step!(f, d, a, b, c, 5, 12, 0x4787c62a);
    step!(f, c, d, a, b, 6, 17, 0xa8304613);
    step!(f, b, c, d, a, 7, 22, 0xfd469501);
    step!(f, a, b, c, d, 8, 7, 0x698098d8);
    step!(f, d, a, b, c, 9, 12, 0x8b44f7af);
    step!(f, c, d, a, b, 10, 17, 0xffff5bb1);
    step!(f, b, c, d, a, 11, 22, 0x895cd7be);
    step!(f, a, b, c, d, 12, 7, 0x6b901122);
    step!(f, d, a, b, c, 13, 12, 0xfd987193);
    step!(f, c, d, a, b, 14, 17, 0xa679438e);
    step!(f, b, c, d, a, 15, 22, 0x49b40821);

    step!(g, a, b, c, d, 1, 5, 0xf61e2562);
    step!(g, d, a, b, c, 6, 9, 0xc040b340);
    step!(g, c, d, a, b, 11, 14, 0x265e5a51);
    step!(g, b, c, d, a, 0, 20, 0xe9b6c7aa);
    step!(g, a, b, c, d, 5, 5, 0xd62f105d);
    step!(g, d, a, b, c, 10, 9, 0x02441453);
    step!(g, c, d, a, b, 15, 14, 0xd8a1e681);
    step!(g, b, c, d, a, 4, 20, 0xe7d3fbc8);
    step!(g, a, b, c, d, 9, 5, 0x21e1cde6);
    step!(g, d, a, b, c, 14, 9, 0xc33707d6);
    step!(g, c, d, a, b, 3, 14, 0xf4d50d87);
    step!(g, b, c, d, a, 8, 20, 0x455a14ed);
    step!(g, a, b, c, d, 13, 5, 0xa9e3e905);
    step!(g, d, a, b, c, 2, 9, 0xfcefa3f8);
    step!(g, c, d, a, b, 7, 14, 0x676f02d9);
    step!(g, b, c, d, a, 12, 20, 0x8d2a4c8a);

    step!(h, a, b, c, d, 5, 4, 0xfffa3942);
    step!(h, d, a, b, c, 8, 11, 0x8771f681);
    step!(h, c, d, a, b, 11, 16, 0x6d9d6122);
    step!(h, b, c, d, a, 14, 23, 0xfde5380c);
    step!(h, a, b, c, d, 1, 4, 0xa4beea44);
    step!(h, d, a, b, c, 4, 11, 0x4bdecfa9);
    step!(h, c, d, a, b, 7, 16, 0xf6bb4b60);
    step!(h, b, c, d, a, 10, 23, 0xbebfbc70);
    step!(h, a, b, c, d, 13, 4, 0x289b7ec6);
    step!(h, d, a, b, c, 0, 11, 0xeaa127fa);
    step!(h, c, d, a, b, 3, 16, 0xd4ef3085);
    step!(h, b, c, d, a, 6, 23, 0x04881d05);
    step!(h, a, b, c, d, 9, 4, 0xd9d4d039);
    step!(h, d, a, b, c, 12, 11, 0xe6db99e5);
    step!(h, c, d, a, b, 15, 16, 0x1fa27cf8);
    step!(h, b, c, d, a, 2, 23, 0xc4ac5665);

    step!(i, a, b, c, d, 0, 6, 0xf4292244);
    step!(i, d, a, b, c, 7, 10, 0x432aff97);
    step!(i, c, d, a, b, 14, 15, 0xab9423a7);
    step!(i, b, c, d, a, 5, 21, 0xfc93a039);
    step!(i, a, b, c, d, 12, 6, 0x655b59c3);
    step!(i, d, a, b, c, 3, 10, 0x8f0ccc92);
    step!(i, c, d, a, b, 10, 15, 0xffeff47d);
    step!(i, b, c, d, a, 1, 21, 0x85845dd1);
    step!(i, a, b, c, d, 8, 6, 0x6fa87e4f);
    step!(i, d, a, b, c, 15, 10, 0xfe2ce6e0);
    step!(i, c, d, a, b, 6, 15, 0xa3014314);
    step!(i, b, c, d, a, 13, 21, 0x4e0811a1);
    step!(i, a, b, c, d, 4, 6, 0xf7537e82);
    step!(i, d, a, b, c, 11, 10, 0xbd3af235);
    step!(i, c, d, a, b, 2, 15, 0x2ad7d2bb);
    step!(i, b, c, d, a, 9, 21, 0xeb86d391);

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
}

/// Compresses `blocks`, a whole number of 64-byte blocks, into `state`.
pub(crate) fn md5_compress_blocks(state: &mut [u32; 4], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));

    let (chunks, _) = blocks.as_chunks::<64>();
    for block in chunks {
        md5_compress_block(state, block);
    }
}
