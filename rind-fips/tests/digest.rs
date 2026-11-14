// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Digests through the module match rind's, whose own tests check them
//! against NIST's vectors and aws-lc-rs: one-shot, fed in pieces, and from
//! a context cloned midway, which must fork the state rather than share it.
#![cfg(rind_fips_module)]

use rind_fips::digest::{self, Context};

#[test]
fn digests_match_rind() {
    let message: Vec<u8> = (0..1000u32).map(|i| (i * 7) as u8).collect();
    for (ours, theirs) in [
        (&digest::SHA256, &rind::digest::SHA256),
        (&digest::SHA384, &rind::digest::SHA384),
        (&digest::SHA512, &rind::digest::SHA512),
        (&digest::SHA512_256, &rind::digest::SHA512_256),
        (&digest::SHA3_256, &rind::digest::SHA3_256),
        (&digest::SHA3_384, &rind::digest::SHA3_384),
        (&digest::SHA3_512, &rind::digest::SHA3_512),
    ] {
        assert_eq!(ours.output_len(), theirs.output_len());
        for len in [0, 1, 55, 56, 64, 127, 128, 135, 136, 1000] {
            let expected = rind::digest::digest(theirs, &message[..len]);
            assert_eq!(
                digest::digest(ours, &message[..len]).as_ref(),
                expected.as_ref(),
                "{len} bytes"
            );

            let mut context = Context::new(ours);
            for piece in message[..len].chunks(17) {
                context.update(piece);
            }
            assert_eq!(
                context.finish().as_ref(),
                expected.as_ref(),
                "{len} bytes in pieces"
            );
        }

        // A clone continues apart from its original.
        let mut original = Context::new(ours);
        original.update(&message[..300]);
        let mut clone = original.clone();
        original.update(&message[300..]);
        clone.update(b"elsewhere");
        let mut reference = rind::digest::Context::new(theirs);
        reference.update(&message[..300]);
        reference.update(b"elsewhere");
        assert_eq!(
            original.finish().as_ref(),
            rind::digest::digest(theirs, &message).as_ref()
        );
        assert_eq!(clone.finish().as_ref(), reference.finish().as_ref());
    }
}
