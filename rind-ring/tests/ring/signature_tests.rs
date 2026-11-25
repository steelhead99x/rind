#![allow(missing_docs)]

use ring::signature;
#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
use wasm_bindgen_test::wasm_bindgen_test as test;

#[allow(deprecated)]
use crate::test;

#[test]
fn signature_impl_test() {
    test::compile_time_assert_clone::<signature::Signature>();
    test::compile_time_assert_copy::<signature::Signature>();
    test::compile_time_assert_send::<signature::Signature>();
    test::compile_time_assert_sync::<signature::Signature>();

    let unparsed_public_key =
        signature::UnparsedPublicKey::new(&signature::ED25519, &[0x01, 0x02, 0x03]);

    assert_eq!(
        format!("{:?}", unparsed_public_key),
        r#"UnparsedPublicKey { algorithm: ring::signature::ED25519, bytes: "010203" }"#
    );

    // Test `AsRef<[u8]>`
    assert_eq!(unparsed_public_key.as_ref(), &[0x01, 0x02, 0x03]);
}
