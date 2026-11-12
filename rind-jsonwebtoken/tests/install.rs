//! Installs rind's provider for this process and drives jsonwebtoken through
//! its public API, the way an application would.

mod common;

use jsonwebtoken::jwk::Jwk;
use jsonwebtoken::{Algorithm, DecodingKey, Header, Validation, decode, encode};
use serde_json::{Value, json};

#[test]
fn tokens_round_trip_through_jwks() {
    rind_jsonwebtoken::DEFAULT_PROVIDER
        .install_default()
        .unwrap();

    let claims = json!({ "sub": "rind", "exp": jsonwebtoken::get_current_timestamp() + 60 });

    for key in common::all() {
        let token = encode(&Header::new(key.algorithm), &claims, &key.encoding).unwrap();
        let validation = Validation::new(key.algorithm);

        let mut decoding = vec![key.decoding.clone()];
        // jsonwebtoken reads an Ed25519 JWK only from a 48-byte PKCS#8 v1 key.
        if key.algorithm != Algorithm::EdDSA || key.encoding.as_bytes().len() == 48 {
            let jwk = Jwk::from_encoding_key(&key.encoding, key.algorithm)
                .unwrap_or_else(|e| panic!("{}: {e}", key.label()));
            decoding.push(DecodingKey::from_jwk(&jwk).unwrap());
        }

        let mut forged = token.clone().into_bytes();
        let last = forged.len() - 2;
        forged[last] = if forged[last] == b'A' { b'B' } else { b'A' };
        let forged = String::from_utf8(forged).unwrap();

        for decoding in &decoding {
            let decoded = decode::<Value>(&token, decoding, &validation)
                .unwrap_or_else(|e| panic!("{}: {e}", key.label()));
            assert_eq!(decoded.claims, claims, "{}", key.label());
            assert!(
                decode::<Value>(&forged, decoding, &validation).is_err(),
                "{}",
                key.label()
            );
        }
    }
}
