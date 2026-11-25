// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

/// RSA signatures and RSA-OAEP encryption, imported `as rsa`.
///
/// Algorithms only legacy protocols should use are in
/// `package:rind/rsa_legacy.dart`.
library;

export 'src/rsa.dart'
    show
        DecryptingKey,
        EncryptingKey,
        KeyPair,
        KeySize,
        OaepAlgorithm,
        PssSigningAlgorithm,
        PssVerificationAlgorithm,
        PublicKey,
        SigningAlgorithm,
        SigningScheme,
        VerificationAlgorithm;
export 'src/error.dart' show RindError, RindException;
