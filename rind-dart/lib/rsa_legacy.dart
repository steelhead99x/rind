// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

/// RSA algorithms only legacy protocols should use: SHA-1, and verification
/// with another modulus floor than 2048 bits, imported `as rsa` beside
/// `package:rind/rsa.dart`.
library;

export 'src/rsa.dart'
    show
        oaepSha1,
        pkcs1Min1024Sha1,
        pkcs1Min1024Sha256,
        pkcs1Min1024Sha512,
        pkcs1Min3072Sha384,
        pkcs1Sha1;
