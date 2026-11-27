// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

/// Algorithms only legacy protocols and formats should use: SHA-1 and MD5.
///
/// RSA's are in `package:rind/rsa_legacy.dart`.
library;

export 'src/bindings.dart'
    show digestMd5, digestSha1, hkdfSha1, hmacSha1, pbkdf2HmacSha1;
