// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import 'dart:typed_data';

import 'package:rind/rsa.dart' as rsa;

// The first rind call in this process. An empty key is refused once the
// native has run; a failure to resolve it is a different error.
void main() {
  try {
    rsa.PublicKey(Uint8List(0));
  } on rsa.RindException {
    return;
  }
  throw StateError('an empty RSA key was accepted');
}
