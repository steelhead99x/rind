// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import 'package:rind/ecdsa.dart' as ecdsa;

// The first rind call in this process. Resolution must not depend on some
// other library having already loaded the code asset.
void main() {
  ecdsa.KeyPair.generate(ecdsa.SigningAlgorithm.p256Sha256Asn1);
}
