// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import 'package:rind/ed25519.dart' as ed25519;

// The first rind call in this process. Resolution must not depend on some
// other library having already loaded the code asset.
void main() {
  ed25519.KeyPair.generate();
}
