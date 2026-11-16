// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// The natives behind `package:rind/rind.dart` and `package:rind/legacy.dart`,
// which export their names from here. The signature libraries are separate,
// since each has its own `KeyPair` and `PublicKey`.
//
// `hook/build.dart` registers one code asset, this library's URI. Naming it
// keeps that id if this file moves.
@DefaultAsset(nativeAssetId)
library;

import 'dart:ffi';
import 'dart:typed_data';

import 'error.dart';
import 'handle.dart';
import 'status.dart';

part 'aead.dart';
part 'agreement.dart';
part 'cipher.dart';
part 'digest.dart';
part 'ffi.dart';
part 'hkdf.dart';
part 'hmac.dart';
part 'kem.dart';
part 'pbkdf2.dart';
part 'rand.dart';
