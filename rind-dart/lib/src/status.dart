// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// Status mapping, buffers, and bounds every native call shares.
//
// `hook/build.dart` registers one code asset, [nativeAssetId]. The annotation
// names it, because this library's own URI is not that asset.
@DefaultAsset(nativeAssetId)
library;

import 'dart:convert';
import 'dart:ffi';
import 'dart:typed_data';

import 'package:ffi/ffi.dart';

import 'error.dart';

/// The code asset `hook/build.dart` registers, which every `@Native` resolves.
const nativeAssetId = 'package:rind/src/bindings.dart';

/// Returns a non-negative [status], or throws for a negative one.
int check(int status) {
  if (status >= 0) return status;
  if (status == -10) throw StateError('rind binding bug: ${_lastMessage()}');
  throw RindException(
    RindError.values[-status - 1],
    status == -2 ? _lastMessage() : null,
  );
}

String _lastMessage() {
  final out = Uint8List(256);
  final len = _message(out.address, out.length);
  return utf8.decode(
    out.sublist(0, len < out.length ? len : out.length),
    allowMalformed: true,
  );
}

/// Allocates [length] zeroed bytes and returns what [call] wrote into them.
///
/// [Uint8List.new] zeroes the buffer. Rust borrows it as `&mut [u8]`, which
/// has to already be initialized.
Uint8List output(int length, int Function(Uint8List out) call) {
  final out = Uint8List(length);
  return out.sublist(0, check(call(out)));
}

/// The longest key export, an RSA-8192 PKCS#8 key, fits in this many bytes.
const exportLength = 8192;

/// The longest X9.62 uncompressed point, P-521's: a 0x04 tag and two
/// 66-byte coordinates. P-256's and P-384's are 65 and 97 bytes.
const maxEcPointLength = 1 + 2 * 66;

/// The longest NIST curve `SubjectPublicKeyInfo`, P-521's: id-ecPublicKey
/// and the curve OID around [maxEcPointLength] bytes.
const maxEcSpkiLength = 158;

/// Runs [call] with a slot for the handle it stores, and returns that pointer.
///
/// The pointer is the one [call] just wrote. This holds no key of its own.
Pointer<Void> newHandle(int Function(Pointer<Pointer<Void>> slot) call) {
  final slot = malloc<Pointer<Void>>();
  try {
    check(call(slot));
    return slot.value;
  } finally {
    malloc.free(slot);
  }
}

/// Copies [data] into native memory for a non-leaf call, then frees it.
///
/// A non-leaf call can let the garbage collector move a [Uint8List], so the
/// bytes have to live in native memory. [setAll] writes every byte before the
/// call. A copy inside a call stays unwiped, as rind's own do.
T nativeCopy<T>(Uint8List data, T Function(Pointer<Uint8> pointer) call) {
  final pointer = malloc<Uint8>(data.isEmpty ? 1 : data.length);
  final view = pointer.asTypedList(data.length);
  try {
    view.setAll(0, data);
    return call(pointer);
  } finally {
    malloc.free(pointer);
  }
}

/// Frees one native handle.
typedef HandleFree = Void Function(Pointer<Void>);

/// Builds the finalizer that runs [free] when its handle is collected.
NativeFinalizer finalizer(Pointer<NativeFunction<HandleFree>> free) =>
    NativeFinalizer(free);

@Native<IntPtr Function(Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_message',
  isLeaf: true,
)
external int _message(Pointer<Uint8> out, int outLen);
