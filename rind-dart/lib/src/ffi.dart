// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// The native functions in `rind-dart/src/lib.rs`, which `hook/build.dart`
// builds into this library's code asset, and the helpers that call them.
//
// Calls that finish in microseconds are leaf calls, which read Dart's typed
// data in place. Those that can run for milliseconds or more (RSA key
// generation and private-key operations, and PBKDF2) are not, since a leaf
// call holds up garbage collection; they take copies in native memory.

part of 'bindings.dart';

typedef _Free = Void Function(Pointer<Void>);

// Runs [call] with a slot for a handle, and returns the handle it stored.
Pointer<Void> _newHandle(int Function(Pointer<Pointer<Void>> slot) call) {
  final slot = malloc<Pointer<Void>>();
  try {
    _check(call(slot));
    return slot.value;
  } finally {
    malloc.free(slot);
  }
}

// Returns a non-negative [status], or throws for a negative one.
int _check(int status) {
  if (status >= 0) return status;
  if (status == -9) throw UnsupportedError(_lastMessage());
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

// Allocates [length] bytes, calls [call] with them, and returns the bytes it
// says it wrote.
Uint8List _output(int length, int Function(Uint8List out) call) {
  final out = Uint8List(length);
  return out.sublist(0, _check(call(out)));
}

// Copies [data] to native memory for a non-leaf call, freeing it after. A
// copy inside a call stays unwiped, as rind's own do.
T _native<T>(Uint8List data, T Function(Pointer<Uint8> pointer) call) {
  final pointer = malloc<Uint8>(data.isEmpty ? 1 : data.length);
  final view = pointer.asTypedList(data.length);
  try {
    view.setAll(0, data);
    return call(pointer);
  } finally {
    malloc.free(pointer);
  }
}

// A native object, freed with [finalizer] when this is collected.
abstract base class _Handle implements Finalizable {
  _Handle(this._pointer, NativeFinalizer finalizer) {
    finalizer.attach(this, _pointer, detach: this);
  }

  final Pointer<Void> _pointer;
}

// The longest key export, an RSA-8192 PKCS#8 key, fits in this many bytes.
const _exportLength = 8192;

// RSA-8192's modulus, which bounds RSA's signatures, ciphertexts, and
// plaintexts.
const _modulusLength = 1024;

NativeFinalizer _finalizer(Pointer<NativeFunction<_Free>> free) =>
    NativeFinalizer(free);

// --- Errors, CPU, randomness, comparison ---

@Native<IntPtr Function(Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_message',
  isLeaf: true,
)
external int _message(Pointer<Uint8> out, int outLen);

@Native<IntPtr Function()>(symbol: 'rind_dart_has_aes_hardware', isLeaf: true)
external int _hasAesHardware();

@Native<IntPtr Function(Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_rand_fill',
  isLeaf: true,
)
external int _randFill(Pointer<Uint8> out, int outLen);

@Native<IntPtr Function(Pointer<Uint8>, Size, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_constant_time_verify',
  isLeaf: true,
)
external int _constantTimeVerify(
  Pointer<Uint8> a,
  int aLen,
  Pointer<Uint8> b,
  int bLen,
);

// --- AEAD ---

@Native<_Free>(symbol: 'rind_dart_aead_key_free')
external void _aeadKeyFree(Pointer<Void> key);
final _aeadKeyFinalizer = _finalizer(Native.addressOf(_aeadKeyFree));

@Native<IntPtr Function(Uint32, Pointer<Uint8>, Size, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_aead_key_new',
  isLeaf: true,
)
external int _aeadKeyNew(
  int algorithm,
  Pointer<Uint8> key,
  int keyLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_aead_seal', isLeaf: true)
external int _aeadSeal(
  Pointer<Void> key,
  Pointer<Uint8> nonce,
  int nonceLen,
  Pointer<Uint8> aad,
  int aadLen,
  Pointer<Uint8> inOut,
  int len,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_aead_open', isLeaf: true)
external int _aeadOpen(
  Pointer<Void> key,
  Pointer<Uint8> nonce,
  int nonceLen,
  Pointer<Uint8> aad,
  int aadLen,
  Pointer<Uint8> inOut,
  int len,
);

@Native<_Free>(symbol: 'rind_dart_randomized_nonce_key_free')
external void _randomizedNonceKeyFree(Pointer<Void> key);
final _randomizedNonceKeyFinalizer = _finalizer(
  Native.addressOf(_randomizedNonceKeyFree),
);

@Native<IntPtr Function(Pointer<Uint8>, Size, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_randomized_nonce_key_new',
  isLeaf: true,
)
external int _randomizedNonceKeyNew(
  Pointer<Uint8> key,
  int keyLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
  )
>(symbol: 'rind_dart_randomized_nonce_key_seal', isLeaf: true)
external int _randomizedNonceKeySeal(
  Pointer<Void> key,
  Pointer<Uint8> aad,
  int aadLen,
  Pointer<Uint8> inOut,
  int len,
  Pointer<Uint8> nonceOut,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_randomized_nonce_key_open', isLeaf: true)
external int _randomizedNonceKeyOpen(
  Pointer<Void> key,
  Pointer<Uint8> nonce,
  int nonceLen,
  Pointer<Uint8> aad,
  int aadLen,
  Pointer<Uint8> inOut,
  int len,
);

// --- Digests ---

@Native<IntPtr Function(Uint32, Pointer<Uint8>, Size, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_digest',
  isLeaf: true,
)
external int _digest(
  int algorithm,
  Pointer<Uint8> data,
  int dataLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<_Free>(symbol: 'rind_dart_digest_context_free')
external void _digestContextFree(Pointer<Void> context);
final _digestContextFinalizer = _finalizer(
  Native.addressOf(_digestContextFree),
);

@Native<IntPtr Function(Uint32, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_digest_context_new',
  isLeaf: true,
)
external int _digestContextNew(int algorithm, Pointer<Pointer<Void>> out);

@Native<IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_digest_context_update',
  isLeaf: true,
)
external int _digestContextUpdate(
  Pointer<Void> context,
  Pointer<Uint8> data,
  int dataLen,
);

@Native<IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_digest_context_finish',
  isLeaf: true,
)
external int _digestContextFinish(
  Pointer<Void> context,
  Pointer<Uint8> out,
  int outLen,
);

// --- HMAC ---

@Native<_Free>(symbol: 'rind_dart_hmac_key_free')
external void _hmacKeyFree(Pointer<Void> key);
final _hmacKeyFinalizer = _finalizer(Native.addressOf(_hmacKeyFree));

@Native<IntPtr Function(Uint32, Pointer<Uint8>, Size, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_hmac_key_new',
  isLeaf: true,
)
external int _hmacKeyNew(
  int algorithm,
  Pointer<Uint8> key,
  int keyLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size, Pointer<Uint8>, Size)
>(symbol: 'rind_dart_hmac_sign', isLeaf: true)
external int _hmacSign(
  Pointer<Void> key,
  Pointer<Uint8> data,
  int dataLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<
  IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size, Pointer<Uint8>, Size)
>(symbol: 'rind_dart_hmac_verify', isLeaf: true)
external int _hmacVerify(
  Pointer<Void> key,
  Pointer<Uint8> data,
  int dataLen,
  Pointer<Uint8> tag,
  int tagLen,
);

@Native<_Free>(symbol: 'rind_dart_hmac_context_free')
external void _hmacContextFree(Pointer<Void> context);
final _hmacContextFinalizer = _finalizer(Native.addressOf(_hmacContextFree));

@Native<IntPtr Function(Pointer<Void>, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_hmac_context_new',
  isLeaf: true,
)
external int _hmacContextNew(Pointer<Void> key, Pointer<Pointer<Void>> out);

@Native<IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_hmac_context_update',
  isLeaf: true,
)
external int _hmacContextUpdate(
  Pointer<Void> context,
  Pointer<Uint8> data,
  int dataLen,
);

@Native<IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_hmac_context_sign',
  isLeaf: true,
)
external int _hmacContextSign(
  Pointer<Void> context,
  Pointer<Uint8> out,
  int outLen,
);

// --- HKDF ---

@Native<_Free>(symbol: 'rind_dart_hkdf_salt_free')
external void _hkdfSaltFree(Pointer<Void> salt);
final _hkdfSaltFinalizer = _finalizer(Native.addressOf(_hkdfSaltFree));

@Native<_Free>(symbol: 'rind_dart_hkdf_prk_free')
external void _hkdfPrkFree(Pointer<Void> prk);
final _hkdfPrkFinalizer = _finalizer(Native.addressOf(_hkdfPrkFree));

@Native<IntPtr Function(Uint32, Pointer<Uint8>, Size, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_hkdf_salt_new',
  isLeaf: true,
)
external int _hkdfSaltNew(
  int algorithm,
  Pointer<Uint8> salt,
  int saltLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size, Pointer<Pointer<Void>>)
>(symbol: 'rind_dart_hkdf_extract', isLeaf: true)
external int _hkdfExtract(
  Pointer<Void> salt,
  Pointer<Uint8> secret,
  int secretLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size, Pointer<Uint8>, Size)
>(symbol: 'rind_dart_hkdf_expand', isLeaf: true)
external int _hkdfExpand(
  Pointer<Void> prk,
  Pointer<Uint8> info,
  int infoLen,
  Pointer<Uint8> out,
  int outLen,
);

// --- PBKDF2 ---

@Native<_Free>(symbol: 'rind_dart_pbkdf2_secret_free')
external void _pbkdf2SecretFree(Pointer<Void> secret);
final _pbkdf2SecretFinalizer = _finalizer(Native.addressOf(_pbkdf2SecretFree));

@Native<IntPtr Function(Uint32, Pointer<Uint8>, Size, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_pbkdf2_secret_new',
  isLeaf: true,
)
external int _pbkdf2SecretNew(
  int algorithm,
  Pointer<Uint8> secret,
  int secretLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_pbkdf2_derive')
external int _pbkdf2Derive(
  Pointer<Void> secret,
  int iterations,
  Pointer<Uint8> salt,
  int saltLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_pbkdf2_verify')
external int _pbkdf2Verify(
  Pointer<Void> secret,
  int iterations,
  Pointer<Uint8> salt,
  int saltLen,
  Pointer<Uint8> previous,
  int previousLen,
);

// --- Key agreement ---

@Native<_Free>(symbol: 'rind_dart_agreement_private_key_free')
external void _agreementPrivateKeyFree(Pointer<Void> key);
final _agreementPrivateKeyFinalizer = _finalizer(
  Native.addressOf(_agreementPrivateKeyFree),
);

@Native<
  IntPtr Function(Uint32, Uint32, Pointer<Uint8>, Size, Pointer<Pointer<Void>>)
>(symbol: 'rind_dart_agreement_private_key_new', isLeaf: true)
external int _agreementPrivateKeyNew(
  int algorithm,
  int source,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Pointer<Void>> out,
);

@Native<IntPtr Function(Pointer<Void>, Uint32, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_agreement_private_key_export',
  isLeaf: true,
)
external int _agreementPrivateKeyExport(
  Pointer<Void> key,
  int what,
  Pointer<Uint8> out,
  int outLen,
);

@Native<
  IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size, Pointer<Uint8>, Size)
>(symbol: 'rind_dart_agreement_agree', isLeaf: true)
external int _agreementAgree(
  Pointer<Void> key,
  Pointer<Uint8> peer,
  int peerLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<
  IntPtr Function(
    Uint32,
    Uint32,
    Pointer<Uint8>,
    Size,
    Uint32,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_agreement_public_key', isLeaf: true)
external int _agreementPublicKey(
  int algorithm,
  int spki,
  Pointer<Uint8> bytes,
  int bytesLen,
  int export,
  Pointer<Uint8> out,
  int outLen,
);

// --- Signatures ---

@Native<_Free>(symbol: 'rind_dart_ecdsa_key_pair_free')
external void _ecdsaKeyPairFree(Pointer<Void> pair);
final _ecdsaKeyPairFinalizer = _finalizer(Native.addressOf(_ecdsaKeyPairFree));

@Native<
  IntPtr Function(
    Uint32,
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Pointer<Void>>,
  )
>(symbol: 'rind_dart_ecdsa_key_pair_new', isLeaf: true)
external int _ecdsaKeyPairNew(
  int algorithm,
  int source,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Uint8> publicKey,
  int publicKeyLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size, Pointer<Uint8>, Size)
>(symbol: 'rind_dart_ecdsa_sign', isLeaf: true)
external int _ecdsaSign(
  Pointer<Void> pair,
  Pointer<Uint8> message,
  int messageLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>, Uint32, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_ecdsa_key_pair_export',
  isLeaf: true,
)
external int _ecdsaKeyPairExport(
  Pointer<Void> pair,
  int what,
  Pointer<Uint8> out,
  int outLen,
);

@Native<_Free>(symbol: 'rind_dart_ed25519_key_pair_free')
external void _ed25519KeyPairFree(Pointer<Void> pair);
final _ed25519KeyPairFinalizer = _finalizer(
  Native.addressOf(_ed25519KeyPairFree),
);

@Native<
  IntPtr Function(
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Pointer<Void>>,
  )
>(symbol: 'rind_dart_ed25519_key_pair_new', isLeaf: true)
external int _ed25519KeyPairNew(
  int source,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Uint8> publicKey,
  int publicKeyLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size, Pointer<Uint8>, Size)
>(symbol: 'rind_dart_ed25519_sign', isLeaf: true)
external int _ed25519Sign(
  Pointer<Void> pair,
  Pointer<Uint8> message,
  int messageLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>, Uint32, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_ed25519_key_pair_export',
  isLeaf: true,
)
external int _ed25519KeyPairExport(
  Pointer<Void> pair,
  int what,
  Pointer<Uint8> out,
  int outLen,
);

@Native<_Free>(symbol: 'rind_dart_rsa_key_pair_free')
external void _rsaKeyPairFree(Pointer<Void> pair);
final _rsaKeyPairFinalizer = _finalizer(Native.addressOf(_rsaKeyPairFree));

// Not a leaf call: generating a key takes up to seconds.
@Native<
  IntPtr Function(Uint32, Uint32, Pointer<Uint8>, Size, Pointer<Pointer<Void>>)
>(symbol: 'rind_dart_rsa_key_pair_new')
external int _rsaKeyPairNew(
  int source,
  int size,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_rsa_sign')
external int _rsaSign(
  Pointer<Void> pair,
  int algorithm,
  Pointer<Uint8> message,
  int messageLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>, Uint32, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_rsa_key_pair_export',
  isLeaf: true,
)
external int _rsaKeyPairExport(
  Pointer<Void> pair,
  int what,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Uint32, Pointer<Void>, Uint32, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_key_pair_public_key',
  isLeaf: true,
)
external int _keyPairPublicKey(
  int kind,
  Pointer<Void> pair,
  int algorithm,
  Pointer<Pointer<Void>> out,
);

@Native<_Free>(symbol: 'rind_dart_public_key_free')
external void _publicKeyFree(Pointer<Void> key);
final _publicKeyFinalizer = _finalizer(Native.addressOf(_publicKeyFree));

@Native<
  IntPtr Function(
    Uint32,
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Pointer<Void>>,
  )
>(symbol: 'rind_dart_public_key_new', isLeaf: true)
external int _publicKeyNew(
  int algorithm,
  int source,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Uint8> exponent,
  int exponentLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size, Pointer<Uint8>, Size)
>(symbol: 'rind_dart_public_key_verify', isLeaf: true)
external int _publicKeyVerify(
  Pointer<Void> key,
  Pointer<Uint8> message,
  int messageLen,
  Pointer<Uint8> signature,
  int signatureLen,
);

@Native<IntPtr Function(Pointer<Void>, Uint32, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_public_key_export',
  isLeaf: true,
)
external int _publicKeyExport(
  Pointer<Void> key,
  int spki,
  Pointer<Uint8> out,
  int outLen,
);

// --- Key encapsulation ---

@Native<_Free>(symbol: 'rind_dart_decapsulation_key_free')
external void _decapsulationKeyFree(Pointer<Void> key);
final _decapsulationKeyFinalizer = _finalizer(
  Native.addressOf(_decapsulationKeyFree),
);

@Native<IntPtr Function(Uint32, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_decapsulation_key_generate',
  isLeaf: true,
)
external int _decapsulationKeyGenerate(
  int algorithm,
  Pointer<Pointer<Void>> out,
);

@Native<IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_decapsulation_key_public_key',
  isLeaf: true,
)
external int _decapsulationKeyPublicKey(
  Pointer<Void> key,
  Pointer<Uint8> out,
  int outLen,
);

@Native<
  IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size, Pointer<Uint8>, Size)
>(symbol: 'rind_dart_decapsulate', isLeaf: true)
external int _decapsulate(
  Pointer<Void> key,
  Pointer<Uint8> ciphertext,
  int ciphertextLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<_Free>(symbol: 'rind_dart_encapsulation_key_free')
external void _encapsulationKeyFree(Pointer<Void> key);
final _encapsulationKeyFinalizer = _finalizer(
  Native.addressOf(_encapsulationKeyFree),
);

@Native<IntPtr Function(Uint32, Pointer<Uint8>, Size, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_encapsulation_key_new',
  isLeaf: true,
)
external int _encapsulationKeyNew(
  int algorithm,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size, Pointer<Uint8>, Size)
>(symbol: 'rind_dart_encapsulate', isLeaf: true)
external int _encapsulate(
  Pointer<Void> key,
  Pointer<Uint8> ciphertext,
  int ciphertextLen,
  Pointer<Uint8> secret,
  int secretLen,
);

// --- RSA encryption ---

@Native<_Free>(symbol: 'rind_dart_decrypting_key_free')
external void _decryptingKeyFree(Pointer<Void> key);
final _decryptingKeyFinalizer = _finalizer(
  Native.addressOf(_decryptingKeyFree),
);

// Not a leaf call: generating a key takes up to seconds.
@Native<
  IntPtr Function(
    Uint32,
    Uint32,
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Pointer<Void>>,
  )
>(symbol: 'rind_dart_decrypting_key_new')
external int _decryptingKeyNew(
  int algorithm,
  int source,
  int size,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Pointer<Void>> out,
);

@Native<IntPtr Function(Pointer<Void>, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_decrypting_key_public_key',
  isLeaf: true,
)
external int _decryptingKeyPublicKey(
  Pointer<Void> key,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_decrypt')
external int _decrypt(
  Pointer<Void> key,
  Pointer<Uint8> ciphertext,
  int ciphertextLen,
  Pointer<Uint8> label,
  int labelLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>, Uint32, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_decrypting_key_export',
  isLeaf: true,
)
external int _decryptingKeyExport(
  Pointer<Void> key,
  int what,
  Pointer<Uint8> out,
  int outLen,
);

@Native<_Free>(symbol: 'rind_dart_encrypting_key_free')
external void _encryptingKeyFree(Pointer<Void> key);
final _encryptingKeyFinalizer = _finalizer(
  Native.addressOf(_encryptingKeyFree),
);

@Native<
  IntPtr Function(
    Uint32,
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Pointer<Void>>,
  )
>(symbol: 'rind_dart_encrypting_key_new', isLeaf: true)
external int _encryptingKeyNew(
  int algorithm,
  int source,
  Pointer<Uint8> bytes,
  int bytesLen,
  Pointer<Uint8> exponent,
  int exponentLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_encrypt', isLeaf: true)
external int _encrypt(
  Pointer<Void> key,
  Pointer<Uint8> message,
  int messageLen,
  Pointer<Uint8> label,
  int labelLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>, Uint32, Pointer<Uint8>, Size)>(
  symbol: 'rind_dart_encrypting_key_export',
  isLeaf: true,
)
external int _encryptingKeyExport(
  Pointer<Void> key,
  int spki,
  Pointer<Uint8> out,
  int outLen,
);

@Native<
  IntPtr Function(
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_aes_cbc', isLeaf: true)
external int _aesCbc(
  int decrypt,
  Pointer<Uint8> key,
  int keyLen,
  Pointer<Uint8> iv,
  int ivLen,
  Pointer<Uint8> inOut,
  int inOutLen,
);

@Native<
  IntPtr Function(
    Pointer<Uint8>,
    Size,
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_aes_ctr', isLeaf: true)
external int _aesCtr(
  Pointer<Uint8> key,
  int keyLen,
  int counterBits,
  Pointer<Uint8> counter,
  int counterLen,
  Pointer<Uint8> inOut,
  int inOutLen,
);

@Native<
  IntPtr Function(
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Uint32,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_chacha20', isLeaf: true)
external int _chacha20(
  Pointer<Uint8> key,
  int keyLen,
  Pointer<Uint8> nonce,
  int nonceLen,
  int counter,
  Pointer<Uint8> inOut,
  int inOutLen,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_randomized_nonce_key_seal_with_nonce', isLeaf: true)
external int _randomizedNonceKeySealWithNonce(
  Pointer<Void> key,
  Pointer<Uint8> nonce,
  int nonceLen,
  Pointer<Uint8> aad,
  int aadLen,
  Pointer<Uint8> inOut,
  int len,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Uint32,
    Uint32,
    Pointer<Uint8>,
    Size,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_rsa_sign_pss')
external int _rsaSignPss(
  Pointer<Void> pair,
  int hash,
  int saltLen,
  Pointer<Uint8> message,
  int messageLen,
  Pointer<Uint8> out,
  int outLen,
);

@Native<IntPtr Function(Pointer<Void>)>(
  symbol: 'rind_dart_encrypting_key_max_message_len',
  isLeaf: true,
)
external int _encryptingKeyMaxMessageLen(Pointer<Void> key);
