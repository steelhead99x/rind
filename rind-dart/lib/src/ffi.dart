// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// The native functions the rest of `package:rind/rind.dart` calls, in
// `rind-dart/src/lib.rs`.

part of 'bindings.dart';

// --- CPU, randomness, comparison ---

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

@Native<HandleFree>(symbol: 'rind_dart_aead_key_free')
external void _aeadKeyFree(Pointer<Void> key);
final _aeadKeyFinalizer = finalizer(Native.addressOf(_aeadKeyFree));

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

@Native<HandleFree>(symbol: 'rind_dart_randomized_nonce_key_free')
external void _randomizedNonceKeyFree(Pointer<Void> key);
final _randomizedNonceKeyFinalizer = finalizer(
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

// --- Ciphers ---

@Native<HandleFree>(symbol: 'rind_dart_aes_cbc_encrypting_key_free')
external void _aesCbcEncryptingKeyFree(Pointer<Void> key);
final _aesCbcEncryptingKeyFinalizer = finalizer(
  Native.addressOf(_aesCbcEncryptingKeyFree),
);

@Native<IntPtr Function(Uint32, Pointer<Uint8>, Size, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_aes_cbc_encrypting_key_new',
  isLeaf: true,
)
external int _aesCbcEncryptingKeyNew(
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
    Uint32,
    Pointer<Uint8>,
    Size,
    Size,
  )
>(symbol: 'rind_dart_aes_cbc_encrypt', isLeaf: true)
external int _aesCbcEncrypt(
  Pointer<Void> key,
  Pointer<Uint8> iv,
  int ivLen,
  int pad,
  Pointer<Uint8> inOut,
  int inOutLen,
  int len,
);

@Native<HandleFree>(symbol: 'rind_dart_aes_cbc_decrypting_key_free')
external void _aesCbcDecryptingKeyFree(Pointer<Void> key);
final _aesCbcDecryptingKeyFinalizer = finalizer(
  Native.addressOf(_aesCbcDecryptingKeyFree),
);

@Native<IntPtr Function(Uint32, Pointer<Uint8>, Size, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_aes_cbc_decrypting_key_new',
  isLeaf: true,
)
external int _aesCbcDecryptingKeyNew(
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
    Uint32,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_aes_cbc_decrypt', isLeaf: true)
external int _aesCbcDecrypt(
  Pointer<Void> key,
  Pointer<Uint8> iv,
  int ivLen,
  int pad,
  Pointer<Uint8> inOut,
  int len,
);

@Native<HandleFree>(symbol: 'rind_dart_aes_ctr_free')
external void _aesCtrFree(Pointer<Void> key);
final _aesCtrFinalizer = finalizer(Native.addressOf(_aesCtrFree));

@Native<
  IntPtr Function(Uint32, Pointer<Uint8>, Size, Uint32, Pointer<Pointer<Void>>)
>(symbol: 'rind_dart_aes_ctr_new', isLeaf: true)
external int _aesCtrNew(
  int algorithm,
  Pointer<Uint8> key,
  int keyLen,
  int counterBits,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(Pointer<Void>, Pointer<Uint8>, Size, Pointer<Uint8>, Size)
>(symbol: 'rind_dart_aes_ctr_apply_keystream', isLeaf: true)
external int _aesCtrApplyKeystream(
  Pointer<Void> key,
  Pointer<Uint8> counterBlock,
  int counterBlockLen,
  Pointer<Uint8> inOut,
  int len,
);

@Native<HandleFree>(symbol: 'rind_dart_chacha20_free')
external void _chacha20Free(Pointer<Void> key);
final _chacha20Finalizer = finalizer(Native.addressOf(_chacha20Free));

@Native<IntPtr Function(Pointer<Uint8>, Size, Pointer<Pointer<Void>>)>(
  symbol: 'rind_dart_chacha20_new',
  isLeaf: true,
)
external int _chacha20New(
  Pointer<Uint8> key,
  int keyLen,
  Pointer<Pointer<Void>> out,
);

@Native<
  IntPtr Function(
    Pointer<Void>,
    Pointer<Uint8>,
    Size,
    Uint32,
    Pointer<Uint8>,
    Size,
  )
>(symbol: 'rind_dart_chacha20_apply_keystream', isLeaf: true)
external int _chacha20ApplyKeystream(
  Pointer<Void> key,
  Pointer<Uint8> nonce,
  int nonceLen,
  int counter,
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

@Native<HandleFree>(symbol: 'rind_dart_digest_context_free')
external void _digestContextFree(Pointer<Void> context);
final _digestContextFinalizer = finalizer(Native.addressOf(_digestContextFree));

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

@Native<HandleFree>(symbol: 'rind_dart_hmac_key_free')
external void _hmacKeyFree(Pointer<Void> key);
final _hmacKeyFinalizer = finalizer(Native.addressOf(_hmacKeyFree));

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

@Native<HandleFree>(symbol: 'rind_dart_hmac_context_free')
external void _hmacContextFree(Pointer<Void> context);
final _hmacContextFinalizer = finalizer(Native.addressOf(_hmacContextFree));

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

@Native<HandleFree>(symbol: 'rind_dart_hkdf_salt_free')
external void _hkdfSaltFree(Pointer<Void> salt);
final _hkdfSaltFinalizer = finalizer(Native.addressOf(_hkdfSaltFree));

@Native<HandleFree>(symbol: 'rind_dart_hkdf_prk_free')
external void _hkdfPrkFree(Pointer<Void> prk);
final _hkdfPrkFinalizer = finalizer(Native.addressOf(_hkdfPrkFree));

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

@Native<HandleFree>(symbol: 'rind_dart_pbkdf2_secret_free')
external void _pbkdf2SecretFree(Pointer<Void> secret);
final _pbkdf2SecretFinalizer = finalizer(Native.addressOf(_pbkdf2SecretFree));

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

@Native<HandleFree>(symbol: 'rind_dart_agreement_private_key_free')
external void _agreementPrivateKeyFree(Pointer<Void> key);
final _agreementPrivateKeyFinalizer = finalizer(
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

// --- Key encapsulation ---

@Native<HandleFree>(symbol: 'rind_dart_decapsulation_key_free')
external void _decapsulationKeyFree(Pointer<Void> key);
final _decapsulationKeyFinalizer = finalizer(
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

@Native<HandleFree>(symbol: 'rind_dart_encapsulation_key_free')
external void _encapsulationKeyFree(Pointer<Void> key);
final _encapsulationKeyFinalizer = finalizer(
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
