// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'cryptography.dart';

/// The rind HMAC over [algorithm], throwing [UnsupportedError] when rind has
/// none.
rind.HmacAlgorithm _hmacOf(HashAlgorithm algorithm) => switch (algorithm) {
  Sha1() => rind.hmacSha1,
  Sha256() => rind.HmacAlgorithm.sha256,
  Sha384() => rind.HmacAlgorithm.sha384,
  Sha512() => rind.HmacAlgorithm.sha512,
  _ => throw _unsupported('HMAC over $algorithm'),
};

mixin _Hash on HashAlgorithm {
  rind.DigestAlgorithm get _digest;

  @override
  Future<Hash> hash(List<int> input) async =>
      Hash(rind.digest(_digest, _bytes(input)));

  @override
  HashSink newHashSink() => _HashSink(_digest);
}

final class _Sha1 extends Sha1 with _Hash {
  const _Sha1() : super.constructor();

  @override
  rind.DigestAlgorithm get _digest => rind.digestSha1;
}

final class _Sha256 extends Sha256 with _Hash {
  const _Sha256() : super.constructor();

  @override
  rind.DigestAlgorithm get _digest => rind.DigestAlgorithm.sha256;
}

final class _Sha384 extends Sha384 with _Hash {
  const _Sha384() : super.constructor();

  @override
  rind.DigestAlgorithm get _digest => rind.DigestAlgorithm.sha384;
}

final class _Sha512 extends Sha512 with _Hash {
  const _Sha512() : super.constructor();

  @override
  rind.DigestAlgorithm get _digest => rind.DigestAlgorithm.sha512;
}

final class _HashSink extends HashSink {
  _HashSink(rind.DigestAlgorithm algorithm)
    : _context = rind.DigestContext(algorithm);

  final rind.DigestContext _context;
  Hash? _hash;

  @override
  void addSlice(List<int> chunk, int start, int end, bool isLast) {
    if (_hash != null) throw StateError('Sink is closed');
    end = RangeError.checkValidRange(start, end, chunk.length);
    _context.update(_slice(chunk, start, end));
    if (isLast) close();
  }

  @override
  void close() {
    _hash ??= Hash(_context.finish());
  }

  @override
  Future<Hash> hash() async =>
      _hash ?? (throw StateError('Sink is not closed'));
}

/// [chunk] from [start] to [end] as a [Uint8List], without copying one.
Uint8List _slice(List<int> chunk, int start, int end) => chunk is Uint8List
    ? Uint8List.sublistView(chunk, start, end)
    : Uint8List.fromList(chunk.sublist(start, end));

final class _Hmac extends Hmac {
  _Hmac(this.hashAlgorithm)
    : _algorithm = _hmacOf(hashAlgorithm),
      super.constructor();

  @override
  final HashAlgorithm hashAlgorithm;

  final rind.HmacAlgorithm _algorithm;

  @override
  Future<Mac> calculateMac(
    List<int> bytes, {
    required SecretKey secretKey,
    List<int> nonce = const <int>[],
    List<int> aad = const <int>[],
  }) async {
    _checkNoAad(aad);
    final key = rind.HmacKey(
      _algorithm,
      _bytes(await secretKey.extractBytes()),
    );
    return Mac(key.sign(_bytes(bytes)));
  }

  @override
  Future<MacSink> newMacSink({
    required SecretKey secretKey,
    List<int> nonce = const <int>[],
    List<int> aad = const <int>[],
  }) async {
    _checkNoAad(aad);
    final key = rind.HmacKey(
      _algorithm,
      _bytes(await secretKey.extractBytes()),
    );
    return _HmacSink(rind.HmacContext(key));
  }

  static void _checkNoAad(List<int> aad) {
    if (aad.isNotEmpty) {
      throw ArgumentError.value(aad, 'aad', 'AAD is not supported by HMAC');
    }
  }
}

final class _HmacSink extends MacSink {
  _HmacSink(this._context);

  final rind.HmacContext _context;
  Mac? _mac;

  @override
  bool get isClosed => _mac != null;

  @override
  void addSlice(List<int> chunk, int start, int end, bool isLast) {
    if (isClosed) throw StateError('Sink is closed');
    end = RangeError.checkValidRange(start, end, chunk.length);
    _context.update(_slice(chunk, start, end));
    if (isLast) _mac = Mac(_context.sign());
  }

  @override
  Future<Mac> mac() async => _mac ?? (throw StateError('Sink is not closed'));
}
