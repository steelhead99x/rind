// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

part of 'cryptography.dart';

// The DER rind's RSA keys load from and export to, with the package's RSA key
// pairs held as integers.

const _derInteger = 0x02;
const _derOctetString = 0x04;
const _derSequence = 0x30;

/// A DER element of [tag] holding [content].
Uint8List _der(int tag, List<int> content) {
  final length = content.length;
  final header = <int>[tag];
  if (length < 0x80) {
    header.add(length);
  } else {
    final bytes = <int>[];
    for (var n = length; n > 0; n >>= 8) {
      bytes.insert(0, n & 0xff);
    }
    header
      ..add(0x80 | bytes.length)
      ..addAll(bytes);
  }
  return Uint8List(header.length + length)
    ..setAll(0, header)
    ..setAll(header.length, content);
}

/// A DER SEQUENCE of [elements].
Uint8List _derSequenceOf(List<Uint8List> elements) =>
    _der(_derSequence, [for (final e in elements) ...e]);

/// The DER INTEGER of the unsigned big-endian [value].
Uint8List _derUnsigned(List<int> value) {
  var start = 0;
  while (start < value.length - 1 && value[start] == 0) {
    start++;
  }
  final digits = value.sublist(start);
  if (digits.isEmpty) return _der(_derInteger, [0]);
  return _der(_derInteger, [if (digits[0] & 0x80 != 0) 0, ...digits]);
}

/// Reads DER elements one after another, refusing anything malformed.
final class _DerReader {
  _DerReader(this._bytes);

  final Uint8List _bytes;
  int _offset = 0;

  bool get isEmpty => _offset == _bytes.length;

  /// The content of the next element, which must have [tag].
  Uint8List read(int tag) {
    if (_offset + 2 > _bytes.length || _bytes[_offset] != tag) {
      throw const FormatException('Malformed DER');
    }
    var length = _bytes[_offset + 1];
    _offset += 2;
    if (length & 0x80 != 0) {
      final count = length & 0x7f;
      if (count == 0 || count > 3 || _offset + count > _bytes.length) {
        throw const FormatException('Malformed DER');
      }
      length = 0;
      for (var i = 0; i < count; i++) {
        length = length << 8 | _bytes[_offset++];
      }
    }
    if (_offset + length > _bytes.length) {
      throw const FormatException('Malformed DER');
    }
    final content = Uint8List.sublistView(_bytes, _offset, _offset + length);
    _offset += length;
    return content;
  }

  /// The next element, a non-negative INTEGER, as unsigned big-endian bytes
  /// without leading zeros.
  Uint8List unsigned() {
    final content = read(_derInteger);
    if (content.isEmpty || content[0] & 0x80 != 0) {
      throw const FormatException('Malformed DER');
    }
    var start = 0;
    while (start < content.length - 1 && content[start] == 0) {
      start++;
    }
    return Uint8List.fromList(Uint8List.sublistView(content, start));
  }
}
