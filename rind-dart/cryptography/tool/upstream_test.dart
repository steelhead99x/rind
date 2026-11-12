// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// Runs the cryptography package's own test suite, from the release pub
// resolved, on RindCryptography: a copy whose every Cryptography instance is
// RindCryptography, skipping the files and tests compat/cryptography.txt
// lists as needing what rind lacks.
//
// Usage, from the package root: dart run tool/upstream_test.dart [ARGS...]

import 'dart:convert';
import 'dart:io';

Future<void> main(List<String> args) async {
  final root = Directory.current;
  final upstream = Directory.fromUri(
    (await _packageRoot(root, 'cryptography')).resolve('test/'),
  );
  final out = Directory('${root.path}/.dart_tool/upstream_test');
  if (out.existsSync()) out.deleteSync(recursive: true);

  final skippedFiles = <String>{};
  final skippedTests = <String>[];
  for (final line in File(
    '${root.path}/compat/cryptography.txt',
  ).readAsLinesSync()) {
    if (line.isEmpty || line.startsWith('#')) continue;
    (line.endsWith('_test.dart') ? skippedFiles.add : skippedTests.add)(line);
  }

  var copied = 0;
  for (final entity in upstream.listSync(recursive: true)) {
    if (entity is! File || !entity.path.endsWith('.dart')) continue;
    final path = entity.path.substring(upstream.path.length);
    if (skippedFiles.remove(path)) continue;
    File('${out.path}/$path')
      ..createSync(recursive: true)
      ..writeAsStringSync(_rewrite(entity.readAsStringSync()));
    copied++;
  }
  if (skippedFiles.isNotEmpty) {
    _fail('compat/cryptography.txt lists missing files: $skippedFiles');
  }
  if (copied == 0) _fail('found no tests in ${upstream.path}');

  // Every test but the skipped ones, by full name.
  final names = skippedTests.map(RegExp.escape).join('|');
  final test = await Process.start(
    Platform.resolvedExecutable,
    [
      'test',
      if (names.isNotEmpty) ...['--name', '^(?!(?:$names)\$)'],
      ...args,
      out.path,
    ],
    workingDirectory: root.path,
    mode: ProcessStartMode.inheritStdio,
  );
  exitCode = await test.exitCode;
}

/// [source] with RindCryptography as its every Cryptography instance, its
/// tests of WebCrypto's algorithms, which run only in Chrome, run on it too,
/// and its BrowserCryptography groups skipped where they repeat its
/// DartCryptography ones.
String _rewrite(String source) {
  if (source.contains("group('DartCryptography:', () {")) {
    source = source.replaceAll(
      "group('BrowserCryptography:', () {",
      "group('BrowserCryptography:', skip: 'repeats DartCryptography', () {",
    );
  }
  return source
      .replaceAll(", testOn: 'chrome'", '')
      .replaceAll(
        RegExp(r'(Dart|Browser)Cryptography\.defaultInstance'),
        'RindCryptography()',
      )
      .replaceAll(
        RegExp(r'(Dart|Browser)Cryptography\(random: random\)'),
        'RindCryptography(random: random)',
      )
      .replaceFirst(
        RegExp(r'^void main\(\) \{$', multiLine: true),
        'void main() {\n  Cryptography.instance = RindCryptography();',
      )
      .replaceFirst(
        RegExp(r'^import ', multiLine: true),
        "import 'package:cryptography/cryptography.dart';\n"
        "import 'package:rind_cryptography/rind_cryptography.dart';\n"
        'import ',
      );
}

/// The root of [package], as pub resolved it for the package at [root].
Future<Uri> _packageRoot(Directory root, String package) async {
  final file = File('${root.path}/.dart_tool/package_config.json');
  final config = jsonDecode(await file.readAsString()) as Map<String, Object?>;
  for (final entry in config['packages'] as List<Object?>) {
    final map = entry as Map<String, Object?>;
    if (map['name'] == package) {
      final uri = file.uri.resolve(map['rootUri'] as String);
      return uri.path.endsWith('/') ? uri : Uri.parse('$uri/');
    }
  }
  _fail('pub resolved no $package package');
}

Never _fail(String message) {
  stderr.writeln('upstream_test: $message');
  exit(1);
}
