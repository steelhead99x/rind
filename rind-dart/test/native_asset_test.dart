// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import 'dart:io';

import 'package:rind/src/status.dart';
import 'package:test/test.dart';

void main() {
  test('every @Native resolves against the registered code asset', () {
    final registered = _hookAssetId();
    expect(nativeAssetId, registered, reason: 'hook/build.dart');
    final separator = RegExp(r'[/\\]');
    final nativeLibraries = <String>[];
    for (final file in Directory(
      'lib',
    ).listSync(recursive: true).whereType<File>()) {
      if (!file.path.endsWith('.dart')) continue;
      final text = file.readAsStringSync();
      if (!text.contains('@Native')) continue;
      final library = _libraryFile(file, text);
      nativeLibraries.add(library.path);
      expect(
        _defaultAssetArgument(library),
        'nativeAssetId',
        reason:
            '${file.path} points @Native at an asset the build hook '
            'does not register',
      );
      for (final id in _explicitAssetIds(text)) {
        expect(id, nativeAssetId, reason: file.path);
      }
    }
    expect(
      nativeLibraries.map((path) => path.split(separator).last).toSet(),
      containsAll([
        'bindings.dart',
        'ecdsa.dart',
        'ed25519.dart',
        'rsa.dart',
        'status.dart',
      ]),
    );
  });

  test(
    'a fresh process resolves each signature library on its first rind call',
    () async {
      const names = ['ed25519', 'ecdsa', 'rsa'];
      final results = await Future.wait([
        for (final name in names)
          Process.run(Platform.resolvedExecutable, [
            'test/first_call/$name.dart',
          ]),
      ]);
      for (var i = 0; i < names.length; i++) {
        final result = results[i];
        expect(
          result.exitCode,
          0,
          reason: '${names[i]}\n${result.stdout}\n${result.stderr}',
        );
      }
    },
    timeout: const Timeout(Duration(minutes: 3)),
  );
}

File _libraryFile(File file, String text) {
  final part = RegExp(
    r'''^part of ['"]([^'"]+)['"];''',
    multiLine: true,
  ).firstMatch(text);
  if (part == null) return file;
  return File('${file.parent.path}/${part.group(1)}');
}

// The asset id `hook/build.dart` registers: `package:<name>/<CodeAsset name>`.
String _hookAssetId() {
  final package = RegExp(
    r'^name:\s*(\S+)',
    multiLine: true,
  ).firstMatch(File('pubspec.yaml').readAsStringSync())!.group(1)!;
  final name = RegExp(
    r'''CodeAsset\(\s*package:\s*input\.packageName\s*,\s*name:\s*['"]([^'"]+)['"]''',
  ).firstMatch(File('hook/build.dart').readAsStringSync())!.group(1)!;
  return 'package:$package/$name';
}

// The argument of the library's @DefaultAsset. Every native library names
// [nativeAssetId], so the id string lives in one place.
String _defaultAssetArgument(File library) {
  final annotation = RegExp(
    r'''@DefaultAsset\(\s*([^\s)]+)\s*\)''',
  ).firstMatch(library.readAsStringSync());
  expect(annotation, isNotNull, reason: '${library.path} has no @DefaultAsset');
  return annotation!.group(1)!;
}

Iterable<String> _explicitAssetIds(String text) => RegExp(
  r'''assetId:\s*['"]([^'"]+)['"]''',
).allMatches(text).map((match) => match.group(1)!);
