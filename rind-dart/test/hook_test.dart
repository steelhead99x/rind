// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import 'dart:io';

import 'package:code_assets/code_assets.dart';
import 'package:crypto/crypto.dart' as crypto;
import 'package:hooks/hooks.dart';
import 'package:test/test.dart';

import '../hook/build.dart' as hook;

final fromSource = PackageUserDefines(
  workspacePubspec: PackageUserDefinesSource(
    defines: {'build_from_source': true},
    basePath: Directory.current.uri,
  ),
);

// Only a released package, as sh/dart-package.sh and sh/dart-prebuilt.sh
// stage it, pins prebuilt libraries.
final released = File('hook/prebuilt.json').existsSync();

/// Every target rind supports, as `os-arch[-iossdk]`.
const supported = [
  'android-arm64',
  'android-arm',
  'android-x64',
  'ios-arm64-iphoneos',
  'ios-arm64-iphonesimulator',
  'ios-x64-iphonesimulator',
  'macos-arm64',
  'macos-x64',
  'linux-arm64',
  'linux-arm',
  'linux-x64',
  'windows-arm64',
  'windows-x64',
];

void main() {
  // A cold build on a slow runner, such as macos-15-intel, outlasts the
  // default 30 seconds.
  test('builds from source for the host, listing its sources', () async {
    await testCodeBuildHook(
      mainMethod: hook.main,
      userDefines: fromSource,
      check: (input, output) {
        expect(output.assets.code.single.file, isNotNull);
        expect(
          output.dependencies,
          containsAll([
            input.packageRoot.resolve('src/lib.rs'),
            isA<Uri>().having(
              (uri) => uri.path,
              'path',
              endsWith('/Cargo.lock'),
            ),
          ]),
        );
      },
    );
  }, timeout: const Timeout(Duration(minutes: 5)));

  test('refuses to download in an unreleased copy', () async {
    await expectLater(
      testCodeBuildHook(mainMethod: hook.main, check: (_, _) {}),
      throwsUnsupportedError,
    );
  }, skip: released ? 'this copy is released' : false);

  // testCodeBuildHook checks each library is for its target's architecture.
  for (final target in supported) {
    test(
      'downloads the library for $target',
      () => _testTarget(target),
      skip: released ? false : 'only a released copy pins libraries',
    );
  }

  final refused = {
    'Android on ia32': (OS.android, Architecture.ia32),
    'Linux on riscv64': (OS.linux, Architecture.riscv64),
    'Fuchsia': (OS.fuchsia, Architecture.arm64),
  };
  refused.forEach((name, target) {
    test('refuses $name', () async {
      await expectLater(
        testCodeBuildHook(
          mainMethod: hook.main,
          targetOS: target.$1,
          targetArchitecture: target.$2,
          check: (_, _) {},
        ),
        throwsUnsupportedError,
      );
    });
  });

  test('refuses static linking', () async {
    await expectLater(
      testCodeBuildHook(
        mainMethod: hook.main,
        linkModePreference: LinkModePreference.static,
        check: (_, _) {},
      ),
      throwsUnsupportedError,
    );
  });

  group('fetchLibrary', () {
    final library = List.generate(1000, (i) => i % 251);
    final sha256 = crypto.sha256.convert(library).toString();
    late HttpServer server;
    late Uri url;
    late Directory dir;
    setUp(() async {
      server = await HttpServer.bind(InternetAddress.loopbackIPv4, 0);
      server.listen((request) {
        final body = switch (request.uri.path) {
          '/library' => library,
          '/longer' => [...library, 0],
          _ => [...library]..[0] ^= 1,
        };
        request.response
          ..add(body)
          ..close();
      });
      url = Uri.http('127.0.0.1:${server.port}');
      dir = await Directory.systemTemp.createTemp();
    });
    tearDown(() async {
      await server.close(force: true);
      await dir.delete(recursive: true);
    });

    test('downloads the pinned library, then reuses it', () async {
      final file = File('${dir.path}/library');
      await hook.fetchLibrary(
        url.resolve('/library'),
        sha256: sha256,
        size: library.length,
        file: file,
      );
      expect(file.readAsBytesSync(), library);
      await server.close(force: true);
      await hook.fetchLibrary(
        url.resolve('/library'),
        sha256: sha256,
        size: library.length,
        file: file,
      );
    });

    for (final path in ['/altered', '/longer']) {
      test('refuses $path', () async {
        final file = File('${dir.path}/library');
        await expectLater(
          hook.fetchLibrary(
            url.resolve(path),
            sha256: sha256,
            size: library.length,
            file: file,
          ),
          throwsStateError,
        );
        expect(file.existsSync(), isFalse);
      });
    }
  });

  // Cross builds, which need each target's Rust standard library and, for
  // Android, the NDK; CI's build workflow sets these.
  final targets = Platform.environment['RIND_DART_CROSS_TARGETS'] ?? '';
  for (final target
      in targets.isEmpty ? const <String>[] : targets.split(',')) {
    test(
      'builds from source for $target',
      () => _testTarget(target, userDefines: fromSource),
      // android-arm's cross compile exceeds the 30s default; the host
      // build above already allows five minutes for the same hook.
      timeout: const Timeout(Duration(minutes: 5)),
    );
  }
}

/// Runs the hook for [target], given as `os-arch[-iossdk]`.
Future<void> _testTarget(
  String target, {
  PackageUserDefines? userDefines,
}) async {
  final [os, arch, ...sdk] = target.split('-');
  final targetOS = OS.fromString(os);
  final ndk = Platform.environment['ANDROID_NDK_HOME'];
  await testCodeBuildHook(
    mainMethod: hook.main,
    userDefines: userDefines,
    targetOS: targetOS,
    targetArchitecture: Architecture.fromString(arch),
    targetIOSSdk: sdk.isEmpty ? IOSSdk.iPhoneOS : IOSSdk.fromString(sdk.single),
    targetAndroidNdkApi: 21,
    cCompiler: userDefines != null && targetOS == OS.android
        ? _ndkClang(ndk!)
        : null,
    check: (input, output) {},
  );
}

CCompilerConfig _ndkClang(String ndk) {
  final host = Platform.isMacOS ? 'darwin-x86_64' : 'linux-x86_64';
  final bin = Uri.directory('$ndk/toolchains/llvm/prebuilt/$host/bin');
  return CCompilerConfig(
    compiler: bin.resolve('clang'),
    linker: bin.resolve('ld.lld'),
    archiver: bin.resolve('llvm-ar'),
  );
}
