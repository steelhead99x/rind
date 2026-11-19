// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// Bundles rind's library for the target the Dart or Flutter build asks for as
// this package's code asset: the prebuilt library `hook/prebuilt.json` pins by
// SHA-256, downloaded from this version's GitHub release, or, with the
// `build_from_source` user-define, the `rind-dart` crate beside this package
// built with cargo. A target rind has no backend for fails here rather than at
// run time.

import 'dart:convert';
import 'dart:io';
import 'dart:typed_data';

import 'package:code_assets/code_assets.dart';
import 'package:crypto/crypto.dart' as crypto;
import 'package:hooks/hooks.dart';

void main(List<String> args) async {
  await build(args, (input, output) async {
    if (!input.config.buildCodeAssets) return;
    final code = input.config.code;
    if (code.linkModePreference == LinkModePreference.static) {
      throw UnsupportedError('rind builds only a dynamic library');
    }

    final target = rustTarget(code);
    final fromSource = input.userDefines['build_from_source'];
    if (fromSource is! bool?) {
      throw const FormatException(
        'hooks.user_defines.rind.build_from_source must be true or false',
      );
    }
    final library = fromSource == true
        ? await _buildFromSource(input, output, target)
        : await _download(input, output, target);
    output.assets.code.add(
      CodeAsset(
        package: input.packageName,
        name: 'src/bindings.dart',
        linkMode: DynamicLoadingBundled(),
        file: library,
      ),
    );
  });
}

/// Downloads [target]'s pinned library into the hook's shared output
/// directory, where later builds reuse it.
Future<Uri> _download(
  BuildInput input,
  BuildOutputBuilder output,
  String target,
) async {
  final manifest = File.fromUri(
    input.packageRoot.resolve('hook/prebuilt.json'),
  );
  if (!manifest.existsSync()) {
    throw UnsupportedError(
      'only a released rind pins prebuilt libraries; build this one from '
      'source by setting hooks.user_defines.rind.build_from_source to true in '
      'your pubspec.yaml',
    );
  }
  output.dependencies.add(manifest.uri);
  final pin = (jsonDecode(manifest.readAsStringSync()) as Map)[target];
  if (pin is! Map) {
    throw UnsupportedError(
      'this rind release pins no prebuilt library for $target',
    );
  }
  final sha256 = pin['sha256'] as String;
  final library = input.outputDirectoryShared.resolve(
    'prebuilt/$sha256/${input.config.code.targetOS.dylibFileName('rind_dart')}',
  );
  await fetchLibrary(
    Uri.parse(pin['url'] as String),
    sha256: sha256,
    size: pin['size'] as int,
    file: File.fromUri(library),
  );
  return library;
}

/// Downloads [url] to [file] unless [file] already holds it, refusing a
/// download whose length or SHA-256 is not the pinned one.
Future<void> fetchLibrary(
  Uri url, {
  required String sha256,
  required int size,
  required File file,
}) async {
  if (file.existsSync() &&
      crypto.sha256.convert(file.readAsBytesSync()).toString() == sha256) {
    return;
  }

  final client = HttpClient()..findProxy = HttpClient.findProxyFromEnvironment;
  final Uint8List bytes;
  try {
    final response = await (await client.getUrl(url)).close();
    if (response.statusCode != HttpStatus.ok) {
      throw HttpException(
        'downloading rind answered ${response.statusCode}',
        uri: url,
      );
    }
    // The pinned length bounds what the server can make the hook hold.
    final builder = BytesBuilder(copy: false);
    await for (final chunk in response) {
      if (builder.length + chunk.length > size) {
        throw StateError('$url is longer than the library this package pins');
      }
      builder.add(chunk);
    }
    bytes = builder.takeBytes();
  } finally {
    client.close(force: true);
  }
  if (bytes.length != size ||
      crypto.sha256.convert(bytes).toString() != sha256) {
    throw StateError('$url is not the library this package pins');
  }

  // Renamed into place, so an interrupted build never leaves a partial file.
  file.parent.createSync(recursive: true);
  File('${file.path}.partial')
    ..writeAsBytesSync(bytes)
    ..renameSync(file.path);
}

/// Builds the `rind-dart` crate beside this package for [target] with cargo,
/// listing the files it read as the build's dependencies.
Future<Uri> _buildFromSource(
  BuildInput input,
  BuildOutputBuilder output,
  String target,
) async {
  final code = input.config.code;
  final manifest = input.packageRoot.resolve('Cargo.toml');
  // The `cargo_target_dir` user-define shares one cargo target directory
  // between builds whose hook output folders differ, so the later ones
  // rebuild nothing; cargo locks it against concurrent builds.
  final sharedTargetDir = input.userDefines.path('cargo_target_dir');
  final targetDir = sharedTargetDir == null
      ? input.outputDirectoryShared.resolve('target/')
      : Directory.fromUri(sharedTargetDir).uri;
  final env = <String, String>{};
  final linkArgs = <String>[];

  switch (code.targetOS) {
    case OS.android:
      // The NDK's clang links, for the app's minimum API level.
      final clang = code.cCompiler?.compiler;
      if (clang == null) {
        throw UnsupportedError('building rind for Android needs the NDK');
      }
      final api = code.android.targetNdkApi;
      final clangTarget = target.replaceFirst('armv7-', 'armv7a-');
      linkArgs
        ..add('-Clinker=${clang.toFilePath()}')
        ..add('-Clink-arg=--target=$clangTarget$api')
        // Android 15 devices may use 16 KB pages, which Google Play
        // requires apps to support.
        ..add('-Clink-arg=-Wl,-z,max-page-size=16384');
    case OS.iOS:
      final version = code.iOS.deploymentVersion;
      env['IPHONEOS_DEPLOYMENT_TARGET'] = '${version.major}.${version.minor}';
    case OS.macOS:
      final version = code.macOS.deploymentVersion;
      env['MACOSX_DEPLOYMENT_TARGET'] = '${version.major}.${version.minor}';
  }

  await _checkTargetInstalled(target);
  final cargo = await Process.run('cargo', [
    'rustc',
    '--release',
    '--locked',
    '--lib',
    '--manifest-path',
    manifest.toFilePath(),
    '--target',
    target,
    '--target-dir',
    targetDir.toFilePath(),
    if (linkArgs.isNotEmpty) ...['--', ...linkArgs],
  ], environment: env);
  if (cargo.exitCode != 0) {
    throw ProcessException(
      'cargo',
      const [],
      'building rind for $target failed:\n${cargo.stderr}',
      cargo.exitCode,
    );
  }

  final outDir = targetDir.resolve('$target/release/');
  final library = outDir.resolve(code.targetOS.dylibFileName('rind_dart'));

  // Cargo lists every source file the library depends on beside it.
  final depInfo = outDir.resolve(
    code.targetOS
        .dylibFileName('rind_dart')
        .replaceFirst(RegExp(r'\.[^.]+$'), '.d'),
  );
  // Its lockfile and manifest, the workspace's in this repository and the
  // package's own once published, pick the dependencies' versions.
  final workspace = await Process.run('cargo', [
    'locate-project',
    '--workspace',
    '--message-format',
    'plain',
    '--manifest-path',
    manifest.toFilePath(),
  ]);
  if (workspace.exitCode != 0) {
    throw ProcessException(
      'cargo',
      const ['locate-project'],
      '${workspace.stderr}',
      workspace.exitCode,
    );
  }
  final workspaceManifest = Uri.file((workspace.stdout as String).trim());
  output.dependencies
    ..add(manifest)
    ..add(workspaceManifest)
    ..add(workspaceManifest.resolve('Cargo.lock'))
    ..addAll(_parseDepInfo(await _readDepInfo(File.fromUri(depInfo))));
  return library;
}

/// The Rust target triple for [code]'s target, refusing one rind lacks.
String rustTarget(CodeConfig code) {
  final arch = code.targetArchitecture;
  final os = code.targetOS;
  final triple = switch ((os, arch)) {
    (OS.android, Architecture.arm64) => 'aarch64-linux-android',
    (OS.android, Architecture.arm) => 'armv7-linux-androideabi',
    (OS.android, Architecture.x64) => 'x86_64-linux-android',
    (OS.iOS, Architecture.arm64) =>
      code.iOS.targetSdk == IOSSdk.iPhoneSimulator
          ? 'aarch64-apple-ios-sim'
          : 'aarch64-apple-ios',
    (OS.iOS, Architecture.x64) => 'x86_64-apple-ios',
    (OS.macOS, Architecture.arm64) => 'aarch64-apple-darwin',
    (OS.macOS, Architecture.x64) => 'x86_64-apple-darwin',
    (OS.linux, Architecture.arm64) => 'aarch64-unknown-linux-gnu',
    (OS.linux, Architecture.arm) => 'armv7-unknown-linux-gnueabihf',
    (OS.linux, Architecture.x64) => 'x86_64-unknown-linux-gnu',
    (OS.windows, Architecture.arm64) => 'aarch64-pc-windows-msvc',
    (OS.windows, Architecture.x64) => 'x86_64-pc-windows-msvc',
    _ => null,
  };
  if (triple == null) {
    throw UnsupportedError('rind does not support $os on $arch');
  }
  return triple;
}

/// Fails with the command that installs [target]'s standard library, which
/// cargo would otherwise report as a missing `core` crate.
Future<void> _checkTargetInstalled(String target) async {
  final ProcessResult sysroot;
  try {
    sysroot = await Process.run('rustc', ['--print', 'sysroot']);
  } on ProcessException {
    throw UnsupportedError(
      'building rind needs Rust 1.90 or later; install it from https://rustup.rs',
    );
  }
  final lib = Directory(
    '${(sysroot.stdout as String).trim()}/lib/rustlib/$target',
  );
  if (!lib.existsSync()) {
    throw UnsupportedError(
      "Rust's standard library for $target is not installed; "
      'run `rustup target add $target`',
    );
  }
}

/// [file]'s text once it holds a whole rule. Every cargo run rewrites the
/// dep-info beside the library, and outside cargo's lock, so a build that
/// shares the target directory through `cargo_target_dir` can read it while
/// another build has it truncated, or has removed it to write it afresh, so
/// a missing file waits as a truncated one does.
Future<String> _readDepInfo(File file) async {
  for (var attempt = 0; ; attempt++) {
    String text;
    try {
      text = file.readAsStringSync();
    } on PathNotFoundException {
      text = '';
    }
    if (text.split('\n').first.contains(': ') && text.endsWith('\n')) {
      return text;
    }
    if (attempt == 50) {
      throw FormatException('cargo left no dependency rule in ${file.path}');
    }
    await Future<void>.delayed(const Duration(milliseconds: 100));
  }
}

/// The files a Makefile-style dep-info file lists, in which a backslash
/// escapes a space in a path.
Iterable<Uri> _parseDepInfo(String depInfo) sync* {
  final rule = depInfo.split('\n').first;
  final colon = rule.indexOf(': ');
  if (colon < 0) throw FormatException('no dependency rule', rule);
  final deps = rule.substring(colon + 2);
  for (final path in deps.split(RegExp(r'(?<!\\) '))) {
    if (path.isNotEmpty) yield Uri.file(path.replaceAll(r'\ ', ' '));
  }
}
