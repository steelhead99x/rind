{
  description = "rind - pure-Rust cryptography for MoQ";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    # The quest CLI, which also serves the quest guide and skills the stubs in
    # .claude/skills call. Bump the rev to upgrade them.
    quest = {
      url = "github:moq-dev/quest";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
  };

  outputs =
    {
      nixpkgs,
      flake-utils,
      rust-overlay,
      quest,
      ...
    }:
    flake-utils.lib.eachSystem
      [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
      ]
      (
        system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ (import rust-overlay) ];
          };

          # Pinned build toolchain so `nix develop` and CI compile against the
          # same rustc. The workspace declares a lower floor (rust-version),
          # which `devShells.msrv` builds with. No rust-toolchain.toml: it
          # would override the nightly jobs' toolchains.
          rust-stable = pkgs.rust-bin.stable."1.98.1";
          # `just ci`'s check of the unstable style options in
          # .rustfmt.unstable.toml, which only a nightly rustfmt reads. Its own
          # name keeps the stable rustfmt the one `cargo fmt` runs.
          rustfmt-unstable = pkgs.writeShellScriptBin "rustfmt-unstable" ''
            exec ${
              pkgs.rust-bin.nightly."2025-02-14".minimal.override { extensions = [ "rustfmt" ]; }
            }/bin/rustfmt "$@"
          '';
          rust-toolchain = rust-stable.minimal.override {
            # `minimal` rather than `default`, which adds offline HTML docs to
            # a closure every CI job downloads.
            extensions = [
              "rustfmt"
              "clippy"
              "rust-src"
              "rust-analyzer"
            ];
            # The gate lints rind's other backends without their C toolchains,
            # the portable one forced on x86_64 and on wasm32.
            targets = [
              "aarch64-unknown-linux-gnu"
              "armv7-unknown-linux-gnueabihf"
              "wasm32-unknown-unknown"
              "wasm32-wasip2"
              "x86_64-unknown-linux-gnu"
            ];
          };

          quest-cli = quest.packages.${system}.default;

          timing-shell = {
            packages = [
              rust-stable.minimal
              # admin/timing finds the binary cargo built.
              pkgs.jq
            ]
            # taskset pins the tests to one core.
            ++ pkgs.lib.optionals pkgs.stdenv.hostPlatform.isLinux [ pkgs.util-linux ];
          };

          # rind itself builds for armv7 without C. Only its tests need this
          # ARM C toolchain, for the aws-lc-rs dev-dependency they check
          # against, so it lives in `devShells.armv7` and nothing rind ships
          # links it.
          armv7-cc = pkgs.pkgsCross.armv7l-hf-multiplatform.stdenv.cc;
          armv7-prefix = "${armv7-cc}/bin/${armv7-cc.targetPrefix}";

          armv7-shell = {
            packages = [
              (rust-stable.minimal.override {
                extensions = [ "clippy" ];
                targets = [
                  "armv7-unknown-linux-gnueabihf"
                  "armv7-linux-androideabi"
                ];
              })
              armv7-cc
              pkgs.qemu-user
              # admin/mutants --target armv7-unknown-linux-gnueabihf.
              pkgs.cargo-mutants
              pkgs.cargo-nextest
            ];

            env = {
              CC_armv7_unknown_linux_gnueabihf = "${armv7-prefix}cc";
              CXX_armv7_unknown_linux_gnueabihf = "${armv7-prefix}c++";
              AR_armv7_unknown_linux_gnueabihf = "${armv7-prefix}ar";
              CARGO_TARGET_ARMV7_UNKNOWN_LINUX_GNUEABIHF_LINKER = "${armv7-prefix}cc";
              # The wrapper links against the store's armhf glibc by absolute
              # path, so qemu needs no sysroot.
              CARGO_TARGET_ARMV7_UNKNOWN_LINUX_GNUEABIHF_RUNNER = "qemu-arm";
            };
          };

          # A shell that builds `target`, a target with no rind assembly, and
          # runs its tests under qemu-user, as `just qemu` does, or natively
          # where the host can, as x86_64 runs i686. `cross` is the nixpkgs
          # cross set whose C toolchain the tests' aws-lc-rs dev-dependency
          # builds with; rind itself needs none. `cpu`, if set, is the core
          # qemu emulates, so it traps any newer instruction. `rustflags`, if
          # set, is passed to every build for `target`, its doctests included.
          qemu-shell =
            {
              target,
              cross,
              cpu ? null,
              rustflags ? null,
            }:
            let
              cc = cross.stdenv.cc;
              prefix = "${cc}/bin/${cc.targetPrefix}";
              var = pkgs.lib.toUpper (builtins.replaceStrings [ "-" ] [ "_" ] target);
              lower = builtins.replaceStrings [ "-" ] [ "_" ] target;
              native = pkgs.stdenv.hostPlatform.canExecute cross.stdenv.hostPlatform;
            in
            pkgs.mkShell {
              packages = [
                (rust-stable.minimal.override {
                  extensions = [ "clippy" ];
                  targets = [ target ];
                })
                cc
              ]
              ++ pkgs.lib.optional (!native) pkgs.qemu-user;

              env = {
                RIND_QEMU_TARGET = target;
                "CC_${lower}" = "${prefix}cc";
                "CXX_${lower}" = "${prefix}c++";
                "AR_${lower}" = "${prefix}ar";
                "CARGO_TARGET_${var}_LINKER" = "${prefix}cc";
              }
              # The wrapper links against the store's glibc for the target by
              # absolute path, so neither qemu nor the host needs a sysroot.
              // pkgs.lib.optionalAttrs (!native) {
                "CARGO_TARGET_${var}_RUNNER" = "qemu-${cross.stdenv.hostPlatform.qemuArch}";
              }
              // pkgs.lib.optionalAttrs (cpu != null) { QEMU_CPU = cpu; }
              // pkgs.lib.optionalAttrs (rustflags != null) {
                "CARGO_TARGET_${var}_RUSTFLAGS" = rustflags;
                # Cargo hands rustdoc, which links the doctests, only these.
                RUSTDOCFLAGS = rustflags;
              };
            };

          # The tracer `admin/ct-qemu` loads into qemu-arm or qemu-aarch64,
          # built against the plugin API of the qemu-user its shells run.
          ct-qemu-plugin = pkgs.stdenv.mkDerivation {
            name = "ct-qemu-plugin";
            src = ./admin/ct-qemu-plugin.c;
            dontUnpack = true;
            nativeBuildInputs = [ pkgs.pkg-config ];
            buildInputs = [ pkgs.glib ];
            buildPhase = ''
              $CC -O2 -shared -fPIC -Wall -Werror -I${pkgs.qemu-user}/include \
                $(pkg-config --cflags glib-2.0) -o ct-qemu-plugin.so $src
            '';
            installPhase = "install -D ct-qemu-plugin.so $out/lib/ct-qemu-plugin.so";
          };

          # Intel SDE, which `x86-cpu.yml`, `coverage.yml`, `admin/x86-cpu`,
          # and `admin/ct-sde` run to emulate Intel CPU models. Its license allows use and
          # redistribution only unmodified, so its 64-bit launcher runs as
          # shipped in an FHS sandbox for its /lib64 loader, rather than
          # patched for Nix. The kit's `sde` launcher is 32-bit; `sde64` takes
          # the same arguments.
          # Ubuntu's AppArmor denies the sandbox its user namespace until
          # `kernel.apparmor_restrict_unprivileged_userns=0`, as the workflows set.
          sde = pkgs.buildFHSEnv {
            name = "sde";
            runScript = "${
              pkgs.fetchFromGitHub {
                owner = "ctz";
                repo = "intel-sde";
                # SDE 9.53.0.
                rev = "1e06cc8cf49bb3b9004737e4f69bcf12f80e0bca";
                hash = "sha256-KjemFD8imYo22rlnfKQbRPfmuMdVNaljqQSwyQxzo90=";
              }
            }/sde64";
          };

          # BINSEC, whose checkct plugin `admin/ct-binsec` runs, built from
          # its release with the decoders it takes from unisim-archisec and
          # the Bitwuzla solver it links. nixpkgs packages neither BINSEC nor
          # its `mula` dependency. BINSEC loads its plugins through findlib,
          # so the wrapper points OCAMLPATH at its own.
          binsec =
            let
              ocaml = pkgs.ocamlPackages;
              mula = ocaml.buildDunePackage rec {
                pname = "mula";
                version = "0.1.2";
                src = pkgs.fetchurl {
                  url = "https://github.com/ifazk/mula/releases/download/${version}/mula-${version}.tbz";
                  hash = "sha256-Hw7kKspz4zRZeWuqJgY7+C0pDLb0xyPT58mg5Y8eDXI=";
                };
              };
            in
            ocaml.buildDunePackage rec {
              pname = "binsec";
              version = "0.11.3";
              src = pkgs.fetchurl {
                url = "https://github.com/binsec/binsec/releases/download/${version}/binsec-${version}.tbz";
                hash = "sha256-k/b+Q51IaxZgYu9t2SxM46oJR7Xhixw6p94vwwA6ptk=";
              };
              nativeBuildInputs = [
                ocaml.menhir
                ocaml.dypgen
                pkgs.makeWrapper
              ];
              # Its parser generator, which is also a library BINSEC links.
              buildInputs = [ ocaml.dypgen ];
              propagatedBuildInputs = [
                ocaml.ocamlgraph
                ocaml.zarith
                ocaml.dune-site
                ocaml.toml
                mula
                ocaml.unisim_archisec
                ocaml.bitwuzla-cxx
              ];
              postInstall = ''
                wrapProgram $out/bin/binsec \
                  --prefix OCAMLPATH : $out/lib/ocaml/${ocaml.ocaml.version}/site-lib
              '';
            };

          # `admin/parse-asm` calls cpp, as, and objdump by their Debian names,
          # as s2n-bignum's Makefiles do. Each maps to the target's tools,
          # native where the host matches, so the disassembly it reads can't
          # change unless nixpkgs does.
          debian-cross-tools =
            let
              link = arch: cross: ''
                ln -s ${cross.stdenv.cc.cc}/bin/${cross.stdenv.cc.targetPrefix}cpp $out/bin/${arch}-linux-gnu-cpp
                for tool in as objdump; do
                  ln -s ${cross.stdenv.cc.bintools.bintools}/bin/${cross.stdenv.cc.targetPrefix}$tool $out/bin/${arch}-linux-gnu-$tool
                done
              '';
            in
            pkgs.runCommand "debian-cross-tools" { } ''
              mkdir -p $out/bin
              ${link "x86_64" pkgs.pkgsCross.gnu64}
              ${link "aarch64" pkgs.pkgsCross.aarch64-multiplatform}
            '';

          # Otherwise cargo exports the host's OpenSSL CA paths, which on
          # Ubuntu lie under the /usr the SDE sandbox replaces, and the tests
          # that load the system's roots find none. A shell hook, since `nix
          # develop` keeps the caller's SSL_CERT_FILE over `env`.
          # Charon and Aeneas, which `admin/prove` runs to translate rind's
          # Rust to Lean, from Aeneas's nightly release, which ships the two
          # built together. Bump the tag, both hashes, and `rust-charon` with
          # `proofs/lakefile.toml`'s Aeneas revision.
          aeneas-release = "nightly-2026.11.03-ab34bd2";
          aeneas-tarball = {
            x86_64-linux = {
              arch = "x86_64";
              hash = "sha256-7Q4zbFBtrTfk4cU/bMTW1ZWdfjr6sv1Vrq0oB3VlH14=";
            };
            aarch64-linux = {
              arch = "aarch64";
              hash = "sha256-010M/V6/mqFYvTEvLPOoB2ppHyewhgX2Zk39twWtF14=";
            };
          };

          # The nightly Charon's driver links against: its `rust-toolchain`.
          rust-charon = pkgs.rust-bin.nightly."2026-09-17".minimal.override {
            extensions = [
              "rustc-dev"
              "rust-src"
              "llvm-tools"
              "miri"
            ];
            targets = [
              "x86_64-unknown-linux-gnu"
              "aarch64-unknown-linux-gnu"
            ];
          };

          # The standard library with full MIR, which Charon reads, for the
          # targets `admin/prove` translates; as Charon's own flake builds it.
          charon-sysroots = pkgs.runCommand "charon-sysroots" { nativeBuildInputs = [ rust-charon ]; } ''
            export HOME=$NIX_BUILD_TOP/home CARGO_HOME=$NIX_BUILD_TOP/cargo CARGO_NET_OFFLINE=true
            mkdir -p $HOME $CARGO_HOME
            cat > $CARGO_HOME/config.toml <<END
            [source.crates-io]
            replace-with = "vendored-sources"
            [source.vendored-sources]
            directory = "$(rustc --print sysroot)/lib/rustlib/src/rust/library/vendor"
            END
            for target in x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu; do
              sysroot=$(cargo miri setup --target=$target --print-sysroot)
            done
            mkdir -p $out
            cp -a $sysroot/. $out/
          '';

          aeneas = pkgs.stdenv.mkDerivation {
            pname = "aeneas";
            version = aeneas-release;
            src = pkgs.fetchurl {
              url = "https://github.com/AeneasVerif/aeneas/releases/download/${aeneas-release}/aeneas-linux-${aeneas-tarball.${system}.arch}.tar.gz";
              inherit (aeneas-tarball.${system}) hash;
            };
            sourceRoot = ".";
            unpackCmd = "tar xzf $curSrc aeneas charon charon-driver";
            nativeBuildInputs = [
              pkgs.autoPatchelfHook
              pkgs.makeWrapper
            ];
            buildInputs = [
              rust-charon
              pkgs.stdenv.cc.cc.lib
            ];
            installPhase = ''
              install -Dm755 -t $out/bin aeneas charon charon-driver
              wrapProgram $out/bin/charon \
                --set CHARON_TOOLCHAIN_IS_IN_PATH 1 \
                --set CHARON_MIRI_SYSROOTS ${charon-sysroots} \
                --prefix PATH : ${rust-charon}/bin
            '';
          };

          # `admin/prove hol-light` and `admin/prove bytes` run in it: HOL
          # Light, the OCaml it compiles the proofs with, as s2n-bignum's
          # `tools/build-proof.sh` does, the Rust whose build emits the object
          # code they are of, with llvm-objdump to read it, the Python that
          # compares that code with the code upstream's proofs check, and the
          # cross tools that assemble Vale's and aws-lc's.
          hol-light = pkgs.mkShell {
            packages = [
              (rust-stable.minimal.override {
                extensions = [ "llvm-tools" ];
                targets = [
                  "x86_64-unknown-linux-gnu"
                  "aarch64-unknown-linux-gnu"
                ];
              })
              pkgs.hol_light
              pkgs.ocamlPackages.ocaml
              pkgs.ocamlPackages.findlib
              pkgs.ocamlPackages.camlp5
              pkgs.git
              pkgs.python3
              debian-cross-tools
            ];
          };

          sde-certs = ''
            export SSL_CERT_FILE=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt
          '';
        in
        {
          devShells = {
            inherit hol-light;

            default = pkgs.mkShell {
              packages =
                with pkgs;
                [
                  rust-toolchain
                  just
                  git
                  jq
                  # aws-lc-rs (dev-dependency, the differential-test oracle),
                  # libfuzzer-sys, and the OpenSSL benchmarks build C.
                  cmake
                  pkg-config
                  openssl
                  cargo-deny
                  # admin/mutants and the mutants workflow.
                  cargo-mutants
                  cargo-nextest
                  cargo-semver-checks
                  # Linters used by `just check` and `just fix`, which skip a
                  # module whose tools aren't on $PATH. CI sets CI_STRICT=1, which
                  # turns that skip into an error (see sh/dispatch.sh).
                  shellcheck
                  actionlint
                  # sh/alert.sh reads the workflows.
                  yq-go
                  nixfmt
                  # admin/ scripts, and pyrind's tests and benchmarks: they
                  # check it against pyca/cryptography, and its type stubs
                  # with mypy's stubtest. pytest runs pyjwt's and joserfc's
                  # suites against pyrind-cryptography.
                  (python3.withPackages (ps: [
                    ps.cryptography
                    ps.mypy
                    ps.pytest
                  ]))
                  # Builds pyrind (rind-python).
                  maturin
                  # admin/bench-report-test runs the script that holds a
                  # leased host.
                  flock
                  cargo-modules
                  rustfmt-unstable
                  quest-cli
                ]
                ++ pkgs.lib.optionals (!pkgs.stdenv.hostPlatform.isDarwin) [
                  # Marked broken on Darwin in nixpkgs.
                  release-plz
                  # admin/ctgrind's constant-time checks.
                  valgrind
                ];

              # What sh/dispatch.sh checks before a scoped `just check` or `just
              # fix`. IN_NIX_SHELL would also pass inside another project's shell.
              env.IN_RIND_DEV_SHELL = "1";
              # The releases whose test suites `sh/python.sh compat` runs
              # against pyrind-cryptography, pinned with nixpkgs.
              env.PYJWT_SRC = pkgs.python3Packages.pyjwt.src;
              env.JOSERFC_SRC = pkgs.python3Packages.joserfc.src;
            };

            # dudect needs only Rust, without Marvin's Python and toolkit fetches.
            dudect = pkgs.mkShell timing-shell;

            # The Marvin toolkit's RSA ciphertexts, timed by rind-timing and
            # analysed by tlsfuzzer.
            timing = pkgs.mkShell {
              packages = timing-shell.packages ++ [
                (
                  (pkgs.python3.override {
                    packageOverrides = _: super: {
                      # nixpkgs marks python-ecdsa insecure for CVE-2024-23342,
                      # a timing leak in its own signing. tlsfuzzer and
                      # tlslite-ng only parse with it here.
                      ecdsa = super.ecdsa.overridePythonAttrs (old: {
                        meta = old.meta // {
                          knownVulnerabilities = [ ];
                        };
                      });
                      # The tlsfuzzer below needs this release's ML-DSA names.
                      tlslite-ng = super.tlslite-ng.overridePythonAttrs {
                        version = "0.9.0b2";
                        src = pkgs.fetchPypi {
                          pname = "tlslite_ng";
                          version = "0.9.0b2";
                          sha256 = "ff971e02061f17c43b46b41817c4627ba2765cc319e032e33bc4182c4d7091fb";
                        };
                      };
                    };
                  }).withPackages
                    (
                      p: with p; [
                        # tlsfuzzer's requirements-timing.txt, and what its
                        # extract.py and the toolkit's step2.py import.
                        numpy
                        scipy
                        pandas
                        matplotlib
                        ecdsa
                        dpkt
                        tlslite-ng
                      ]
                    )
                )
                # The Marvin keys and certificates.
                pkgs.openssl
              ];

              env = {
                MARVIN_TOOLKIT = pkgs.fetchFromGitHub {
                  owner = "tomato42";
                  repo = "marvin-toolkit";
                  rev = "7d264ab2b6611b25b95d5dd6bd1590a761c47048";
                  hash = "sha256-Y1SvbRTXyyixVOys2ookmqimLm/gdiTl1oFE1slyi1g=";
                };
                TLSFUZZER = pkgs.fetchFromGitHub {
                  owner = "tlsfuzzer";
                  repo = "tlsfuzzer";
                  rev = "5eebc4464e5197a7f7392fb9acda99cfc32441f7";
                  hash = "sha256-+8Lf1sbuu8D7fiWt6iyNgY5RZv3bKXbwuEZARj2NXPQ=";
                };
              };
            };

            # The nightly MSRV job builds in it. The workspace's rust-version
            # names a minor release, which resolves to its latest patch, as
            # rustup does. The extra targets let it check rind's other
            # backends and 32-bit x86, which `check` does without a C toolchain.
            msrv = pkgs.mkShell {
              packages = [
                (pkgs.rust-bin.fromRustupToolchain {
                  channel = (builtins.fromTOML (builtins.readFile ./Cargo.toml)).workspace.package.rust-version;
                  profile = "minimal";
                  targets = [
                    "aarch64-unknown-linux-gnu"
                    "armv7-unknown-linux-gnueabihf"
                    "i686-unknown-linux-gnu"
                  ];
                })
              ];
            };

            # The `dart` module of `just check` runs rind-dart's Dart package
            # in it. Its own shell, since the SDK would add over 200 MB to
            # the closure every CI job downloads.
            dart = pkgs.mkShell {
              packages = [
                rust-toolchain
                pkgs.dart
              ];
            };

            # `coverage.yml` runs `admin/coverage` in it. On x86_64 Linux it
            # adds `sde`, for the pass that covers the AVX-512 paths.
            coverage = pkgs.mkShell {
              packages = [
                (rust-stable.minimal.override { extensions = [ "llvm-tools" ]; })
                # Its tests build with nixpkgs' rustc, whose instrumented
                # binaries crash on exit, so the cache has no build. rind's
                # coverage builds with the toolchain above instead.
                (pkgs.cargo-llvm-cov.overrideAttrs { doCheck = false; })
                # aws-lc-rs builds C.
                pkgs.cmake
                pkgs.pkg-config
                pkgs.openssl
              ]
              ++ pkgs.lib.optionals (system == "x86_64-linux") [ sde ];

              shellHook = pkgs.lib.optionalString (system == "x86_64-linux") sde-certs;
            };

            # `just check` runs `admin/ct-vartime` in it: llvm-objdump, and the
            # standard library of each target it builds rind's rlib for.
            ct-vartime = pkgs.mkShell {
              packages = [
                (rust-stable.minimal.override {
                  extensions = [ "llvm-tools" ];
                  targets = [
                    "x86_64-unknown-linux-gnu"
                    "aarch64-unknown-linux-gnu"
                    "armv7-unknown-linux-gnueabihf"
                    "arm-unknown-linux-gnueabihf"
                    "i686-unknown-linux-gnu"
                    "loongarch64-unknown-linux-gnu"
                    "powerpc-unknown-linux-gnu"
                    "powerpc64-unknown-linux-gnu"
                    "powerpc64le-unknown-linux-gnu"
                    "riscv64gc-unknown-linux-gnu"
                    "s390x-unknown-linux-gnu"
                  ];
                })
                pkgs.python3
              ];
            };
          }
          # Linux only, since valgrind and qemu-user need a Linux host.
          // pkgs.lib.optionalAttrs pkgs.stdenv.hostPlatform.isLinux {
            # `admin/prove` and the prove workflow run in it. Linux only, as
            # Aeneas releases for it. Lake fetches the Lean toolchain that
            # `proofs/lean-toolchain` names, whose bundled `leantar` reads
            # Mathlib's cache, which nixpkgs' Lean cannot.
            prove = pkgs.mkShell {
              inputsFrom = [ hol-light ];
              packages = [
                aeneas
                pkgs.elan
                pkgs.git
                pkgs.curl
              ];
            };

            # `admin/ctgrind` and the ctgrind workflow run in it. A separate
            # shell because crabgrind's bindgen needs libclang, which no other
            # job does.
            ctgrind = pkgs.mkShell {
              packages = [
                rust-stable.minimal
                pkgs.valgrind
                # crabgrind finds valgrind's headers through it.
                pkgs.pkg-config
              ];

              env.LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
            };

            # `just wasm` runs the portable backend's tests on wasm32-wasip2
            # in it, under wasmtime. The toolchain is the default shell's,
            # which already carries the target.
            wasm = pkgs.mkShell {
              packages = [
                rust-toolchain
                pkgs.wasmtime
              ];
            };

            # `just miri` and the miri workflow run in it: Charon's nightly,
            # which already carries Miri, rather than a second nightly.
            miri = pkgs.mkShell {
              packages = [
                rust-charon
                pkgs.cargo-nextest
              ];
            };

            # `admin/regenerate` and the regenerate workflow run in it. A
            # separate shell because the aarch64 cross compiler, for its cpp,
            # adds about 500 MB.
            regenerate = pkgs.mkShell {
              packages = [
                (rust-stable.minimal.override { extensions = [ "rustfmt" ]; })
                pkgs.git
                pkgs.python3
                # OpenSSL's perlasm.
                pkgs.perl
                debian-cross-tools
              ];
            };

            # `just armv7` enters it to lint and test the armv7 build under
            # qemu, and the mutants workflow to mutate it. A separate shell
            # because the ARM C toolchain, qemu-user, and the armv7 standard
            # libraries add about 700 MB, which every other CI job would
            # download.
            armv7 = pkgs.mkShell armv7-shell;

            # `just qemu aarch64` tests the aarch64 build under qemu in it, and
            # `just check`'s cross module lints rind's tests for aarch64 in it,
            # where the aws-lc-rs dev-dependency needs an aarch64 C compiler.
            aarch64 = qemu-shell {
              target = "aarch64-unknown-linux-gnu";
              cross = pkgs.pkgsCross.aarch64-multiplatform;
            };

            # `just qemu s390x` tests the portable backend on big-endian
            # s390x in it.
            s390x = qemu-shell {
              target = "s390x-unknown-linux-gnu";
              cross = pkgs.pkgsCross.s390x;
            };

            # `just qemu i686` tests the portable backend on 32-bit x86 in it,
            # natively on an x86_64 host.
            i686 = qemu-shell {
              target = "i686-unknown-linux-gnu";
              cross = pkgs.pkgsCross.gnu32;
            };

            # `just qemu riscv64` and `just qemu riscv64-musl` test the
            # portable backend on riscv64gc Linux, glibc and musl, in them.
            riscv64 = qemu-shell {
              target = "riscv64gc-unknown-linux-gnu";
              cross = pkgs.pkgsCross.riscv64;
            };
            riscv64-musl = qemu-shell {
              target = "riscv64gc-unknown-linux-musl";
              cross = pkgs.pkgsCross.riscv64-musl;
            };

            # `just qemu loongarch64` tests the portable backend on
            # loongarch64 Linux in it.
            loongarch64 = qemu-shell {
              target = "loongarch64-unknown-linux-gnu";
              cross = pkgs.pkgsCross.loongarch64-linux;
            };

            # `just qemu armv6` and `just qemu armv6-softfloat` test the
            # portable backend on the ARM1176 of the Raspberry Pi 1 and Zero.
            # Rust builds `arm-unknown-linux-gnueabi` for ARMv6 too, and the
            # ARMv5TE glibc it links against runs there.
            armv6 = qemu-shell {
              target = "arm-unknown-linux-gnueabihf";
              cross = pkgs.pkgsCross.raspberryPi;
              cpu = "arm1176";
            };
            armv6-softfloat = qemu-shell {
              target = "arm-unknown-linux-gnueabi";
              cross = pkgs.pkgsCross.armv5tel-multiplatform;
              cpu = "arm1176";
            };

            # `just qemu powerpc64le`, `just qemu powerpc64`, and `just qemu
            # powerpc` test the portable backend on PowerPC Linux in them,
            # the last two big-endian. Rust's powerpc64 target uses the ELFv1
            # ABI, unlike nixpkgs' default `ppc64`. Rust links both big-endian
            # targets with its own lld, which refuses ELFv1 objects, and on
            # 32-bit PowerPC supports only the Secure PLT: nixpkgs' ppc32 gcc
            # is built without `--enable-secureplt`, so its objects, its
            # `crtbeginS.o` included, use the BSS PLT, which lld links without
            # error into a binary that crashes. GNU ld handles both. gcc obeys
            # the last `-fuse-ld`, so a trailing one picks GNU ld.
            powerpc64le = qemu-shell {
              target = "powerpc64le-unknown-linux-gnu";
              cross = pkgs.pkgsCross.powernv;
            };
            powerpc64 = qemu-shell {
              target = "powerpc64-unknown-linux-gnu";
              cross = pkgs.pkgsCross.ppc64-elfv1;
              rustflags = "-C link-arg=-fuse-ld=bfd";
            };
            powerpc = qemu-shell {
              target = "powerpc-unknown-linux-gnu";
              cross = pkgs.pkgsCross.ppc32;
              rustflags = "-C link-arg=-fuse-ld=bfd";
            };

            # `admin/ct-binsec` runs in it: the release tests under gdb, which
            # dumps each at its region, and BINSEC on the dump.
            binsec = pkgs.mkShell {
              packages = [
                rust-stable.minimal
                binsec
                pkgs.gdb
                pkgs.python3
              ];
            };

            # `admin/ct-qemu` traces the armv7 tests in it, through the qemu
            # plugin it adds to the `armv7` shell.
            ct-qemu = pkgs.mkShell (
              armv7-shell
              // {
                packages = armv7-shell.packages ++ [ pkgs.python3 ];
                env = armv7-shell.env // {
                  RIND_CT_QEMU_PLUGIN = "${ct-qemu-plugin}/lib/ct-qemu-plugin.so";
                };
              }
            );

            # `admin/ct-qemu --target aarch64-unknown-linux-gnu` traces the
            # aarch64 tests in it on an aarch64 host, which builds them
            # natively, so it needs none of the armv7 toolchain.
            ct-qemu-aarch64 = pkgs.mkShell {
              packages = [
                rust-stable.minimal
                pkgs.qemu-user
                pkgs.python3
              ];
              env.RIND_CT_QEMU_PLUGIN = "${ct-qemu-plugin}/lib/ct-qemu-plugin.so";
            };
          }
          # `x86-cpu.yml` and `admin/x86-cpu sde-scan` run the tests and
          # `rind-cpuid` under `sde` in it, `admin/ct-sde` traces them, and
          # `admin/mutants --avx512` mutates under it.
          # SDE runs only on x86_64.
          // pkgs.lib.optionalAttrs (system == "x86_64-linux") {
            sde = pkgs.mkShell {
              packages = with pkgs; [
                rust-stable.minimal
                # aws-lc-rs and the OpenSSL benchmarks build C.
                cmake
                pkg-config
                openssl
                python3
                sde
                cargo-mutants
                cargo-nextest
                # `admin/ct-sde` runs SDE without ASLR by its `setarch`.
                util-linux
              ];

              shellHook = sde-certs;
            };
          };

          formatter = pkgs.nixfmt-tree;
        }
      );
}
