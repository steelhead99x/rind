#!/usr/bin/env python3
"""Diff each published adapter's public API against the provider it copies.

Rustdoc's JSON is unstable, so the nightly that writes it is pinned in
flake.nix as `rustdoc-json` (nightly 2026-09-17, format 61). A toolchain
bump that changes the format fails this check instead of passing a wrong
diff.

rind-object-store is not compared. object_store's providers are
pub(crate), so there is no public provider shape to copy. rind-instant-acme
was removed because it had no consumer.

Omissions live in `<adapter>/api-omit.txt`, one path or `feature:<name>`
per line. The adapter's README repeats those tokens inside
`<!-- api-omit -->` ... `<!-- /api-omit -->`, and repeats signature
exceptions (`sig:<path>`) inside `<!-- api-sig -->` ... `<!-- /api-sig -->`.
A listed omission that the diff no longer finds fails, and so does a token
in those regions that the list does not have. An item the adapter adds, or
a signature change that is not listed, fails.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FORMAT_VERSION = 61
# Implemented by the compiler, not written as a signature in the crate.
AUTO_TRAITS = {
    "core::marker::Send",
    "core::marker::Sync",
    "core::marker::Unpin",
    "core::marker::Freeze",
    "core::marker::Sized",
    "core::ops::drop::Drop",
    "core::panic::unwind_safe::UnwindSafe",
    "core::panic::unwind_safe::RefUnwindSafe",
}
NIGHTLY = "nightly-2026-09-17"
# Keep this date in flake.nix's rustdoc-json wrapper.
FLAKE_PIN = f'pkgs.rust-bin.nightly."{NIGHTLY.removeprefix("nightly-")}"'

# object_store's providers are pub(crate). See the module doc.
EXCLUDED = {
    "rind-object-store": (
        "object_store's providers are pub(crate), so there is no public "
        "provider shape to copy"
    ),
}

TOKEN = re.compile(r"`([^`\n]+)`")
OMIT_LINE = re.compile(r"^(?:feature:|sig:)?[A-Za-z_][A-Za-z0-9_]*?(?:::[A-Za-z0-9_]+)*!?$")


@dataclass(frozen=True)
class Adapter:
    """One published adapter and the upstream surface it claims to match.

    `root` is the path under the upstream crate. Empty means the whole
    crate (ring, aws-lc-rs, str0m-aws-lc-rs). `strip` drops that prefix so
    a provider module lines up with the adapter's crate root. A type root
    (rcgen's KeyPair) keeps the type name. `base` is the feature set
    required before that surface exists.
    """

    package: str
    upstream: str
    root: tuple[str, ...] = ()
    base: tuple[str, ...] = ()
    strip: bool = False
    # Features the adapter compiles even when the flag is off. ring gates
    # RSA on alloc and std::error::Error on std; rind-ring always has both.
    always: tuple[str, ...] = ()


# The README of each adapter names this surface.
ADAPTERS = (
    Adapter("rind-ring", "ring", always=("alloc", "std")),
    # aws-lc-rs refuses to build until one of aws-lc-sys, non-fips, or fips is set.
    Adapter("rind-aws-lc-rs", "aws-lc-rs", base=("aws-lc-sys",)),
    Adapter("rind-rustls", "rustls", ("crypto", "aws_lc_rs"), ("aws-lc-rs", "std", "tls12"), True),
    Adapter("rind-dimpl", "dimpl", ("crypto", "aws_lc_rs"), ("aws-lc-rs",), True),
    Adapter("rind-jsonwebtoken", "jsonwebtoken", ("crypto", "aws_lc"), ("aws_lc_rs",), True),
    Adapter("rind-str0m", "str0m-aws-lc-rs"),
    Adapter("rind-rcgen", "rcgen", ("KeyPair",), ("ring", "pem")),
)


def stable_cargo() -> list[str]:
    """The dev shell's cargo is the pinned stable. A host rustup is not."""
    if shutil.which("rustdoc-json"):
        return ["cargo"]
    return ["cargo", "+1.98.1"]


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        self_test()
        print("adapter-api: self-test passed")
        return 0
    pin = (ROOT / "flake.nix").read_text()
    if "rustdoc-json" not in pin or FLAKE_PIN not in pin:
        print(
            f"adapter-api: flake.nix must pin {FLAKE_PIN} in the rustdoc-json wrapper",
            file=sys.stderr,
        )
        return 1
    self_test()
    only = None
    feature_limit = None
    args = argv[1:]
    while args:
        if args[0] == "--only":
            only = args[1]
            args = args[2:]
        elif args[0] == "--feature-set":
            feature_limit = args[1]
            args = args[2:]
        else:
            print(f"adapter-api: unknown argument {args[0]}", file=sys.stderr)
            return 2
    meta = json.loads(
        subprocess.check_output(
            [*stable_cargo(), "metadata", "--format-version", "1", "--locked"],
            cwd=ROOT,
            text=True,
        )
    )
    problems = check_roster(meta)
    failures = 0
    for adapter in ADAPTERS:
        if only and adapter.package != only:
            continue
        print(f"adapter-api: {adapter.package}", file=sys.stderr)
        found = compare(meta, adapter, feature_limit)
        if found:
            failures += 1
            problems.extend(found)
    if problems:
        print("\n".join(problems), file=sys.stderr)
        return 1
    print("adapter-api: public APIs match")
    return 0


def check_roster(meta: dict) -> list[str]:
    published = {
        pkg["name"]
        for pkg in meta["packages"]
        if pkg["name"].startswith("rind-") and pkg.get("publish") is None
    }
    known = {adapter.package for adapter in ADAPTERS} | set(EXCLUDED)
    missing = sorted(published - known)
    extra = sorted(known - published)
    problems = []
    if missing:
        problems.append(
            "adapter-api: published adapters with no comparison: " + ", ".join(missing)
        )
    if extra:
        problems.append("adapter-api: comparison lists an unpublished crate: " + ", ".join(extra))
    return problems


def compare(meta: dict, adapter: Adapter, feature_limit: str | None) -> list[str]:
    upstream = package(meta, adapter.upstream)
    local = package(meta, adapter.package)
    omit_path = ROOT / adapter.package / "api-omit.txt"
    omitted, sigs, added_ok = load_omit(omit_path)
    upstream_features = feature_table(Path(upstream["manifest_path"]))
    adapter_features = feature_table(Path(local["manifest_path"]))
    source = crate_source(Path(upstream["manifest_path"]), adapter.root)
    for name in optional_deps(Path(upstream["manifest_path"])):
        if name not in upstream_features and f'feature = "{name}"' in source:
            upstream_features[name] = [f"dep:{name}"]
    sets = feature_sets(upstream_features, adapter.base, source)
    if feature_limit:
        sets = [item for item in sets if item[0] == feature_limit]
        if not sets:
            return [f"{adapter.package}: no feature set {feature_limit}"]
    problems = check_readme(ROOT / adapter.package / "README.md", omitted, sigs, added_ok)
    implied = set(adapter.base)
    changed = True
    while changed:
        changed = False
        for name in list(implied):
            for dep in upstream_features.get(name, []):
                if (
                    isinstance(dep, str)
                    and not dep.startswith("dep:")
                    and "/" not in dep
                    and dep not in implied
                ):
                    implied.add(dep)
                    changed = True
    missing_features = sorted(
        name
        for name, deps in upstream_features.items()
        if name != "default"
        and name not in implied
        and name not in adapter_features
        and f'feature = "{name}"' in source
    )
    for name in missing_features:
        if f"feature:{name}" not in omitted:
            problems.append(
                f"{adapter.package}: upstream feature {name} is not on the adapter and is not omitted"
            )
    missing_paths: set[str] = set()
    sig_paths: set[str] = set()
    added_paths: set[str] = set()
    for label, no_default, features in sets:
        if any(name not in adapter_features and name not in adapter.base for name in features):
            continue
        upstream_surface = rustdoc_surface(
            upstream, no_default, features, adapter.root, (no_default, tuple(features))
        )
        local_flags = [name for name in features if name in adapter_features]
        local_no_default = bool(local_flags) or (no_default and not adapter.base)
        local_surface = rustdoc_surface(
            local,
            local_no_default,
            local_flags,
            (),
            ("local", adapter.package, local_no_default, tuple(local_flags)),
        )
        if upstream_surface is None and local_surface is None:
            continue
        if upstream_surface is None or local_surface is None:
            problems.append(f"{adapter.package}: {label} builds on only one side")
            continue
        if adapter.always:
            upstream_surface = without_always(
                upstream, upstream_surface, no_default, features, adapter, upstream_features
            )
        found, missed, signed, extra = diff_surfaces(
            adapter.package, label, upstream_surface, local_surface, omitted, sigs, added_ok
        )
        problems.extend(found)
        missing_paths.update(missed)
        sig_paths.update(signed)
        added_paths.update(extra)
    for name in sorted(adapter_features):
        if name == "default" or name in upstream_features or name in adapter.base:
            continue
        with_feature = rustdoc_surface(local, True, [name], (), ("local-only", adapter.package, name))
        without = rustdoc_surface(local, True, [], (), ("local-only", adapter.package, "plain"))
        for path in sorted(set(with_feature) - set(without)):
            if any(covers(entry, path) for entry in added_ok):
                continue
            problems.append(f"{adapter.package}: added {name} {path}")
    for line in sorted(omitted):
        if line.startswith("feature:"):
            if line.removeprefix("feature:") not in missing_features:
                problems.append(
                    f"{adapter.package}: omitted feature {line} is not an upstream-only feature"
                )
            continue
        if not any(covers(line, path) for path in missing_paths):
            problems.append(f"{adapter.package}: omission {line} matches nothing the diff found")
    for line in sorted(sigs):
        path = line.removeprefix("sig:")
        if not any(covers(path, item) for item in sig_paths):
            problems.append(
                f"{adapter.package}: signature exception {path} matches nothing the diff found"
            )
    for line in sorted(added_ok):
        if line not in added_paths:
            problems.append(f"{adapter.package}: listed addition {line} is not an extra item")
    return problems



def without_always(
    upstream: dict,
    surface: dict[str, str],
    no_default: bool,
    features: list[str],
    adapter: Adapter,
    feature_table_upstream: dict[str, list],
) -> dict[str, str]:
    """Drop items the adapter keeps because an upstream feature is always on.

    The returned surface still has every item from `surface`. Items that
    appear only once `always` is enabled are added, so they are not reported
    as adapter additions.
    """
    default = list(feature_table_upstream.get("default") or [])
    if not no_default:
        extra = [name for name in adapter.always if name not in default and name not in features]
        if not extra:
            return surface
        rich = rustdoc_surface(
            upstream, False, extra, adapter.root, (False, tuple(extra), "always")
        )
    else:
        extra = [name for name in adapter.always if name not in features]
        if not extra:
            return surface
        rich = rustdoc_surface(
            upstream,
            True,
            list(features) + extra,
            adapter.root,
            (True, tuple(list(features) + extra), "always"),
        )
    if rich is None:
        return surface
    merged = dict(surface)
    merged.update(rich)
    return merged


def feature_sets(
    features: dict[str, list], base: tuple[str, ...], source: str
) -> list[tuple[str, bool, list[str]]]:
    """Default, no-default (or the module's base), and each feature that changes the surface."""
    sets = []
    if base:
        sets.append(("base", True, list(base)))
    else:
        sets.append(("default", False, []))
        sets.append(("no-default", True, []))
    for name, deps in features.items():
        if name == "default":
            continue
        if name in base:
            continue
        if not affects(name, deps, source):
            continue
        sets.append((name, True, list(base) + [name]))
    return sets


def affects(name: str, deps: list, source: str) -> bool:
    if f'feature = "{name}"' in source or f"feature = \"{name}\"" in source:
        return True
    for dep in deps:
        text = dep if isinstance(dep, str) else ""
        if text.startswith("dep:") or "/" in text:
            return True
    return False


def feature_table(manifest: Path) -> dict[str, list]:
    data = tomllib.loads(manifest.read_text())
    return {name: list(value) if isinstance(value, list) else [] for name, value in data.get("features", {}).items()}


def optional_deps(manifest: Path) -> list[str]:
    """Optional dependencies are features even when `[features]` omits them."""
    data = tomllib.loads(manifest.read_text())
    names = []
    deps = data.get("dependencies")
    if isinstance(deps, dict):
        for name, spec in deps.items():
            if isinstance(spec, dict) and spec.get("optional"):
                names.append(name)
    return names


def crate_source(manifest: Path, root: tuple[str, ...]) -> str:
    """Source whose `feature = "..."` gates the compared surface.

    A module root is that module file and its directory, not the parent
    that selects a different provider. A type root is every impl of that
    type, so a feature that only gates a sibling type is not an omission.
    Comments and `cfg(test)` do not count.
    """
    src = manifest.parent / "src"
    if not src.is_dir():
        return ""
    files = list(src.rglob("*.rs"))
    if root:
        module_file = src.joinpath(*root[:-1], f"{root[-1]}.rs")
        module_dir = src.joinpath(*root)
        module_files = [path for path in files if path == module_file or module_dir in path.parents]
        if module_files:
            files = module_files
            return active_source("\n".join(path.read_text(errors="replace") for path in files))
        kept = [type_items(path.read_text(errors="replace"), root[0]) for path in files]
        return active_source("\n".join(kept))
    return active_source("\n".join(path.read_text(errors="replace") for path in files))


def active_source(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    lines = []
    for line in text.splitlines():
        code = line.split("//", 1)[0]
        if re.search(r"\bcfg\(\s*(?:all|any)?\s*\(?\s*test\b", code):
            continue
        lines.append(code)
    return "\n".join(lines)


def type_items(text: str, type_name: str) -> str:
    """The struct and impl blocks of one type, including their attributes."""
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    lines = text.splitlines()
    code = [line.split("//", 1)[0] for line in lines]
    keep = [False] * len(lines)
    i = 0
    while i < len(lines):
        if _opens_type(code[i], type_name):
            start = i
            while start > 0 and (code[start - 1].strip().startswith("#") or not code[start - 1].strip()):
                start -= 1
            depth = 0
            started = False
            j = i
            while j < len(lines):
                depth += code[j].count("{") - code[j].count("}")
                if "{" in code[j]:
                    started = True
                keep[j] = True
                j += 1
                if started and depth <= 0:
                    break
            for k in range(start, i):
                keep[k] = True
            i = j
            continue
        i += 1
    return "\n".join(line for line, wanted in zip(lines, keep) if wanted)


def _opens_type(code: str, type_name: str) -> bool:
    stripped = code.strip()
    if re.search(rf"\b(struct|enum|union|type)\s+{type_name}\b", stripped):
        return True
    if re.search(rf"\bimpl(?:<[^>]*>)?\s+{type_name}\b", stripped):
        return True
    if re.search(rf"\bimpl(?:<[^>]*>)?\s+.+\s+for\s+{type_name}\b", stripped):
        return True
    return False


def rustdoc_surface(
    pkg: dict, no_default: bool, features: list[str], root: tuple[str, ...], cache_key
) -> dict[str, str] | None:
    cache = rustdoc_surface.cache
    key = (pkg["manifest_path"], cache_key)
    if key in cache:
        cached = cache[key]
        if cached is None:
            return None
        return filter_root(cached, pkg, root, strip_root(pkg, root))
    # One target directory per side so aws-lc's C build is reused across
    # feature sets. The JSON is parsed before the next rustdoc overwrites it.
    if in_workspace(pkg["manifest_path"]):
        target = ROOT / ".tmp" / "adapter-api" / "workspace"
    else:
        target = ROOT / ".tmp" / "adapter-api" / "upstream"
    target.mkdir(parents=True, exist_ok=True)
    cmd = rustdoc_cmd(pkg, no_default, features)
    env = os.environ.copy()
    env["CARGO_TARGET_DIR"] = str(target)
    print(f"adapter-api: rustdoc {pkg['name']} {cache_key}", file=sys.stderr)
    proc = subprocess.run(cmd, cwd=pkg_dir(pkg), env=env, text=True, capture_output=True)
    if proc.returncode != 0:
        tail = "\n".join((proc.stderr or proc.stdout).splitlines()[-8:])
        print(f"adapter-api: {pkg['name']} {cache_key} did not build\n{tail}", file=sys.stderr)
        cache[key] = None
        return None
    lib = lib_name(pkg)
    found = list(target.glob(f"doc/{lib}.json"))
    if not found:
        found = list((target / "doc").glob("*.json"))
    if len(found) != 1:
        raise SystemExit(f"adapter-api: expected one JSON for {pkg['name']}, found {found}")
    doc = json.loads(found[0].read_text())
    if doc.get("format_version") != FORMAT_VERSION:
        raise SystemExit(
            f"adapter-api: rustdoc JSON format {doc.get('format_version')} "
            f"!= {FORMAT_VERSION}; the pin in flake.nix moved"
        )
    surface = public_surface(doc)
    cache[key] = surface
    return filter_root(surface, pkg, root, strip_root(pkg, root))


rustdoc_surface.cache = {}


def strip_root(pkg: dict, root: tuple[str, ...]) -> bool:
    for adapter in ADAPTERS:
        if adapter.upstream == pkg["name"] or adapter.package == pkg["name"]:
            if adapter.root == root:
                return adapter.strip
    return False


def filter_root(surface: dict[str, str], pkg: dict, root: tuple[str, ...], strip: bool) -> dict[str, str]:
    """Paths from the module walk have no crate name. `root` selects the surface."""
    out = {}
    for path, sig in surface.items():
        body = path[len("impl ") :].split(" as ", 1)[0] if path.startswith("impl ") else path
        parts = body.split("::")
        if root and tuple(parts[: len(root)]) != root:
            continue
        if root and strip:
            rel_body = "::".join(parts[len(root) :])
            if path.startswith("impl "):
                trait = path.split(" as ", 1)[1] if " as " in path else ""
                rel = f"impl {rel_body} as {trait}" if trait else f"impl {rel_body}"
            else:
                rel = rel_body
        else:
            rel = path
        if not rel:
            continue
        out[rel] = sig
    return out


def rustdoc_cmd(pkg: dict, no_default: bool, features: list[str]) -> list[str]:
    manifest = pkg["manifest_path"]
    workspace = in_workspace(manifest)
    if workspace:
        manifest = str(ROOT / "Cargo.toml")
    else:
        # A registry crate's dev-dependencies are not in this workspace's
        # lock. Depend on the locked version from a tiny crate so cargo
        # resolves only what the library needs.
        manifest = wrapper_manifest(pkg, no_default, features)
    if shutil.which("rustdoc-json"):
        cmd = ["rustdoc-json"]
    else:
        cmd = ["cargo", f"+{NIGHTLY}", "rustdoc"]
    cmd += ["--manifest-path", manifest, "-p", pkg["name"], "--lib"]
    if workspace:
        cmd += ["--locked", "--offline"]
        # --features is rejected for a registry crate. The wrapper's
        # dependency lists those features, and cargo rustdoc -p uses them.
        if no_default:
            cmd.append("--no-default-features")
        if features:
            cmd += ["--features", ",".join(features)]
    cmd += ["--", "-Z", "unstable-options", "--output-format", "json"]
    return cmd


def wrapper_manifest(pkg: dict, no_default: bool, features: list[str]) -> str:
    dest = ROOT / ".tmp" / "adapter-api" / "wrappers" / safe(
        f"{pkg['name']}-{pkg['version']}-{no_default}-{','.join(features)}"
    )
    dest.mkdir(parents=True, exist_ok=True)
    spec = f'version = "={pkg["version"]}"'
    if no_default or features:
        spec += ", default-features = false"
    if features:
        joined = ", ".join(f'"{name}"' for name in features)
        spec += f", features = [{joined}]"
    (dest / "Cargo.toml").write_text(
        "\n".join(
            [
                "[package]",
                'name = "adapter-api-wrap"',
                'version = "0.0.0"',
                'edition = "2021"',
                "publish = false",
                "",
                "[dependencies]",
                f"{pkg['name']} = {{ {spec} }}",
                "",
                "# Not a member of the rind workspace that contains .tmp/.",
                "[workspace]",
                "",
            ]
        )
    )
    source = dest / "src"
    source.mkdir(exist_ok=True)
    (source / "lib.rs").write_text("")
    return str(dest / "Cargo.toml")


def in_workspace(manifest: str) -> bool:
    path = Path(manifest).resolve()
    root = ROOT.resolve()
    return path == root / "Cargo.toml" or root in path.parents


def pkg_dir(pkg: dict) -> Path:
    return Path(pkg["manifest_path"]).parent


def package(meta: dict, name: str) -> dict:
    found = [pkg for pkg in meta["packages"] if pkg["name"] == name]
    if len(found) != 1:
        raise SystemExit(f"adapter-api: expected one {name} in Cargo.lock, found {len(found)}")
    return found[0]


def lib_name(pkg: dict) -> str:
    for target in pkg["targets"]:
        if "lib" in target["kind"]:
            return target["name"]
    raise SystemExit(f"adapter-api: {pkg['name']} has no lib target")


def safe(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9._-]+", "_", text)[:120]


def public_surface(doc: dict) -> dict[str, str]:
    index = doc["index"]
    root = index[str(doc["root"])]
    local = root["crate_id"]
    paths = doc["paths"]
    by_id = {}
    for ident, info in paths.items():
        if info["crate_id"] == local:
            by_id[int(ident)] = info["path"]

    def path_of(ident: int) -> str | None:
        found = by_id.get(ident)
        if found:
            return "::".join(found)
        return None

    expanding: set[int] = set()
    surface: dict[str, str] = {}
    # Shortest public path of each local item. Re-exports are what callers name.
    public_names: dict[int, str] = {}

    def add(path: str, sig: str) -> None:
        surface[path] = sig

    def render_id_path(ident: int) -> str:
        named = public_names.get(int(ident))
        if named:
            return named
        info = paths.get(str(ident))
        if not info:
            return f"{{id{ident}}}"
        parts = info["path"]
        if info["crate_id"] == local:
            return "::".join(parts[1:])
        return "::".join(parts)

    def render_type(node) -> str:
        if not isinstance(node, dict):
            return str(node)
        if "primitive" in node:
            return node["primitive"]
        if "generic" in node:
            return node["generic"]
        if "resolved_path" in node:
            item = node["resolved_path"]
            ident = item.get("id")
            target = index.get(str(ident)) if ident is not None else None
            while target and "use" in target.get("inner", {}):
                ident = target["inner"]["use"].get("id")
                target = index.get(str(ident)) if ident is not None else None
            alias = (target or {}).get("inner", {}).get("type_alias") if target else None
            if alias and alias.get("type") is not None and ident not in expanding:
                expanding.add(ident)
                rendered = render_type(alias["type"])
                expanding.discard(ident)
                return rendered
            name = render_id_path(ident) if ident is not None else item.get("path", "?")
            if name in ("core::fmt::Result", "std::fmt::Result"):
                return "core::result::Result<(), core::fmt::Error>"
            return name + render_args(item.get("args"))
        if "borrowed_ref" in node:
            item = node["borrowed_ref"]
            life = (item.get("lifetime") or "") + " " if item.get("lifetime") else ""
            mut = "mut " if item.get("is_mutable") else ""
            return f"&{life}{mut}{render_type(item['type'])}"
        if "raw_pointer" in node:
            item = node["raw_pointer"]
            kind = "mut" if item.get("is_mutable") else "const"
            return f"*{kind} {render_type(item['type'])}"
        if "tuple" in node:
            return "(" + ", ".join(render_type(part) for part in node["tuple"]) + ")"
        if "slice" in node:
            return f"[{render_type(node['slice'])}]"
        if "array" in node:
            body = node["array"]
            return f"[{render_type(body['type'])}; {body.get('len', '?')}]"
        if "dyn_trait" in node or "impl_trait" in node:
            key = "dyn_trait" if "dyn_trait" in node else "impl_trait"
            word = "dyn" if key == "dyn_trait" else "impl"
            body = node[key]
            if isinstance(body, dict):
                bounds = body.get("traits") or body.get("bounds") or []
            else:
                bounds = body
            return word + " " + render_bounds(bounds)
        if "qualified_path" in node:
            item = node["qualified_path"]
            trait = item.get("trait") or {}
            trait_name = render_id_path(trait["id"]) if "id" in trait else trait.get("path", "")
            self_ty = render_type(item.get("self_type"))
            return f"<{self_ty} as {trait_name}>::{item.get('name', '?')}"
        if "function_pointer" in node:
            return "fn" + render_fn_sig(node["function_pointer"])
        if "name" in node and "trait" in node and "self_type" in node:
            trait = node["trait"]
            trait_name = render_id_path(trait["id"]) if isinstance(trait, dict) and "id" in trait else "?"
            return f"<{render_type(node['self_type'])} as {trait_name}>::{node['name']}"
        return json.dumps(node, sort_keys=True, default=str)

    def render_args(args) -> str:
        if not args:
            return ""
        if "angle_bracketed" in args:
            bits = []
            for arg in args["angle_bracketed"].get("args", []):
                if "type" in arg:
                    bits.append(render_type(arg["type"]))
                elif "lifetime" in arg:
                    bits.append(arg["lifetime"])
                elif "const" in arg:
                    bits.append(json.dumps(arg["const"], sort_keys=True, default=str))
                else:
                    bits.append(json.dumps(arg, sort_keys=True, default=str))
            return "<" + ", ".join(bits) + ">" if bits else ""
        if "parenthesized" in args:
            item = args["parenthesized"]
            inputs = ", ".join(render_type(part) for part in item.get("inputs", []))
            output = render_type(item["output"]) if item.get("output") else ""
            return f"({inputs})" + (f" -> {output}" if output else "")
        return ""

    def render_bounds(bounds) -> str:
        parts = []
        for bound in bounds:
            trait = None
            if isinstance(bound, dict) and "trait_bound" in bound:
                trait = bound["trait_bound"]["trait"]
            elif isinstance(bound, dict) and "trait" in bound:
                trait = bound["trait"]
            if trait:
                name = render_id_path(trait["id"]) if "id" in trait else trait.get("path", "?")
                parts.append(name + render_args(trait.get("args")))
            else:
                parts.append(json.dumps(bound, sort_keys=True, default=str))
        return " + ".join(parts)

    def render_fn_sig(fn: dict) -> str:
        header = fn.get("header") or {}
        flags = []
        if header.get("is_const"):
            flags.append("const")
        if header.get("is_async"):
            flags.append("async")
        if header.get("is_unsafe"):
            flags.append("unsafe")
        abi = header.get("abi")
        if abi and abi != "Rust":
            flags.append(f'extern "{abi}"')
        generics = render_generics(fn.get("generics"))
        inputs = []
        for name, ty in fn.get("sig", {}).get("inputs", []):
            rendered = render_type(ty)
            inputs.append(rendered if name == "self" else f"_: {rendered}")
        output = fn.get("sig", {}).get("output")
        ret = f" -> {render_type(output)}" if output else ""
        return " ".join(flags) + generics + "(" + ", ".join(inputs) + ")" + ret

    def render_generics(generics) -> str:
        if not generics:
            return ""
        params = [param["name"] for param in generics.get("params") or []]
        text = f"<{', '.join(params)}>" if params else ""
        where = generics.get("where_predicates") or []
        if where:
            text += " where " + json.dumps(scrub(where), sort_keys=True, default=str)
        return text

    def scrub(node):
        if isinstance(node, dict):
            if "resolved_path" in node and set(node) <= {"resolved_path"}:
                return render_type(node)
            if "id" in node and "path" in node:
                return render_id_path(node["id"]) + render_args(node.get("args"))
            return {
                key: scrub(value)
                for key, value in node.items()
                if key not in ("id", "expr", "is_literal", "is_unsafe")
            }
        if isinstance(node, list):
            return [scrub(value) for value in node]
        return node

    def consider_child(parent: str, ident: int) -> None:
        item = index[str(ident)]
        kind = next(iter(item["inner"]))
        vis = item.get("visibility")
        if vis not in ("public", "default"):
            return
        if kind == "variant":
            name = item.get("name") or "?"
            add(f"{parent}::{name}", "variant")
            return
        if kind == "struct_field":
            if vis != "public":
                return
            name = item.get("name") or "?"
            add(f"{parent}::{name}", "field " + render_type(item["inner"]["struct_field"]))
            return
        if kind in ("function", "assoc_const", "assoc_type"):
            name = item.get("name") or "?"
            inner = item["inner"][kind]
            if kind == "function":
                sig = render_fn_sig(inner)
                self_ty = parent.split(" as ", 1)[0]
                sig = re.sub(r"\bSelf\b", self_ty, sig)
                sig = elide_lifetimes(sig)
            else:
                sig = kind + " " + json.dumps(scrub(inner), sort_keys=True, default=str)
            add(f"{parent}::{name}", sig)

    def implemented_traits(type_node) -> str:
        if not isinstance(type_node, dict) or "resolved_path" not in type_node:
            return ""
        ident = type_node["resolved_path"].get("id")
        item = index.get(str(ident)) if ident is not None else None
        if not item:
            return ""
        body = item["inner"]
        key = next(iter(body))
        if key not in ("struct", "enum", "union"):
            return ""
        names = []
        for impl_id in body[key].get("impls") or []:
            block = index[str(impl_id)]["inner"].get("impl") or {}
            trait = block.get("trait")
            if not trait or block.get("is_synthetic") or block.get("blanket_impl"):
                continue
            name = render_id_path(trait["id"]) if "id" in trait else trait.get("path", "")
            if not name or "Structural" in name or name.startswith("core::marker::"):
                continue
            if "id" in trait and int(trait["id"]) not in public_names and not name.startswith(("core::", "std::")):
                continue
            names.append(name)
        return " + ".join(sorted(set(names)))

    def remember(ident: int, path: str) -> None:
        previous = public_names.get(ident)
        rank = (path.count("::"), path)
        if previous is None or rank < (previous.count("::"), previous):
            public_names[ident] = path

    def add_at(ident: int, pub_path: list[str]) -> None:
        item = index[str(ident)]
        inner = item["inner"]
        kind = next(iter(inner))
        path = "::".join(pub_path)
        remember(int(ident), path)
        if kind == "module":
            add(path, "module")
            walk(ident, pub_path)
            return
        if kind == "struct":
            add(path, "struct")
            kind_body = inner["struct"].get("kind") or {}
            plain = kind_body.get("plain", {}) if isinstance(kind_body, dict) else {}
            fields = plain.get("fields") or [] if isinstance(plain, dict) else []
            for field in fields:
                consider_child(path, field)
        elif kind == "enum":
            add(path, "enum")
            for variant in inner["enum"].get("variants") or []:
                consider_child(path, variant)
        elif kind == "union":
            add(path, "union")
        elif kind == "macro":
            add(path + "!", "macro")
        elif kind == "function":
            add(path, render_fn_sig(inner["function"]))
        elif kind == "trait":
            add(path, "trait")
            for child in inner["trait"].get("items") or []:
                consider_child(path, child)
        elif kind in ("constant", "static", "type_alias"):
            body = inner[kind]
            ty = render_type(body["type"]) if isinstance(body, dict) and "type" in body else json.dumps(scrub(body), sort_keys=True)
            if kind == "static" and ty not in public_names.values():
                traits = implemented_traits(body.get("type"))
                if traits:
                    ty = traits
            value = ""
            if kind == "constant" and isinstance(body, dict):
                const = body.get("const") or {}
                if const.get("value"):
                    value = " = " + const["value"]
            add(path, f"{kind} {ty}{value}")
        else:
            add(path, kind)
        if kind in ("struct", "enum", "union"):
            for impl in inner[kind].get("impls") or []:
                block = index[str(impl)]["inner"].get("impl")
                if not block or block.get("is_synthetic") or block.get("blanket_impl"):
                    continue
                trait = block.get("trait")
                if trait:
                    trait_name = render_id_path_from(trait, render_id_path)
                    # Marker traits are not a signature callers can name.
                    if trait_name in AUTO_TRAITS or "StructuralPartialEq" in trait_name or "StructuralEq" in trait_name:
                        continue
                    add(f"impl {path} as {trait_name}", "impl")
                    # The trait fixes the method signatures. Comparing them
                    # reports rustdoc's qualified-path spelling, not an API change.
                    continue
                for child in block.get("items") or []:
                    consider_child(path, child)

    seen: set[tuple[int, tuple[str, ...]]] = set()

    def walk(mod_id: int, prefix: list[str]) -> None:
        key = (int(mod_id), tuple(prefix))
        if key in seen:
            return
        seen.add(key)
        module = index[str(mod_id)]["inner"]["module"]
        for iid in module["items"]:
            item = index[str(iid)]
            kind = next(iter(item["inner"]))
            if kind == "use":
                if item.get("visibility") != "public":
                    continue
                use = item["inner"]["use"]
                if use.get("is_glob") or not use.get("name") or str(use.get("id")) not in index:
                    continue
                add_at(use["id"], prefix + [use["name"]])
                continue
            if item.get("visibility") != "public" or not item.get("name"):
                continue
            add_at(iid, prefix + [item["name"]])

    # Names first, so a signature can use the public path of a later item.
    def collect(mod_id: int, prefix: list[str]) -> None:
        module = index[str(mod_id)]["inner"]["module"]
        for iid in module["items"]:
            item = index[str(iid)]
            kind = next(iter(item["inner"]))
            if kind == "use":
                if item.get("visibility") != "public":
                    continue
                use = item["inner"]["use"]
                if use.get("is_glob") or not use.get("name") or str(use.get("id")) not in index:
                    continue
                remember(int(use["id"]), "::".join(prefix + [use["name"]]))
                target = index[str(use["id"])]
                if "module" in target["inner"]:
                    collect(use["id"], prefix + [use["name"]])
                continue
            if item.get("visibility") != "public" or not item.get("name"):
                continue
            remember(int(iid), "::".join(prefix + [item["name"]]))
            if kind == "module":
                collect(iid, prefix + [item["name"]])

    collect(int(doc["root"]), [])
    walk(int(doc["root"]), [])

    return surface


def render_id_path_from(trait: dict, render_id_path) -> str:
    name = render_id_path(trait["id"]) if "id" in trait else trait.get("path", "?")
    return name


def diff_surfaces(
    package_name: str,
    label: str,
    upstream: dict[str, str],
    local: dict[str, str],
    omitted: set[str],
    sigs: set[str],
    added_ok: set[str],
) -> tuple[list[str], set[str], set[str], set[str]]:
    problems = []
    missed: set[str] = set()
    signed: set[str] = set()
    extra: set[str] = set()
    names = set(upstream) | set(local)
    counts = name_counts(names)
    # A final name used more than once is two items. A name used once, or
    # only inside a signature, is one type whose path rustdoc spelled
    # differently on each side (`Error` and `rcgen::error::Error`).
    ambiguous = {name for name, count in counts.items() if count > 1}
    roots = {path for path in names if "::" not in path and not path.startswith("impl ")}
    roots.update(
        path.split(" as ", 1)[1] for path in names if " as " in path and "::" not in path.split(" as ", 1)[1]
    )
    upstream = {align_key(path, ambiguous, roots): align(sig, ambiguous, roots) for path, sig in upstream.items()}
    local = {align_key(path, ambiguous, roots): align(sig, ambiguous, roots) for path, sig in local.items()}
    for path, sig in sorted(upstream.items()):
        if path not in local:
            missed.add(path)
            if any(covers(entry, path) for entry in omitted if not entry.startswith("feature:")):
                continue
            problems.append(f"{package_name}: missing {label} {path}")
            continue
        if local[path] != sig:
            signed.add(path)
            if any(covers(entry.removeprefix("sig:"), path) for entry in sigs):
                continue
            problems.append(f"{package_name}: signature {label} {path}")
    for path in sorted(local):
        if path not in upstream:
            extra.add(path)
            if any(covers(entry, path) for entry in added_ok):
                continue
            problems.append(f"{package_name}: added {label} {path}")
    return problems, missed, signed, extra


def name_counts(paths: set[str]):
    from collections import Counter

    counts: Counter[str] = Counter()
    for path in paths:
        for piece in re.findall(r"[A-Za-z_][A-Za-z0-9_]*", path):
            counts[piece] += 1
    return counts


def align_key(path: str, ambiguous: set[str], roots: set[str]) -> str:
    if " as " not in path:
        return path
    left, right = path.split(" as ", 1)
    return left + " as " + align(right, ambiguous, roots)


def align(text: str, ambiguous: set[str], roots: set[str]) -> str:
    """Drop a module prefix on a type name that is not two public items."""

    def repl(match: re.Match[str]) -> str:
        tail = match.group(1)
        if tail in roots or tail not in ambiguous:
            return tail
        return match.group(0)

    return re.sub(r"\b(?:[A-Za-z_][A-Za-z0-9_]*::)+([A-Za-z_][A-Za-z0-9_]*)\b", repl, text)


def elide_lifetimes(sig: str) -> str:
    """Spell elided input lifetimes the same way in both rustdocs."""
    names = re.findall(r"'[A-Za-z_][A-Za-z0-9_]*", sig)
    # Drop a lifetime that occurs only as a reference on an input and as a
    # generic parameter, which rustdoc sometimes names and sometimes elides.
    for name in dict.fromkeys(names):
        if sig.split("->", 1)[-1].find(name) != -1 and "->" in sig:
            continue
        sig = sig.replace(name, "")
    sig = re.sub(r"<\s*,", "<", sig)
    sig = re.sub(r",\s*>", ">", sig)
    sig = re.sub(r"<\s*>", "", sig)
    sig = re.sub(r"<\s+", "<", sig)
    sig = re.sub(r"&\s+mut\b", "&mut", sig)
    sig = re.sub(r"&\s+", "&", sig)
    sig = re.sub(r"&+", "&", sig)
    return sig


def covers(entry: str, path: str) -> bool:
    if entry.endswith("*"):
        return path.startswith(entry[:-1]) or (
            path.startswith("impl ") and path[len("impl ") :].startswith(entry[:-1])
        )
    if path == entry or path.startswith(entry + "::"):
        return True
    if path.startswith("impl "):
        self_ty = path[len("impl ") :].split(" as ", 1)[0]
        return self_ty == entry or self_ty.startswith(entry + "::")
    return False


def load_omit(path: Path) -> tuple[set[str], set[str], set[str]]:
    if not path.is_file():
        return set(), set(), set()
    omitted, sigs, added = set(), set(), set()
    for raw in path.read_text().splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        if line.startswith("sig:"):
            sigs.add(line)
        elif line.startswith("add:"):
            added.add(line.removeprefix("add:"))
        else:
            omitted.add(line)
    return omitted, sigs, added


def check_readme(readme: Path, omitted: set[str], sigs: set[str], added_ok: set[str]) -> list[str]:
    if not omitted and not sigs and not added_ok:
        return []
    text = readme.read_text() if readme.is_file() else ""
    problems = []
    problems.extend(region_matches(readme, text, "api-omit", display_tokens(omitted)))
    problems.extend(region_matches(readme, text, "api-sig", {line.removeprefix("sig:") for line in sigs}))
    problems.extend(region_matches(readme, text, "api-add", added_ok))
    return problems


def display_tokens(omitted: set[str]) -> set[str]:
    tokens = set()
    for line in omitted:
        if line.startswith("feature:"):
            tokens.add(line.removeprefix("feature:"))
        else:
            tokens.add(line)
    return tokens


def region_matches(readme: Path, text: str, name: str, expected: set[str]) -> list[str]:
    if not expected:
        return []
    start = f"<!-- {name} -->"
    end = f"<!-- /{name} -->"
    if start not in text or end not in text:
        return [f"{readme.relative_to(ROOT)}: missing {start} ... {end} for {sorted(expected)}"]
    region = text.split(start, 1)[1].split(end, 1)[0]
    found = set(TOKEN.findall(region))
    label = readme.name if ROOT not in readme.parents and readme != ROOT else str(readme.relative_to(ROOT))
    problems = []
    for token in sorted(expected - found):
        problems.append(f"{label}: {name} region does not mention `{token}`")
    for token in sorted(found - expected):
        if OMIT_LINE.match(token) or "::" in token or token.endswith("!"):
            problems.append(f"{label}: {name} region mentions `{token}` which is not listed")
    return problems


def self_test() -> None:
    omitted = {"io", "feature:fips"}
    assert covers("io", "io::reader")
    assert not covers("io", "iota")
    problems, missed, _signed, _extra = diff_surfaces(
        "example",
        "default",
        {"io::reader": "fn()", "keep": "fn()"},
        {"keep": "fn()", "extra": "fn()"},
        omitted,
        set(),
        set(),
    )
    assert any("added default extra" in item for item in problems), problems
    assert not any("io::reader" in item for item in problems), problems
    assert "io::reader" in missed
    sigs = {"sig:keep"}
    problems, _missed, signed, _extra = diff_surfaces(
        "example2",
        "default",
        {"keep": "fn(a)"},
        {"keep": "fn(b)"},
        set(),
        sigs,
        set(),
    )
    assert problems == [], problems
    assert signed == {"keep"}
    same, _, _, _ = diff_surfaces(
        "alias",
        "default",
        {"CryptoProvider": "struct", "f": "fn() -> crypto::CryptoProvider"},
        {"CryptoProvider": "struct", "f": "fn() -> rustls::crypto::CryptoProvider"},
        set(),
        set(),
        set(),
    )
    assert same == [], same
    differ, _, _, _ = diff_surfaces(
        "errors",
        "default",
        {"foo::Error": "struct", "f": "fn() -> foo::Error"},
        {"bar::Error": "struct", "f": "fn() -> bar::Error"},
        set(),
        set(),
        set(),
    )
    assert any("signature" in item for item in differ), differ
    readme = """
<!-- api-omit -->
`io` and `fips`
<!-- /api-omit -->
<!-- api-sig -->
`keep`
<!-- /api-sig -->
"""
    sample = """
/// #[cfg(feature = "rcgen")]
struct Other { #[cfg(feature = "x509-parser")] field: u8 }
#[cfg(feature = "aws_lc_rs")]
impl KeyPair {
    #[cfg(feature = "pem")]
    pub fn pem(&self) {}
}
#[cfg(all(test, feature = "rcgen"))]
impl KeyPair { fn test_only(&self) {} }
#[cfg(feature = "zeroize")]
impl zeroize::Zeroize for KeyPair { fn zeroize(&mut self) {} }
"""
    scanned = active_source(type_items(sample, "KeyPair"))
    assert 'feature = "aws_lc_rs"' in scanned and 'feature = "zeroize"' in scanned
    assert 'feature = "pem"' in scanned
    assert 'feature = "rcgen"' not in scanned and 'feature = "x509-parser"' not in scanned
    assert region_matches(Path("README.md"), readme, "api-omit", {"io", "fips"}) == []
    bad = region_matches(Path("README.md"), readme, "api-omit", {"io", "fips", "gone"})
    assert any("gone" in item for item in bad), bad
    print("adapter-api: self-test ok", file=sys.stderr)


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except BrokenPipeError:
        sys.exit(1)
