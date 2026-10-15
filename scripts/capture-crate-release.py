#!/usr/bin/env python3
"""Capture a crates.io release, or check a saved capture without network access."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import sys
import tarfile
import tempfile
import urllib.request


def sha(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def get(url, destination, limit):
    request = urllib.request.Request(url, headers={"User-Agent": "proof-env-release-capture/1"})
    size = 0
    with urllib.request.urlopen(request, timeout=30) as response, destination.open("wb") as output:
        while chunk := response.read(1024 * 1024):
            size += len(chunk)
            if size > limit:
                raise ValueError(f"Download exceeds capture size limit: {url}")
            output.write(chunk)


def members(archive, name, version):
    prefix = f"{name}-{version}"
    seen = set()
    total = 0
    result = []
    for member in archive:
        path = PurePosixPath(member.name)
        if path.is_absolute() or ".." in path.parts or not path.parts or path.parts[0] != prefix:
            raise ValueError(f"Unexpected archive path: {member.name}")
        if member.isdir():
            continue
        if not member.isfile() or len(path.parts) < 2:
            raise ValueError(f"Unsupported archive entry (not a regular file): {member.name}")
        relative = PurePosixPath(*path.parts[1:]).as_posix()
        if relative in seen:
            raise ValueError(f"Duplicate archive entry: {relative}")
        seen.add(relative)
        total += member.size
        if total > 512 * 1024 * 1024 or len(seen) > 100_000:
            raise ValueError("Unpacked release exceeds capture size limit")
        result.append((relative, member))
    if "Cargo.toml" not in seen:
        raise ValueError("Release archive has no Cargo.toml")
    return result


def identity(metadata, name, version):
    item = metadata["version"]
    if item["crate"] != name or item["num"] != version:
        raise ValueError("Registry response crate/version does not match requested release")
    checksum = item["checksum"]
    if not isinstance(checksum, str) or not re.fullmatch(r"[0-9a-f]{64}", checksum):
        raise ValueError("Registry response has no valid archive checksum")
    return item


def check(directory):
    record = json.loads((directory / "manifest.json").read_text())
    if record.get("schema_version") != 1:
        raise ValueError("Unsupported capture schema")
    name, version = record["crate"]["name"], record["crate"]["version"]
    metadata = directory / "registry-metadata.json"
    archive_path = directory / "release.crate"
    if sha(metadata) != record["registry_metadata_sha256"]:
        raise ValueError("Captured registry metadata changed")
    item = identity(json.loads(metadata.read_bytes()), name, version)
    if item["checksum"] != record["archive_sha256"] or sha(archive_path) != item["checksum"]:
        raise ValueError("Release archive checksum mismatch")
    source = directory / "source"
    if source.is_symlink() or any(p.is_symlink() for p in source.rglob("*")):
        raise ValueError("Captured source contains a symlink absent from the regular-file archive")
    actual = {p.relative_to(source).as_posix(): sha(p) for p in source.rglob("*") if p.is_file()}
    if actual != record["source_files_sha256"]:
        raise ValueError("Captured release source inventory/hash mismatch")
    with tarfile.open(archive_path, "r:gz") as archive:
        entries = members(archive, name, version)
        archive_hashes = {relative: hashlib.sha256(archive.extractfile(member).read()).hexdigest()
                          for relative, member in entries}
    if actual != archive_hashes:
        raise ValueError("Extracted files differ from checksum-pinned archive")
    vcs_path = source / ".cargo_vcs_info.json"
    vcs = json.loads(vcs_path.read_text()) if vcs_path.exists() else None
    if vcs != record["release_vcs_info"]:
        raise ValueError("Release VCS metadata mismatch")
    return record


def capture(args):
    name, version = args.name, args.version
    if not name or not re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9_-]*", name):
        raise ValueError("Provide a crates.io crate name")
    if not version or not re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+(?:-[0-9A-Za-z.-]+)?(?:\+[0-9A-Za-z.-]+)?", version):
        raise ValueError("Provide an exact crate version")
    if args.output is None:
        raise ValueError("Capture requires --output DIRECTORY")
    output = args.output.resolve()
    if output.exists():
        raise ValueError("Output already exists; check it with --check or choose a new directory")
    if bool(args.metadata_file) != bool(args.archive_file):
        raise ValueError("Offline capture requires both --metadata-file and --archive-file")
    output.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=".release-", dir=output.parent))
    metadata_url = f"https://crates.io/api/v1/crates/{name}/{version}"
    archive_url = f"https://static.crates.io/crates/{name}/{name}-{version}.crate"
    try:
        metadata_path = stage / "registry-metadata.json"
        archive_path = stage / "release.crate"
        if args.metadata_file:
            shutil.copyfile(args.metadata_file, metadata_path)
            shutil.copyfile(args.archive_file, archive_path)
        else:
            get(metadata_url, metadata_path, 8 * 1024 * 1024)
            get(archive_url, archive_path, 128 * 1024 * 1024)
        item = identity(json.loads(metadata_path.read_bytes()), name, version)
        if sha(archive_path) != item["checksum"]:
            raise ValueError("Downloaded/supplied archive differs from registry checksum")
        with tarfile.open(archive_path, "r:gz") as archive:
            for relative, member in members(archive, name, version):
                destination = stage / "source" / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                with archive.extractfile(member) as source, destination.open("wb") as target:
                    shutil.copyfileobj(source, target)
                destination.chmod(member.mode & 0o777)
        source = stage / "source"
        vcs_path = source / ".cargo_vcs_info.json"
        record = {
            "schema_version": 1,
            "captured_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "crate": {"name": name, "version": version},
            "metadata_url": metadata_url,
            "archive_url": archive_url,
            "input_origin": "supplied local files" if args.metadata_file else "crates.io HTTPS reads",
            "published_at": item.get("created_at"),
            "repository": item.get("repository"),
            "license": item.get("license"),
            "rust_version": item.get("rust_version"),
            "archive_sha256": item["checksum"],
            "registry_metadata_sha256": sha(metadata_path),
            "release_vcs_info": json.loads(vcs_path.read_text()) if vcs_path.exists() else None,
            "source_files_sha256": {p.relative_to(source).as_posix(): sha(p)
                                    for p in sorted(source.rglob("*")) if p.is_file()},
            "limitations": "Checks captured file consistency, not current registry authenticity, Git-tree equality, or verification-fork equivalence; does not build or execute crate code.",
        }
        (stage / "manifest.json").write_text(json.dumps(record, indent=2) + "\n")
        check(stage)
        stage.rename(output)
    finally:
        if stage.exists():
            shutil.rmtree(stage)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name", nargs="?")
    parser.add_argument("version", nargs="?")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--metadata-file", type=Path, help="offline input: captured version API response")
    parser.add_argument("--archive-file", type=Path, help="offline input: matching .crate archive")
    parser.add_argument("--check", type=Path, metavar="DIRECTORY", help="check saved capture offline, read-only")
    args = parser.parse_args()
    if args.check:
        if args.name or args.version or args.output or args.metadata_file or args.archive_file:
            parser.error("--check takes only a saved capture directory")
        record = check(args.check.resolve())
    else:
        record = capture(args)
    print(f"OK: {record['crate']['name']} {record['crate']['version']}; "
          f"archive checksum and {len(record['source_files_sha256'])} source files checked.")
    print("Recorded-file consistency only; no Git/fork equivalence claim, build, proof, or publication.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
