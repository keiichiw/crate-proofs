#!/usr/bin/env python3
"""Check the pinned crates.io release correspondence record offline by default."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tarfile
import tempfile
import urllib.error
import urllib.request
from pathlib import Path, PurePosixPath


VERSION_ROOT = Path(__file__).resolve().parents[1]
CORRESPONDENCE = VERSION_ROOT / "verification" / "correspondence"
RECORD_PATH = CORRESPONDENCE / "release.json"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def verify_local(record: dict) -> list[str]:
    errors = []
    for archive_name, entry in record["reference_files"].items():
        path = CORRESPONDENCE / entry["path"]
        if not path.is_file():
            errors.append(f"missing vendored file: {entry['path']}")
            continue
        actual = sha256_file(path)
        if actual != entry["sha256"]:
            errors.append(f"SHA-256 mismatch: {entry['path']} ({actual})")

    vcs_entry = record["reference_files"][".cargo_vcs_info.json"]
    vcs_path = CORRESPONDENCE / vcs_entry["path"]
    if vcs_path.is_file():
        try:
            vcs_info = json.loads(vcs_path.read_text(encoding="utf-8"))
            release_sha = record["upstream"]["release_git_sha"]
            if vcs_info["git"]["sha1"] != release_sha:
                errors.append("vendored .cargo_vcs_info.json SHA does not match release_git_sha")
            if vcs_info.get("path_in_vcs") != "":
                errors.append("vendored .cargo_vcs_info.json path_in_vcs is not empty")
        except (OSError, json.JSONDecodeError, KeyError, TypeError) as exc:
            errors.append(f"invalid vendored .cargo_vcs_info.json: {exc}")

    registry = record["registry"]
    metadata_path = CORRESPONDENCE / registry["metadata_capture_path"]
    if not metadata_path.is_file():
        errors.append(f"missing captured registry metadata: {registry['metadata_capture_path']}")
    else:
        metadata_bytes = metadata_path.read_bytes()
        metadata_hash = sha256_bytes(metadata_bytes)
        if metadata_hash != registry["metadata_capture_sha256"]:
            errors.append(f"captured registry metadata SHA-256 mismatch: {metadata_hash}")
        try:
            metadata = json.loads(metadata_bytes)
            version = metadata["version"]
            expected = {
                "crate": record["crate"]["name"],
                "num": record["crate"]["version"],
                "checksum": registry["archive_sha256"],
                "created_at": registry["published_at"],
            }
            for field, value in expected.items():
                if version.get(field) != value:
                    errors.append(
                        f"captured registry metadata {field} is {version.get(field)!r}, "
                        f"expected {value!r}"
                    )
        except (json.JSONDecodeError, KeyError, TypeError) as exc:
            errors.append(f"invalid captured registry metadata: {exc}")

    saved = record["upstream"]["saved_trial_reference"]
    saved_path = VERSION_ROOT / saved["path"]
    if not saved_path.is_file():
        errors.append(f"missing saved trial reference: {saved['path']}")
    else:
        actual = sha256_file(saved_path)
        if actual != saved["sha256"]:
            errors.append(f"SHA-256 mismatch: {saved['path']} ({actual})")
    return errors


def verify_origin(record: dict) -> list[str]:
    origin = Path("/workspace/httpdate")
    if not origin.is_dir():
        return ["optional origin check requested but /workspace/httpdate is absent"]
    errors = []
    expected_head = record["upstream"]["copied_git_sha"]
    try:
        head = subprocess.check_output(
            ["git", "-C", str(origin), "rev-parse", "HEAD"], text=True
        ).strip()
        dirty = subprocess.check_output(
            ["git", "-C", str(origin), "status", "--porcelain"], text=True
        ).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        return [f"cannot inspect optional origin repository: {exc}"]
    if head != expected_head:
        errors.append(f"origin HEAD is {head}, expected {expected_head}")
    if dirty:
        errors.append("origin repository has local changes; refusing origin source comparison")
        return errors
    for name, expected in record["origin_runtime_files"].items():
        path = origin / name
        if not path.is_file():
            errors.append(f"origin source is missing: {name}")
        elif sha256_file(path) != expected:
            errors.append(f"origin source SHA-256 mismatch: {name}")
    release_sha = record["upstream"]["release_git_sha"]
    for name, entry in record["reference_files"].items():
        if not name.startswith("src/"):
            continue
        try:
            released = subprocess.check_output(
                ["git", "-C", str(origin), "show", f"{release_sha}:{name}"]
            )
        except (OSError, subprocess.CalledProcessError) as exc:
            errors.append(f"cannot read release Git source {release_sha}:{name}: {exc}")
            continue
        actual = sha256_bytes(released)
        if actual != entry["sha256"]:
            errors.append(f"release Git source SHA-256 mismatch: {name} ({actual})")
    return errors


def verify_archive(record: dict, archive_path: Path) -> list[str]:
    errors = []
    if not archive_path.is_file():
        return [f"archive file is absent: {archive_path}"]
    expected_archive = record["registry"]["archive_sha256"]
    try:
        actual_archive = sha256_file(archive_path)
    except OSError as exc:
        return [f"cannot read archive file {archive_path}: {exc}"]
    if actual_archive != expected_archive:
        return [f"archive SHA-256 mismatch: {actual_archive}, expected {expected_archive}"]

    try:
        with tarfile.open(archive_path, "r:gz") as archive:
            members = {}
            for member in archive.getmembers():
                relative = PurePosixPath(member.name)
                if len(relative.parts) < 2 or relative.parts[0] != "httpdate-1.0.3":
                    continue
                if member.isfile():
                    members[str(PurePosixPath(*relative.parts[1:]))] = member
            for name, entry in record["reference_files"].items():
                member = members.get(name)
                if member is None:
                    errors.append(f"archive is missing referenced file: {name}")
                    continue
                stream = archive.extractfile(member)
                if stream is None:
                    errors.append(f"cannot read archive member: {name}")
                    continue
                actual = sha256_bytes(stream.read())
                if actual != entry["sha256"]:
                    errors.append(f"archive member SHA-256 mismatch: {name} ({actual})")
    except (OSError, tarfile.TarError) as exc:
        errors.append(f"cannot read crate archive: {exc}")
    return errors


def fetch_archive(record: dict, destination: Path) -> None:
    request = urllib.request.Request(
        record["registry"]["archive_url"],
        headers={"User-Agent": "httpdate-release-correspondence-check/1"},
    )
    with urllib.request.urlopen(request, timeout=30) as response, destination.open("wb") as out:
        while True:
            chunk = response.read(1024 * 1024)
            if not chunk:
                break
            out.write(chunk)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, help="verify a local .crate archive")
    parser.add_argument(
        "--fetch", action="store_true", help="explicitly fetch the pinned archive, then verify it"
    )
    parser.add_argument(
        "--check-origin",
        action="store_true",
        help="also check /workspace/httpdate when it exists and is clean",
    )
    args = parser.parse_args()
    if args.archive and args.fetch:
        parser.error("use either --archive or --fetch")

    try:
        record = json.loads(RECORD_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(f"release record error: {exc}", file=sys.stderr)
        return 1

    try:
        errors = verify_local(record)
        if args.check_origin:
            errors.extend(verify_origin(record))
        if args.archive:
            errors.extend(verify_archive(record, args.archive))
        elif args.fetch:
            with tempfile.TemporaryDirectory(prefix="httpdate-release-check-") as temp_dir:
                fetched = Path(temp_dir) / "httpdate-1.0.3.crate"
                fetch_archive(record, fetched)
                errors.extend(verify_archive(record, fetched))
    except (OSError, KeyError, TypeError, ValueError, urllib.error.URLError) as exc:
        print(f"FAIL: checker could not complete: {exc}", file=sys.stderr)
        return 1
    except Exception as exc:
        print(f"FAIL: unexpected checker error: {exc}", file=sys.stderr)
        return 1

    if errors:
        for error in errors:
            print(f"FAIL: {error}", file=sys.stderr)
        return 1

    mode = "local source hashes"
    if args.archive:
        mode += " + supplied archive"
    elif args.fetch:
        mode += " + fetched pinned archive"
    if args.check_origin:
        mode += " + clean origin checkout"
    print(f"OK: httpdate 1.0.3 correspondence verified ({mode}).")
    if args.archive or args.fetch:
        print(
            "The recorded crates.io archive checksum was verified against the archive; "
            "this does not authenticate current registry state."
        )
    else:
        print(
            "Vendored files and captured metadata were checked against the local release record; "
            "no crate archive was read and registry authenticity was not checked."
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
