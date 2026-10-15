#!/usr/bin/env python3
"""Validate fresh closed proof sessions and bind evidence to unchanged inputs."""
import datetime
import hashlib
import json
import os
import re
import tempfile
from pathlib import Path
import shutil
import sys
import subprocess

CORE_TARGETS = tuple("date/" + name for name in (
    "toint_1", "toint_2", "toint_4", "parse_imf_fixdate", "imf_bytes",
    "is_leap_year", "from_unix_seconds", "to_unix_seconds",
    "imf_roundtrip", "seconds_roundtrip", "civil_day_injective",
    "calendar_roundtrip", "is_valid_date", "parse_date_bytes",
    "valid_imf_roundtrip", "asctime/parse_asctime",
    "rfc850/parse_rfc850_date", "rfc850/parse_rfc850_date/wday",
    "asctime/encoding_laws", "rfc850/encoding_laws", "valid_datetime_injective"))
PUBLIC_TARGETS = (
    "parse_http_date", "fmt_http_date", "date/system_time_roundtrip",
    "date/impl_HttpDate/as_raw", "date/impl_HttpDate/from_raw",
    "date/impl_HttpDate/imf_string", "date/impl_FromStr_for_HttpDate/from_str",
    "date/impl_From_for_HttpDate/from", "date/impl_From_for_SystemTime/from",
    "date/impl_From_for_SystemTime/from__refines",
    "date/impl_PartialEq_for_HttpDate/eq", "date/impl_PartialEq_for_HttpDate/eq__refines",
    "date/impl_Ord_for_HttpDate/cmp", "date/impl_Ord_for_HttpDate/cmp__refines",
    "date/impl_PartialOrd_for_HttpDate/partial_cmp",
    "date/impl_PartialOrd_for_HttpDate/partial_cmp__refines",
    "date/impl_Clone_for_HttpDate/clone", "date/impl_Clone_for_HttpDate/clone__refines",
    "date/impl_Clone_for_RawDate/clone", "date/impl_Display_for_HttpDate/fmt",
    "impl_Display_for_Error/fmt", "stdlib_specs/trim_unique", "stdlib_specs/bytes_unique")
HASH_TARGETS = (
    "date/hash/impl_Hash_for_HttpDate/hash",
    "date/hash/impl_Hash_for_HttpDate/hash__refines",
    "date/hash/equal_dates_hash_equally", "date/hash/default_hasher_equality")
ERROR_TARGETS = (
    "impl_Error_for_Error/source", "impl_Error_for_Error/cause",
    "impl_Error_for_Error/description", "impl_From_for_Error/from",
    "impl_From_for_Error/from__refines", "error_conversion_observable")
DEBUG_TARGETS = (
    "debug_support/debug_mode", "debug_support/write_ascii",
    "debug_support/concat_law", "debug_support/write_prefix", "debug_support/digit_byte", "debug_support/write_decimal",
    "debug_support/write_field_u8", "debug_support/write_field_u16",
    "date/debug/impl_Debug_for_HttpDate/fmt", "impl_Debug_for_Error/fmt")
TARGETS = CORE_TARGETS + PUBLIC_TARGETS + HASH_TARGETS + ERROR_TARGETS + DEBUG_TARGETS
EXPECTED_OPEN = {
    "date/impl_From_for_HttpDate/from__refines":
        "Unconditional std From precondition cannot imply the supported SystemTime range; "
        "native pre-epoch/year-10000 inputs panic. Bounded implementation body is proved separately."
}
EXCLUDED = {
    "date/impl_Debug_for_RawDate/fmt": "Private diagnostic formatting; content unmodeled.",
}
STDLIB_ASSUMPTIONS = (
    "time_ns", "UNIX_EPOCH", "SystemTime::duration_since", "SystemTime + Duration",
    "str::from_utf8 (ASCII)", "str::is_ascii", "str::trim (ASCII)", "str::as_bytes (ASCII)",
    "formatter_output", "append_sink", "Formatter as fmt::Write::write_str (conditional Ok append)",
    "supported_hasher", "hash_state", "hash_step_u8", "hash_step_u16", "hash_finish",
    "Hash::hash (supported hasher domain)", "Hasher::finish", "u8::hash", "u16::hash",
    "DefaultHasher::new", "DefaultHasher::finish",
    "io_kind", "io_payload", "io::Error::new (direct concrete Error payload)", "io::Error::kind",
    "debug_options", "Formatter::flags", "Formatter::width", "Formatter::precision",
    "Formatter::fill", "Formatter::align", "Formatter::debug_struct", "Formatter::debug_tuple",
    "DebugStruct::field", "DebugStruct::finish", "DebugTuple::field", "DebugTuple::finish",
    "u8::Debug::fmt (conditional decimal)", "u16::Debug::fmt (conditional decimal)",
    "unit::Debug::fmt (conditional unit text)")


def session(base, target):
    path = base / target / "proof.json"
    modules = json.loads(path.read_text()).get("proofs")
    if not isinstance(modules, dict) or not modules:
        raise ValueError(f"No proof modules: {path}")
    goals = {f"{module}.{goal}": tree for module, group in modules.items()
             for goal, tree in group.items()}
    function = target.rsplit("/", 1)[-1]
    coma = (base / f"{target}.coma").read_text()
    if function.endswith("__refines"):
        expected = "refines"
    else:
        roots = re.findall(r"^goal (vc_\w+):", coma, re.MULTILINE)
        bodies = re.findall(r"^let (?:rec )?(\w+) ", coma, re.MULTILINE)
        if roots:
            expected = roots[-1]
        elif bodies:
            expected = "vc_" + bodies[-1]
        else:
            raise ValueError(f"No concrete target declaration: {target}")
    if not goals or not any(goal.rsplit(".", 1)[-1] == expected for goal in goals):
        raise ValueError(f"Target verification condition missing: {path}: {expected}")
    # Reconstruct all root goals from the fresh Coma using Why3 independently
    # of proof.json, so omitted auxiliary goals cannot look like a closed run.
    data_home = Path(os.environ["XDG_DATA_HOME"])
    theory = subprocess.run([
        "why3", "prove", "-C", str(data_home / "creusot/creusot_why3.conf"),
        "-L", str(data_home / "creusot/share/why3find/packages/creusot"),
        str(base / f"{target}.coma")], check=True, capture_output=True, text=True,
        timeout=30).stdout
    inventory = set()
    module = None
    for line in theory.splitlines():
        header = re.match(r"^theory (\S+)$", line)
        if header:
            module = header.group(1)
        goal = re.match(r"^  goal (\S+)\s*:", line)
        if goal:
            if module is None:
                raise ValueError(f"Goal without a Why3 theory: {target}")
            inventory.add(f"{module}.{goal.group(1)}")
    if not inventory or inventory != set(goals):
        raise ValueError(f"Complete goal inventory mismatch: {target}: "
                         f"missing={sorted(inventory - set(goals))}, "
                         f"unexpected={sorted(set(goals) - inventory)}")
    failed = [goal for goal, tree in goals.items() if not proved(tree)]
    return {"goals": len(goals), "proof_json_sha256": digest(path),
            "coma_sha256": digest(base / f"{target}.coma"), "open_goals": failed,
            "goal_inventory": sorted(inventory)}


def proved(tree):
    if not isinstance(tree, dict):
        return False
    if isinstance(tree.get("prover"), str):
        return bool(tree["prover"])
    if isinstance(tree.get("tactic"), str):
        children = tree.get("children")
        return isinstance(children, list) and bool(children) and all(map(proved, children))
    return bool(tree) and all(
        isinstance(children, list) and bool(children) and all(map(proved, children))
        for children in tree.values()
    )


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def input_hashes():
    inputs = [Path(p) for p in ("Cargo.toml", "Cargo.lock", "../../rust-toolchain.toml",
                               "../../scripts/activate.sh", "../../scripts/activate-local.sh", "why3find.json", "scripts/verify.sh",
                               "scripts/check-proofs.py", "scripts/why3.conf", "crate/Cargo.toml",
                               "../../verification/toolchain-repositories.json",
                               "../../verification/toolchain-opam.export",
                               "verification/trial/reference/date.rs", "verification/stdlib-assumptions.md",
                               "verification/specification.md", "verification/stdlib-reference.json",
                               "verification/trial/check-evidence-guards.py")]
    inputs += sorted(Path("crate/src").rglob("*.rs"))
    inputs += sorted(p for p in Path("verification/platform-review").rglob("*") if p.is_file())
    # Bind the selected tool executables as well as source and version pins.
    for command in ("cargo-creusot", "cargo-proofs", "why3find", "why3",
                    "alt-ergo", "z3", "cvc4", "cvc5", "rustup"):
        executable = shutil.which(command)
        if executable is None:
            raise ValueError(f"Required tool not on activated PATH: {command}")
        inputs.append(Path(executable).resolve())
    for channel in ("1.91.0", "nightly-2026-06-22"):
        compiler = subprocess.check_output(
            ["rustup", "which", "--toolchain", channel, "rustc"], text=True).strip()
        inputs.append(Path(compiler).resolve())
    inputs.append(Path(os.environ["XDG_DATA_HOME"]) / "creusot/toolchains/nightly-2026-06-22/bin/creusot-rustc")
    return {str(path): digest(path) for path in inputs}


def main():
    if sys.argv[1:] == ["--snapshot"]:
        print(json.dumps(input_hashes(), indent=2))
        return
    if sys.argv[1:] == ["--targets"]:
        print("\n".join(TARGETS))
        return
    if sys.argv[1:] == ["--open-targets"]:
        print("\n".join(EXPECTED_OPEN))
        return
    run = Path(sys.argv[1])
    captured_inputs = json.loads((run / "inputs.json").read_text())
    if captured_inputs != input_hashes():
        raise ValueError("Inputs changed after this run started; rerun verification.")
    base = run / "coma/verif/httpdate_rlib"
    generated = {str(path.relative_to(base)).removesuffix(".coma") for path in base.rglob("*.coma")}
    expected = set(TARGETS) | set(EXPECTED_OPEN) | set(EXCLUDED)
    if generated != expected:
        raise ValueError(f"Generated inventory mismatch: missing={sorted(expected - generated)}, "
                         f"unclassified={sorted(generated - expected)}")
    for path in Path("crate/src").rglob("*.rs"):
        if path.name != "stdlib_specs.rs" and "#[trusted]" in path.read_text():
            raise ValueError(f"Application-level trusted declaration forbidden: {path}")
    sessions = {}
    for target in TARGETS:
        item = session(base, target)
        if item["open_goals"]:
            raise ValueError(f"Unproved goals: {target}: {item['open_goals']}")
        item["boundary"] = ("Creusot/creusot-std only" if target in CORE_TARGETS or
                            any(name in target for name in ("impl_PartialEq", "impl_Ord", "impl_PartialOrd", "impl_Clone")) or
                            target.endswith(("as_raw", "from_raw", "trim_unique", "bytes_unique")) else
                            "Conditional reviewed standard-library model; see assumption ledger")
        sessions[target] = item
    open_sessions = {}
    for target, reason in EXPECTED_OPEN.items():
        item = session(base, target)
        if not item["open_goals"]:
            raise ValueError(f"Expected-open condition changed; review and reclassify: {target}")
        if any(goal.rsplit(".", 1)[-1] != "refines" for goal in item["open_goals"]):
            raise ValueError(f"Unexpected unresolved obligation in expected-open session: {target}")
        item["reason"] = reason
        open_sessions[target] = item
    if (run / "open-prove.exit").read_text().strip() != "1":
        raise ValueError("Expected-open proof must finish normally with why3find unproved-file exit 1.")

    if captured_inputs != input_hashes():
        raise ValueError("Inputs changed during evidence validation; rerun verification.")

    manifest = {
        "generated_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "scope": "Byte/calendar core and actual public parse/format/conversion/comparison/clone/Display/Hash/Error/Debug bodies and equality-compatible Hash/IO observation harnesses; "
                 "public boundaries conditional on reviewed stdlib models; one forward-From trait refinement open.",
        "input_base": "httpdate/1.0.3",
        "command": "bash httpdate/1.0.3/scripts/verify.sh",
        "cache": False,
        "versions": (run / "versions.txt").read_text().splitlines(),
        "inputs_sha256": captured_inputs,
        "targets": sessions,
        "total_session_goals": sum(item["goals"] for item in sessions.values()),
        "native_tests": "cargo test --locked --release -p httpdate (see tests.log)",
        "application_trusted_assumptions": [],
        "standard_library_assumptions": list(STDLIB_ASSUMPTIONS),
        "assumption_ledger": "verification/stdlib-assumptions.md",
        "rustc_host": subprocess.check_output(["rustc", "-Vv"], text=True).strip(),
        "platform": "Reviewed 64-bit Linux or macOS arm64; supported timestamp range; Display and normal/pretty Debug content require a faithful append sink; Debug additionally requires plain_options; Hash requires deterministic nonpanicking supported hashers and equal initial state",
        "expected_open": open_sessions,
        "excluded_generated": EXCLUDED,
        "generated_target_count": len(generated),
        "goal_inventory_validation": "Why3 reconstructs every root goal from fresh Coma; proof.json must match exactly.",
        "unmodeled_native_interfaces": ["Debug content with non-plain formatting options", "Private RawDate Debug", "Hash::hash_slice operational semantics", "dyn std::error::Error payload observers (get_ref/downcast/into_inner)", "unstable Error::provide and hidden type_id"],
        "interface_limitations": "FromStr and Display method bodies are proved but their standard trait interfaces have no general external contract; "
                                 "no claim about unselected inherited or specialized default methods.",
        "proofs_rs_report": "Not recorded or published; local Creusot evidence only.",
    }
    # Build a complete replacement only after every inventory/input/session check.
    # Keeping old per-target files would misleadingly mix source revisions.
    evidence = Path("verification/evidence/latest")
    evidence.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=".fresh-", dir=evidence.parent))
    try:
        for target in (*TARGETS, *EXPECTED_OPEN):
            destination = stage / target
            destination.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(base / target / "proof.json", destination / "proof.json")
            shutil.copyfile(base / f"{target}.coma", destination / "target.coma")
        for log in ("tests.log", "compile.log", "prove.log", "open-prove.log", "open-prove.exit", "versions.txt"):
            shutil.copyfile(run / log, stage / log)
        (stage / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        backup = evidence.parent / ("historical-" + stage.name.removeprefix(".fresh-"))
        if evidence.exists():
            evidence.rename(backup)
        try:
            stage.rename(evidence)
        except Exception:
            if backup.exists():
                backup.rename(evidence)
            raise
    finally:
        if stage.exists():
            shutil.rmtree(stage)
    print(f"{len(TARGETS)} selected targets proved; {manifest['total_session_goals']} closed session goals. "
          f"{len(open_sessions)} explicitly open trait refinement; {len(EXCLUDED)} excluded generated targets.")
    print(f"Evidence: {evidence}")


if __name__ == "__main__":
    main()
