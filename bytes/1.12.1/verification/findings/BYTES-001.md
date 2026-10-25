# BYTES-001: Checked variable-width signed reads omit sign extension

The unchanged bytes 1.12.1 release returns a zero-extended positive integer from
`Buf::try_get_int`, `Buf::try_get_int_le` and `Buf::try_get_int_ne` for short negative
inputs. The corresponding `get_int` readers sign-extend those inputs.

The active report draft is
[proofs.toml](../../aeneas/profiles/unpatched/proofs.toml), including the three
`api_paths`. The active native reproducer is under
[`findings/signed-read`](../../aeneas/profiles/unpatched/findings/signed-read/).
The historical independent review and earlier reproductions are linked below.

## How the finding emerged

While working toward Aeneas formal verification of the signed-return contract,
the contract remained unmet. That status alone did not establish a counterexample
or identify the cause. Source review and native reproduction subsequently
confirmed that the checked readers omit sign extension for short negative inputs.
The retained recorder attempt failed during API discovery, rather than producing a
failed behavioral theorem for these readers; this finding is grounded in the
source analysis and runtime counterexamples described below.

## Counterexample and result

For one byte `0xff`, the signed value is -1. `try_get_int(1)` instead returns
`Ok(255)` and consumes one byte. The retained regression checks BE/LE/NE readers
on all-0xff inputs at every width from 1 through 8, comparing the exact remaining
slice too. At widths 1 through 7 the checked value is `2^(8*n)-1`; the unchecked
value is -1. At width 8 both return -1.

This was rerun during this reorganization with Rust 1.91.1 on
`aarch64-apple-darwin`, default features disabled. The regression exits 0 because
it asserts the actual discrepancy and its controls. The separate historical
minimal test asserting the desired `Ok(-1)` exits 101 as expected.

- [Fresh native command, output, compiler and input hashes](../reorganization/native-signed-read.json)
- [Active retained regression source](../../aeneas/profiles/unpatched/findings/signed-read/src/main.rs)
- [Historical regression source](../../aeneas/profiles/default/findings/signed-read/src/main.rs)
- [Historical independent source review](../../aeneas/profiles/default/findings/signed-read/oracle.md)
- [Historical failing minimal assertion](../preview/2026-10-23/minimal.record.json)
- [Recorded formal-attempt status](../preview/2026-10-23/attempt1.json)

## Reproduce locally

After restoring the checksum-pinned source with the version's setup wrapper,
run from `bytes/1.12.1`:

```sh
CARGO_TARGET_DIR="$PWD/.work/signed-read-replay" rustup run 1.91.1 cargo run \
  --offline --locked --quiet \
  --manifest-path aeneas/profiles/unpatched/findings/signed-read/Cargo.toml
```

The source lock pins archive SHA-256
`fc652a48c352aef3ea3aed32080501cf3ef6ed5da78602a020c991775b0aff04`
and upstream commit `76c0fbb54ed4336caf9d2311658a2f4a5627c21d`.
The complete source inventory was checked before the replay.

## Interpretation and upstream status

The checked implementations initialize an eight-byte array with zeros and convert
it to i64; the unchecked implementation applies sign extension. This is a native
counterexample to the desired signed-return contract, not a successful Lean proof
of these public APIs, a memory-safety finding or whole-crate verification.

The original signed specification and exclusions remain unchanged. The fix was
merged upstream in [PR 839](https://github.com/tokio-rs/bytes/pull/839) on
2026-09-03 as [commit 7930d93](https://github.com/tokio-rs/bytes/commit/7930d93d583757e922014312d4aa3e58a415131f) and is present in
current upstream `master`. As checked on 2026-10-25, the latest published release
remains [1.12.1](https://crates.io/crates/bytes), which contains the affected
implementation. This finding therefore concerns the unchanged 1.12.1 release;
it does not claim current upstream master is affected. No release source fix is
included here.
