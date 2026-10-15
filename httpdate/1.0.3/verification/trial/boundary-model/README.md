# Standard-library boundary specification experiment

This independent crate is not loaded by the `httpdate` implementation. It investigates whether missing specifications in Creusot 0.13.0 can be supplied to verify thin public-API adapters. **The results are conditional proofs that trust the standard-library specifications below**, not proofs of the Rust standard-library implementation. They also do not prove the public `httpdate` API.

To rerun, from the repository root execute `bash httpdate/1.0.3/verification/trial/boundary-model/run.sh`. The target platform is 64-bit Linux. The run uses an independent Cargo.lock, builds dependencies on the first run, generates fresh Coma, proves with `--no-cache`, and saves input fingerprints and the run log.

## Assumption review record

Primary compared the following contracts with the documentation and implementation in the pinned Rust source. The referenced Rust is nightly commit `91fe22da8084a1c9e993d78d4a56f22ab8396236`, used by Creusot. URLs and SHA-256 hashes of retrieved content are saved in [reference/manifest.json](reference/manifest.json). The full standard-library implementation was not reverified.

| Assumption | Basis and limitation |
| --- | --- |
| `time_ns(SystemTime)` represents integer nanoseconds from a fixed origin | Opaque model. No assumption is made about clock reads or monotonicity across runs. It models the timestamp of an existing copied value. |
| The model value of `UNIX_EPOCH` is 0 | The definition in `std/src/sys/time/unix.rs` uses `Timespec::zero()`. The external constant is made opaque with a direct `ensures`. This was needed to avoid translating the constant's private fields. |
| `duration_since` returns `Ok` for a nonnegative difference and `Err` for a negative difference | Corresponds to the public documentation in `std/src/time.rs` and `Timespec::sub_timespec`. The model covers only differences representable as Duration; it does not specify the contents of the `Err` value. |
| Epoch + Duration returns the sum of the timestamps | **Limited to 64-bit Linux.** Only the narrow range from origin 0 to before year 10000 is covered. It fits signed 64-bit seconds and normalized nanoseconds in Unix Timespec, and cannot reach the overflow condition in `checked_add_duration`. Do not extend this to general SystemTime addition or other platforms. |
| `from_utf8` on an ASCII byte slice succeeds and preserves each byte as its code point | Corresponds to the UTF-8 documentation in `core/src/str/mod.rs`. Acceptance or rejection of non-ASCII input is outside this contract. |
| `str::is_ascii` is true exactly when every code point is below 128 | Standard-library strings contain valid UTF-8. In the ASCII range, code point count equals byte count. |
| ASCII `str::trim` removes Unicode whitespace at both ends | In the ASCII range, the relevant bytes are 9..13 and 32. **This includes 11 (vertical tab).** Reusing the `u8::is_ascii_whitespace` set would differ from Rust's `str::trim`. The contract specifies the interior substring and the non-whitespace conditions at both ends. |
| ASCII `str::as_bytes` returns each code point as a byte with the same value | Content preservation is limited to ASCII. No additional assumption is made for general multibyte UTF-8. |

Existing creusot-std models for Duration, Result, Option, slices, integers, and string View remain trusted as well. The `httpdate` algorithm is not trusted. Before adopting these additional external specifications in the main crate, review the target platform, sufficiency of the specifications, and reachability of every public call again.

## Trial targets

- `bounded_epoch_seconds`: conversion from SystemTime to seconds over the supported range, truncating subsecond precision. Known out-of-range panics are outside its precondition.
- `epoch_time`: Epoch + Duration from seconds over the supported range.
- `time_boundary_roundtrip`: closed composition of the two functions above; dependence on external specifications remains.
- `ascii_text`: conversion of 29 ASCII bytes to `&str` while preserving character count and content.
- `normalized_ascii`: reject non-ASCII, trim ASCII whitespace at both ends, and preserve content when converting to bytes.

Native tests check supported boundaries, subsecond values, out-of-range panics, UTF-8 content preservation for all 128 ASCII values, whitespace classification, and Unicode rejection. These are execution examples that sanity-check the assumptions, not formal proofs of standard-library specifications.

Formatter output, String allocation, Hash, and I/O error models are not added here.
