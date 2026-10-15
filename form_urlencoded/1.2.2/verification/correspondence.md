# Release correspondence and runtime changes

The immutable release snapshot is `capture/source`; the independently verified fork is `crate`. Identity is crates.io `form_urlencoded` 1.2.2, archive SHA-256 `cb4cb245038516f5f85277875cdaa4f7d2c9a0fa0468de06ed190163b1581fcf`. Recorded `.cargo_vcs_info.json` names rust-url commit `91377f48bf35011d042aa5abef9e7f2a0a625aaa`, path `form_urlencoded`, and marks the tree dirty. This records archive provenance, not Git-tree equality.

The implementation uses local checked plus replacement, percent decoding, and byte encoding. Percent decoding preserves malformed escape behavior and the runtime Cow borrowed/owned choice. Parser iterator state tracks the remaining raw suffix; its logic models record both the decoded scalar sequence and whether each returned Cow field is borrowed. `ParseIntoOwned` returns owned strings and tracks the same scalar sequence. Byte serialization groups maximal unchanged-byte runs, emits `+` for space and uppercase `%HH` chunks otherwise, and tracks the exact remaining bytes and size hint.

Runtime changes that support the checked proof boundary are shared by native and Creusot builds: numeric indexed scanner steps and local buffer helpers; parser range-slicing helpers; an explicit `Cow<str>` match when converting to owned strings; ASCII-backed unchecked UTF-8 construction for serializer chunks, including the one-byte numeric `+`; and a debug assertion comparing byte contents rather than pointer identity. These preserve specified output and state behavior. Allocation identity, pointer provenance, and OOM behavior are outside the guarantee.

The latest native differential checks compare the actual fork APIs against an extracted copy of the captured release. The harness retains upstream source hashes and changes only the upstream package name to permit both path packages in one workspace. Its finite cases are summarized in `coverage.md`; they are observed correspondence, not all-input equivalence.

The selected Creusot scope and final proof evidence are tracked separately in `public-api-inventory.md`, `target-inventory.json`, and `results.md`. The completed integrated result and current-input freshness are recorded in `results.md`; earlier diagnostic timeouts are historical. The exact dynamic serializer callback type remains unsupported and is excluded; no callback substitute or semantic assumption is used.

## Standalone native execution

Run `bash form_urlencoded/1.2.2/scripts/run-differential.sh` with ordinary Rust 1.91.0/Cargo, a native linker, Bash, and Python 3. This runs the release comparison, native all-feature tests, and alloc-only build without activating formal tools. Cargo uses locked dependencies and may download missing packages; use `CARGO_NET_OFFLINE=true` for cache-only execution. Caller Cargo/Rustup homes are preserved and `CARGO_TARGET_DIR` is honored. Binding results into formal evidence remains a separate proof workflow.
