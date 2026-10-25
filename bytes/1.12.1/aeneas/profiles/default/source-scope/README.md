# Safe-source consumption survey

The user asked to finish feasible consumption verification without unsafe application code. Here, “safe” refers to the selected unchanged Rust dependency bodies, relative to Aeneas's standard-library models. It does not establish the memory safety of the standard library or of arbitrary Buf implementations. In particular, a generic Buf law is an explicit obligation on an implementation, not an automatically true property of the Rust trait.

`functions.json` is a source-location aid: 458 unexpanded function/method records across the 19 checksum-confirmed source files. It records direct unsafe expressions, signature/trait unsafety, calls, methods and macro invocations. It is **not** a public API completeness audit or a transitive safety proof. Macro definitions/expansions and inline nested modules are not recursively enumerated. Empty unsafe-expression lists never imply a safe transitive dependency closure.

Reproduce the source inventory with the pinned Rust toolchain selected by `scripts/env.sh`:

```sh
CARGO_TARGET_DIR=/workspace/work/bytes-inventory-target cargo run --locked \
  --manifest-path verification/source-scope/inventory-tool/Cargo.toml -- upstream
```

The JSON source hashes refer to the original upstream files. The saved inventory removes doc attributes to reduce noise; executable locations and cfg attributes are preserved. The generator emits doc attributes as well, so this is a semantic source-location reproduction, not a byte-for-byte regeneration command for the saved JSON.

## Dependency review

| Family | Original source / boundary |
|---|---|
| Slice Buf remaining/chunk/advance/copy | `src/buf/buf_impl.rs`, concrete safe slice implementation. Standard slice/index/copy models remain trusted. |
| Take / Chain consumption and IntoIter | `src/buf/take.rs`, `chain.rs`, `iter.rs`. Retained Buf methods require actual dictionary correspondence and explicit sequence laws. |
| Default byte reads and copy loop | `src/buf/buf_impl.rs`. Actual checked-copy loop termination and prefix/suffix/error laws are proved for arbitrary lawful fragmentation. The default unchecked copy wrapper is distinct; consult the final ledger for its field-model boundary. |
| Variable-width uint/int reads | Safe BE/LE arms of `buf_try_get_impl!` at `src/buf/buf_impl.rs:43–74`; zero-filled 8-byte temporary, copy, scalar byte conversion. Signed checked/unchecked mismatch has a native counterexample in `../findings/signed-read`. |
| Fixed-width integer readers >=16 bits | First macro arm at `src/buf/buf_impl.rs:13–42` uses an unsafe pointer reinterpretation in the fast path. The safe fallback alone cannot justify verifying the unchanged whole method without unsafe. Float readers depend on these fixed-width methods. |
| Reader / Writer field wrappers | `src/buf/reader.rs` / `writer.rs`; constructors and reference/ownership projections have no Buf/BufMut calls. Unused trait bounds may be erased by Charon without assuming unsafe BufMut behavior. |
| Reader std I/O | `reader.rs:66–80`; safe source composition. The independently selected consume body avoids the unused Error type and is verified; read/fill_buf retain a std I/O error/trait-model boundary, not source unsafety. |
| std Cursor Buf | `buf_impl.rs:2934–2960`; safe source. Original standard Cursor representation/getters/setter and actual Slice/Shared AsRef are transparently extracted; the maintained Cursor contracts add exact consumption with explicit 64-bit premises. Two arithmetic helper proofs alone would be insufficient. |
| VecDeque Buf | `src/buf/vec_deque.rs`; safe source but requires VecDeque len/as_slices/drain models. Cannot accept opaque application leaves. |
| Vectored reads | Default/Chain bodies require std IoSlice modeling. Take's implementation uses explicit unsafe lifetime transmute. Distinguish these boundaries. |
| Range helper | `src/lib.rs:135–173`; safe source with an independently reproduced extractor failure. Not classified as unsafe. |
| copy_to_bytes, Bytes/BytesMut owning operations | Allocation/sharing/vtable and unsafe representation dependencies, outside this safe-consumption closure. A safe public signature or safe-looking leaf body does not prove a safe dependency closure. |
| BufMut and writable Limit operations | Unsafe trait/storage and advance_mut obligations. Prior field-only Limit proofs do not verify writes. Writer::write depends on BufMut and is likewise excluded. |

For accepted theorem coverage consult `theorems.json` and the latest successful result, rather than this source survey. For safe families that cannot be accepted, preserve an exact extraction reproduction and identify unsupported leaves or translator failures. Merely low priority is not a blocker.
