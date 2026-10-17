# Minimal pinned Aeneas reproductions

These are independent tool-boundary examples, not copies of ipnet algorithms or
counterexamples to ipnet behavior. The standalone Cargo workspace has its own
lockfile and no dependency on ipnet. `bash reproduce.sh` checks the version's
pinned tool revisions, active local compatibility patchset, and binary hashes.
It compiles the examples with Rust 1.91.1, then runs the pinned Charon/Aeneas
on one `crate::` entry at a time. It creates fresh
ignored `runs/check-*/` logs and succeeds only if the documented failures
recur. Fresh logs and rejected generated Lean text are packaged in
`evidence/latest/`; SHA-256 hashes and tool identity are in `evidence.json`. The
accepted 625 ipnet proof identities and upstream source are unchanged.

| Entry in `src/lib.rs` | Fresh result | Exact boundary |
| --- | --- | --- |
| `mutable_dyn_write` | Charon succeeds; Aeneas fails at line 21 | The `&mut Sink` to `&mut dyn fmt::Write` unsizing cast is unsupported (`InterpExpressions.ml:945`). The callback must update the original sink; dropping the cast or treating it as a shared borrow would lose effects. This is the same kind of cast that blocks the corrected heapless candidate's concrete Serialize bodies. It does not imply that all dynamic traits are unsupported. |
| `next_ascii` through `borrowed_callback` | Charon and Aeneas emit Lean; Lean rejects two types | The generated generic `FnOnce` dictionary says `call_once : F → Cursor → Result (Option T)`, but the concrete closure body returns `Result (Option U8 × Cursor)` to preserve its mutable argument. The call site expects a product and receives only `Option T`. This independently reproduces the borrowed-callback signature defect with the accepted locally patched backend from the historical ipnet parser research; the earlier context-join patch was not applied here. |
| `extend_bytes` | Charon succeeds; Aeneas fails before local body translation | Aeneas raises an internal error while translating the core `Iterator` trait signature (`SymbolicToPureTypes.ml:1004–1005`). This tiny example does **not** reach the deeper `Vec::extend_desugared` capacity/raw-pointer boundary previously observed for actual ipnet aggregate. Both observations remain separate. |

Run the exact pinned commands with:

```bash
cd ipnet/2.12.2/verification/issue-repros/aeneas
bash reproduce.sh
```

For a single target, the script issues:

```bash
charon cargo --preset=aeneas --start-from crate::TARGET \
  --dest-file "$OUT/repro.llbc" -- --lib --locked
aeneas -backend lean -dest "$OUT" "$OUT/repro.llbc"
```

For `next_ascii`, it additionally runs `lake env lean` on the generated file
from the accepted ipnet Lean package. `reproduce.sh` never edits tool source or
application source, and none of the rejected generated files are imported as
proofs. The full ipnet parser and aggregate attempts, with their larger
source-specific dependencies, remain documented in
`../../blockers/ipv4-parser-callback/` and
`../../blockers/aggregate-extend/`.
