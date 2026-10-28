# ipnet 2.12.2 — managed Aeneas profile

```bash
bash scripts/setup.sh
bash scripts/verify.sh
bash scripts/verify.sh --offline
```

The release archive and complete source inventory are fixed in `source.lock.json`.
The standalone Cargo workspace compiles unchanged `.work/source` bytes and preserves
release features/dependencies. Default, no-default and all-feature native tests run
separately from the formal checks.

See the [management guide](../../verification/aeneas-management.md) and the
[default profile](aeneas/profiles/default) for the independent specification, theorem
inventory, API mappings, generated target models and exact tool locks. Both Aeneas
and Charon have fixed, separately described patches; their resulting trees are checked.
The original LLBC runtime-check settings, standard Rust source hashes and checked
shift overflow examples are mandatory. The extraction and standard-library models
remain trusted translation boundaries. Runtime-model claims do not cover general
const evaluation or panic formatting/abort equivalence.

[Results](aeneas/profiles/default/results.md) distinguish accepted runs from Linux
candidates and historical evidence. Only named audited contracts establish coverage.
Only explicitly inventoried compatibility fixtures remain under evidence/legacy; complete original records are in the local archive identified by evidence/archive.json.
Local verify requires no push. The optional record wrapper uses standard Lake/CLI
audits and retains committed/pushed-source requirements; repository scripts and
preparation/native logs are excluded from SARIF. Setup/verify never publish.



Verification findings are recorded [within this version](verification/findings/README.md).
