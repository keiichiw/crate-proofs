# Selected local evidence

`check-mxgcyMMw/` is an unchanged copy of the successful fresh local verifier
run made on 2026-10-16. Its `result.json` records the 46 audited theorem roots,
five mapped APIs, model comparison, separate native tests, and input freshness.
`manifest.json` hashes every copied run file, including `run.log`; it is a
packaging manifest, not an additional proof or a proofs.rs recording.
The manifest records the original log's modification time in UTC; the run
finished on 2026-10-16 local time (2026-10-17 UTC). To check this saved
package against the maintained generated model and theorem inventory without
accessing the ignored run, execute from the version root:

```bash
python3 verification/evidence/check-evidence.py verification/evidence/check-mxgcyMMw
```

The original execution remains under ignored `verification/runs/check-mxgcyMMw/`.
Older ignored runs, failed probes, and diagnostic logs were not copied or
rewritten. This package contains the selected accepted run only.
