# bytes: report.findings preview

The maintained [proofs.toml](../../../../aeneas/profiles/default/proofs.toml)
now contains one `[[report.findings]]` entry with only an English `title` and a
Markdown `body`. It describes the previously reproduced signed-read discrepancy.
The scope entry was removed because it repeated the report body. There is no
JSON sidecar for authoring findings.
The native counterexample evidence remains in the [previous experiment](../README.md).

Preview: <http://127.0.0.1:60816/report#findings> while the local server is running.
The browser now shows 56 verified claims and one English finding, with a code
example and source link. The original [browser checks](browser-check.json) and
[session metadata](session.json) preserve the earlier two-finding experiment,
including its live title-reload check. The current editorial update was checked
in the browser without running verification again; its screenshot is retained
at `.work/report-findings-preview/preview-english.png` under the crate version.

## Evidence boundary

This experiment reuses Run `29ae1f77-352a-486c-a5ce-4818ca5d2a72` unchanged.
Its SHA-256 remains
`52f9e47acc32297d24d93ab29e7dab68f68450de8792ad1280477602a83e9e62`.
The tool configuration and theorem mappings are unchanged. Neither Lean nor the
native bug reproducer was rerun for this editorial change. The findings are
unpublished draft prose, not additional successful proof results.

The previous experimental recorder is retained. A separate copy in
`.work/report-findings-preview/cli` adds the new report authoring support and
removes `--findings`; [preview-cli.patch](preview-cli.patch) captures its Rust
changes relative to the prior experiment. The production reader bundle is copied
into that CLI. [session.json](session.json) records source and binary hashes.
It retains the experimental local-only publication guard and source-bound API
aliases. Public API catalogue warnings remain visible. The prototype has not been
installed or released, and pinned tool caches and locks have not been changed.

The source checkout's ignored `.work/report-findings.toml` links to the maintained
profile for live editorial reloads. The recorded source's tracked files remain
unchanged. Since recorder storage is scoped by configuration path, an exact copy
of the existing SARIF is used in the new experiment's local record directory.
The old recording and preview directory are preserved.

## Reopen

From the crate-proofs repository, with the retained local session files:

```sh
bash bytes/1.12.1/verification/preview/2026-10-23/report-findings/start-preview.sh
```

The script prints a localhost URL. Add `--port 60816` to reuse the shown port
when it is free. Edit the maintained TOML and reload the browser to change prose.
The launcher uses the pinned local Rust 1.91.1 installation directly and the
separate experimental preview binary.

In the implemented publication workflow, `report.findings` is used only when
creating a new report. Later additions and edits use the Web/API; revising the
report never reposts this array. Nothing was pushed, uploaded, published or
deployed during this experiment.
