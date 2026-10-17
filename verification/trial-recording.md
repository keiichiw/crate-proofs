# Record diagnostic trials

Use this optional wrapper when exploratory commands or long-running verification
steps need failure/interruption records. It supplements the version's verifier;
it does not replace source fingerprints, native checks, theorem audits or proof
manifests. Python 3.11+ and a POSIX host are required.

From the repository root, after activating the target's own environment:

```bash
python3 scripts/record-trial.py \
  --output <crate>/<version>/verification/runs/<new-trial-id> \
  --stage aeneas \
  --input <crate>/<version>/verification/aeneas.json \
  --purpose 'Test the selected dependency boundary' \
  -- python3 scripts/aeneas-extract.py <crate>/<version> \
     --config <crate>/<version>/verification/aeneas.json \
     --output <crate>/<version>/verification/runs/<new-extraction-id>
```

Both directories must be new. Choose a version-local ignored trial directory;
do not mix crate-specific evidence into shared scripts. `--input` can be repeated
for specific files; it is a selected input identity, not a complete fingerprint
of source, tools or transitive dependencies. `--parent-trial` and `--purpose` are
optional metadata supplied by the caller, not inferred causal relationships.
The wrapper records argv literally and does not invoke a shell or retry commands.
Avoid putting credentials in argv; no environment dump is taken.

The initial record is written before starting the child. Normal completion,
nonzero exit, spawn failure and handled interruption retain their records.
An abrupt kill or host failure may leave only the initial record: treat it as
unknown, not a failed or successful proof. Recorded monotonic duration measures
this command's wall time, not agent thinking time or improvement over a baseline.
The wrapper's process result never certifies proof success.
`trial.json` separates the child's raw `child_returncode` (negative for a signal)
from the shell-compatible `wrapper_exit_code`. Standard output and error go to
`stdout.log` and `stderr.log` rather than the terminal. Relative `--input` paths
are resolved against `--cwd`; `--output` is relative to the invoking directory.
On SIGINT/SIGTERM the child process group is signaled and, within five seconds,
remaining group members are killed. Processes that create a separate session are
outside this cleanup boundary. SIGKILL cannot be handled by the recorder.

For a read-only diagnostic summary, inspect `python3 scripts/diagnose-trial.py --help`
and supply the stage and saved logs. Its matches are observations with line context
and file hashes, not root-cause assertions. Known diagnostic prefixes are used
instead of arbitrary `error`/`Exception` substring matches; unmatched logs remain
unclassified. In particular, passing should-panic tests, imported module names and
paths are not failures. Keep original logs even when a summary is available.

Existing historical records may lack timestamps, exits or parent links. Preserve
those fields as unknown; filesystem mtimes are not execution timestamps. Archives
copied from the same run are not independent trials. Do not compute failure rates
from keyword matches or treat unclassified experiments as failed proofs.

The wrapper can run outside an unchanged accepted verifier, so old evidence need
not be rewritten. If it becomes part of a maintained verifier's trusted execution
path, include its code/configuration in that verifier's input fingerprint and
produce fresh evidence under the normal version-local workflow.
