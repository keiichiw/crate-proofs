# Finding storage policy

Findings belong to their owning crate/version. Keep shared documentation limited
to format and storage rules; do not maintain cross-crate finding counts or status
tables. Read each version’s verification/findings directory for its own records.
Multiple counterexamples may share a cause; do not count each profile or integer
width as a new bug.

## Store a new finding

Copy [the finding template](templates/finding.md) to
`<crate>/<version>/verification/findings/<ID>.md`. Assign a stable crate-local ID,
keep minimal reproduction source under that version, and link the finding from its
README or results. For nested independent workspaces, keep the finding under that
workspace. Aeneas and Creusot can use the same record format.

Classify implementation bugs, documentation mismatches, verifier defects,
unsupported boundaries, specification questions and environment failures separately.
Track confidence independently from resolution. Preserve source identity,
preconditions, expected/observed state and exact reproduction conditions; never
upgrade an old observation to a fresh verification claim. Unknown fields stay
explicitly unknown. No upstream report or publication is implicit.

Commit the short finding and minimal reproducer. Complete logs and repeated models
belong in ignored .work or a checked local archive; record its digest, exact member
and availability following the [publication policy](publication.md). Do not rewrite
frozen historical evidence to fit this format. Existing records can be wrapped by
a new finding that links to the original, retaining its scope and caveats.
