# form_urlencoded 1.2.2 verification scope

Follow the repository Creusot skill and `verification/plan.md`, `specification.md`, `coverage.md`, and `public-api-inventory.md` before changing verification code. The release snapshot is in `crate/`; keep this version in its own Cargo workspace and lockfile.

The current milestone expands from the historical five-helper byte core toward the full public API. Preserve each verified bundle as historical when its input fingerprints become stale. Keep selected body proofs distinct from trait refinements, inherited/blanket methods, caller-provided callbacks, and standard-library assumptions. Update the complete public API inventory and generated-target classification before making expanded guarantees.

Keep application algorithms and percent decoding free of `trusted` assumptions. Standard-library models belong in a separate ledgered module and may assume only the authorized library behavior. Do not claim whole-crate coverage until every public API inventory row has either a verified body/refinement or a specifically reviewed and documented standard-library boundary.

Record annotation-only changes separately from runtime changes and keep the release capture immutable. Never log in, push, publish, deploy, or publish evidence without explicit authorization.
