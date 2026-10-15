# percent-encoding 2.3.2 verification scope

Follow the repository-root `.agents/skills/creusot-verification/SKILL.md` and the local `verification/plan.md`, `specification.md`, and `public-api-inventory.md` before changing verification code. The immutable release capture is under `capture/`; the independent workspace and proof fork are under `crate/`.

The proof depends on the checked `form_urlencoded 1.2.2` fork through the package alias `form-model`. Its own `percent-encoding` dependency remains the registry package. Never alter either dependency globally or edit the verified form_urlencoded fork as part of this scope.

Keep application algorithms free of trusted assumptions. Verification proceeds through the feasible public scope in this order: exact Clone state, iterator size hints, decoder trace/IteratorSpec refinement, encoder trace/IteratorSpec refinement, then supported Cow/UTF-8/Display/equality/Debug APIs. The current evidence bundle may cover only an earlier subset; maintain current selected/open/excluded status in `verification/target-inventory.json` and preserve previous runs as historical evidence. The `AsciiSet` mask constants and core set operations are selected; `add` and `remove` contracts cover only inputs below 128, their nonpanicking index domain. Native iterator behavior must remain the implementation under proof. Iterator laws and refinements must not be inferred from a helper-body proof, and an unsupported API must be excluded with its diagnostic rather than omitted silently.

Keep the capture immutable. Distinguish proof-only cfg adaptations from runtime changes and report native tests separately from Creusot results. Never log in, push, publish, deploy, or publish evidence without explicit authorization.
