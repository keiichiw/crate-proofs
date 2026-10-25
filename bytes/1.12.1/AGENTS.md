# bytes 1.12.1 verification

- Use the repository's Aeneas + Lean verification skill and this target's managed setup/verify wrappers. The active profile is `aeneas/profiles/unpatched/`: use unpatched Aeneas, Charon, Lean and backend inputs there. The prior `aeneas/profiles/default/` profile is historical evidence for the earlier 56 claims; keep it read-only and do not treat it as current verification of the unpatched source.
- Preserve the checksum-confirmed release archive and complete source inventory. Source in `.work/source` is immutable; generated Lean is never hand-edited.
- Separate independent specification design, proof implementation and review.
  Keep specification decisions and proof status separate.
- Extend the maintained scope with feasible unchanged upstream bodies, following
  the user's request to cover what can be verified. The theorem inventory and
  latest accepted results define checked coverage. Keep prior proofs intact.
  Do not claim Buf behavior, complete adapter correctness, Bytes/BytesMut,
  unsafe memory safety or whole-crate verification without the corresponding proofs.
- Prove unchanged generated bodies and audit theorem dependencies. Preserve failure
  reproductions outside the maintained proof tree; never promote partial extraction.
- Do not push or publish without explicit user authorization.

For the historical default profile, retain the nine-model and core/numeric/stage3 tool-variant requirements, original repair negative controls, standard-source hashes and exact backend/prelude correspondences. The active unpatched profile has its own scoped model and tool requirements; do not carry over patched-profile coverage claims. Native tests remain separate from formal proofs. In historical replays, the ordinary pinned tool is the baseline defect control; the active profile uses that unpatched tool as its compiler.
