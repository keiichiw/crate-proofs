# Proof patterns from the adler2 verification

These are reusable proof techniques, not assumptions about the next crate.

- Specify an independent scalar/list model, then connect actual generated functions
  to it. A theorem about the specification alone does not prove Rust behavior.
- Audit raw public states. Codec constructors may admit non-normalized states; empty
  operations can normalize them rather than preserve them. Prove both codec roundtrips
  before deriving resumption through serialization.
- State concatenation with actual representable `xs`, `ys`, `whole` slices and
  `whole.val = xs.val ++ ys.val`. Require both computations to succeed with the same
  final state, rather than an equality that can hold because both fail.
- Current pinned Aeneas uses `Result` with failure/divergence and total `WP.spec`.
  `Result.cases`, `WP.spec_ok`, `WP.spec_vis`, and `WP.spec_div` can bridge total WP
  to `∃ out, m = .ok out ∧ post out`. Do not substitute partial `dspec` for termination.
  Check these interfaces in the selected version rather than assuming stability.
- Prove generated loops by decreasing remaining input length, via `loop.spec_decr_nat`
  or list induction and the generated loop equation. Include exact content relations
  in invariants, not only bounds. For nested loops, reset machine bounds per chunk
  while preserving a mathematical relation across an unbounded number of chunks.
- Separate machine-operation safety from mathematical correspondence. Exact lane
  add/mul/rem lemmas can have private bounds; the public proof must discharge them.
  Doubled polynomial inequalities can avoid division in natural-number overflow bounds.
- For SIMD-style modular computations, a cross-added congruence can avoid truncated
  natural subtraction. Keep exact final canonical residues and prove casts preserve
  values; congruence alone is not equality of returned checksums.
- Inspect the pinned standard-library implementation before adding a model bridge.
  In adler2, chunks_exact already had a concrete partition representation. Checked
  length/partition/iterator lemmas were enough; no new trusted iterator assumption
  was needed. Such lemmas still inherit the Rust/library-model trust boundary.
- Transparent fragments of generated `do` blocks may simplify proofs, provided a
  checked decomposition equality reconnects them to the unchanged original body.
  Use bind associativity/unfolding, not a manually substituted application model.
- `step`, scalar arithmetic, `omega`, and explicit BitVec/Nat lemmas were useful.
  `bv_tac` introduced a native axiom in this toolchain; replacing it with kernel-checked
  bit arithmetic kept the audit policy unchanged. Always audit transitive dependencies,
  even when source text contains neither sorry nor axioms.

For concrete implementations, inspect `adler2/2.0.1/proofs/Proofs/Compute.lean`,
`OuterLoop.lean`, `LaneLoop.lean`, `FinalCombine.lean` and `PublicUpdate.lean`.
Do not import these as generic lemmas for a different generated crate or copy their
numeric bounds without a new derivation. Inspect results.md for accepted evidence.
