# crc 3.4.0 verification

- Follow the repository Aeneas skill. Do not modify upstream or generated models.
- Separate specification design, actual-body proof implementation and independent review of provenance, contracts, evidence and coverage.
- Keep callable API coverage distinct from parameter/lane instances, source extraction, native observations and full mathematical CRC correctness.
- Valid algorithm parameters are explicit preconditions, including 1 <= width <= word width and bounded polynomial/init/xorout where the contract needs them. Publicly constructible invalid Algorithm values are not silently assumed valid.
- Keep failed extraction attempts in ignored work/runs and summarize real blockers honestly. Never substitute wrappers or surrogate Rust implementations for actual crate bodies.
- Only propext, Classical.choice and Quot.sound may occur transitively in maintained theorem roots. No sorry/admit/native_decide/custom axioms.
- Use pinned existing tool tuple and dependency caches. Do not clean shared Lake packages or earlier retained evidence.

- Normal verification must use current locked release sources, current configurations,
  specifications, proof packages and regression inputs. Never require an archived
  successful log, old Git object, migration input map or historical specification.
- Keep fresh native observations, independent oracle results, extraction equality,
  standard Lake/theorem/axiom audit and before/after fingerprints distinct. Removing
  historical comparisons does not relax any of these checks. Archive descriptors
  preserve provenance only; no normal setup/verify command reads an evidence archive.
