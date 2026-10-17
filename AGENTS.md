# Repository-wide guidance

- This repository hosts multiple Rust crate versions. Keep crate-specific source, Cargo files, verification scripts, specifications, evidence, instructions, and skills under `<crate>/<version>/`.
- Give each version an independent Cargo workspace and lockfile. Do not add a root Cargo workspace or place crate-specific scope rules here.
- Use `.agents/skills/creusot-verification/SKILL.md` for Creusot and `.agents/skills/aeneas-lean-verification/SKILL.md` for Aeneas + Lean. Follow the target version's own `AGENTS.md`, environment and skill for its proof scope and commands; do not mix the two toolchain activations.
- When body proofs succeed but model boundaries, iterator laws/refinements, or consumers do not compose, use `.agents/skills/creusot-proof-composition/SKILL.md` to diagnose the missing relation and choose a checked bridge.
- Preserve the stated contracts and report native tests separately from formal proof. Do not claim excluded APIs or unselected code are verified.
- Routine implementation and investigation can proceed with Luna. Consult Astra when blocked on proof behavior or specification design. The primary reviews contracts, commands, evidence, and coverage claims.
- Do not log in, push, publish, deploy, or publish evidence without explicit authorization.
