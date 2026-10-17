# Isolated heapless serialization correction candidate

This is a local verification candidate for ipnet 2.12.2, not a change to the
pinned upstream submodule or the accepted 625-theorem proof package. `src/`
was copied byte-for-byte from the upstream checkout at Git commit
`13c5c5873c02127679b1e8e64b538e4e36942640`, then only four cfg guards in
`src/ipnet_serde.rs` were changed from `ser_as_str` to
`any(feature = "heapless", feature = "ser_as_str")` (and their complementary
negative guards). `cfg.patch` is the exact source diff. `provenance.json` records
SHA-256 hashes of every original and candidate source file. The independent
Cargo manifest preserves the parent manifest except `lib.path = "src/lib.rs"`;
Cargo.lock is byte-identical to the parent lockfile.

The candidate builds offline with the pinned native compiler:

```sh
cargo +1.91.1 check --offline --locked --manifest-path Cargo.toml --features heapless
```

The pinned Charon extraction of the actual IPv4 `Serialize::serialize` method
succeeds with selector
`{impl serde_core::ser::Serialize for crate::ipnet::Ipv4Net}::serialize`
and `--features heapless`. The pinned Aeneas backend then stops at the actual
`fmt::write(&mut buf, format_args!("{self}"))` call: it cannot translate the
`&mut heapless::String<18>` to `&mut dyn core::fmt::Write` unsizing cast
(`InterpExpressions.ml:945`; `src/ipnet_serde.rs:90`). Optimized MIR has the
same obstacle. The actual IPv4 `Display::fmt` method extracts separately,
but its baseline external formatter models carry no text state. The current
extraction is therefore diagnostic evidence, **not** a formal Serialize or
Display correctness proof. No generated output is accepted as a model.

The narrow IPv6 Serialize probe fails at the analogous mutable-dyn cast.
The tagged IpNet Serialize probe reaches both concrete methods and inherits
both failures. An optimized-MIR probe retains the cast. An optimized-MIR probe
that additionally includes the exact standard `core::fmt::write` body retains
the application cast and exposes an additional unsupported core formatter
translation at `fmt/mod.rs:1636`; including that standard body does not repair
the candidate's local body. Actual IPv4 Display extraction succeeds, with the
application call sequence (address argument, decimal-prefix argument, literal
slash, `Formatter.write_fmt`) visible, while its external address Display is
opaque and the existing formatter model does not retain text.

Fresh probe commands/logs and their hashes are packaged in
`evidence/latest/result.json` by `verify.py`. The older optimized-MIR,
standard-formatter-include, and Display probe output is preserved only in
ignored local `runs/`; it is historical research, not commit-ready execution
evidence. `check-source.py` checks upstream identity, source
bytes, the exact four-guard edit, manifest path adaptation and lockfile equality.
Independent `proofs/CapacityMath.lean` proves conditional18/43-byte capacity,
bounded-write and serializer error propagation under explicit external text and
buffer/serializer laws. It does not bridge the blocked local Serialize body.
Native feature-matrix evidence is separate from either formal result. See
[results](results.md) for the completed feature matrix and formal-scope limits.
Run `source ../../scripts/env.sh && python3 verify.py` from this directory to
repeat the pinned source checks, 22-theorem Lean check and axiom audit, ten
native feature combinations, candidate tests, and three expected Serialize
extraction failures. The 22 conditional Lean helper theorems and their
transitive axiom audit are listed in `proofs/audit.json`; each depends only on Lean
`propext`, `Classical.choice`, and `Quot.sound` where applicable.
