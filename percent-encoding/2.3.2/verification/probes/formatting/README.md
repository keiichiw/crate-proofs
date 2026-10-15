# Formatting boundary probe

This isolated probe checks Creusot 0.13 support for common formatting paths. It
does not model or claim output bytes or generic writer behavior.

## Findings

- `Formatter::write_str` translates in a loop containing only the static ASCII
  literal `"x"`. Creusot emits `vc_write_str` and loop/result obligations, and
  `why3find` reports the obligations closed. This is only a body translation
  result. The installed `creusot-std` declaration in
  `creusot-std/src/std/fmt.rs` gives `write_str` no precondition or
  postcondition, so nothing connects a call to accepted text, sink effects, or
  an error status. A generic `Formatter` may wrap an arbitrary `fmt::Write`
  implementation, so a successful call alone does not mean text was rendered.
- Calling `<u8 as Display>::fmt` produces a concrete warning that the external
  function has no contract and therefore yields an impossible precondition;
  the corresponding `vc_numeric_format` is unproved.
- `write!(formatter, "{}", value)` translates to an unconstrained `false`
  condition in Coma and leaves `vc_numeric_format` unproved. This is a concrete
  unsupported path for formatting arguments and dynamic dispatch in this
  minimal probe, rather than a general claim that all format macros ICE.
- Calling derived `Debug::fmt` on a struct with one `u8` field translates and
  its generated body/builder-method obligations are reported closed. The
  standard model's `debug_tuple_field1_finish` is also contractless, so these
  results do not establish the rendered Debug text or sink effects.

The positive roots for `literal_loop`, `derived_debug`, and the generated
`impl_Debug_for_DebugPayload/fmt` were independently exported to Why3 and
checked with Z3 by the local diagnostic runner: 10 roots, all closed. This
confirms only the generated obligations under the installed abstract model;
the missing formatter postconditions remain the semantic limit above. The
report and per-root solver inputs/logs are in `direct-checks/`.

## Checked request-trace adapter

The isolated crate imports the actual production module at
`crate/src/format_trace.rs`. Its `request_write` helper calls the inherent
`Formatter::write_str` exactly once, then appends the original `&str` request
and observed `Ok`/`Err` status to a caller-supplied Ghost sequence, and returns
that same `fmt::Result`. The two-chunk loop uses successful-prefix and
failing-prefix invariants. It stops on the first `Err`, includes the failing
chunk and status in the trace, and returns that same error. The helper and loop
are checked application code. They introduce no trusted contract and make no
claim that the underlying writer rendered or retained the requested bytes.

Native `cargo check` of the isolated crate compiles the same production module
with the Ghost argument and updates erased. `cargo creusot request_write
pair_trace --no-cache` reports two files proved. The generated targets have 11
positive roots total; a separate direct Why3/Z3 run closes all 11, recorded in
`direct-checks-bounded-model/diagnostic-report.json`.
This confirms feasibility of checked request tracing and Err propagation. The
probe uses two supplied chunks and does not verify the crate's actual Display
impl or its PercentEncode iterator; those bodies are still outside this probe.

The Rust source and `verif/` outputs are the minimized reproduction. The
`why3find.json` file comes from `cargo creusot init` and is probe-local.

### Byte-model request traces (fresh run)

`crate/src/format_trace.rs` also exposes checked successful/failed prefix
predicates over expected `Seq<Seq<Int>>` chunks. Each trace entry's string is
related to the corresponding expected byte sequence with
`form_model::string_chunk_bytes`; status bits preserve successful calls and,
for the failing case, the first failed call. The updated `encoded_pair_trace`
uses two supplied chunks with their byte models and proves these invariants
around the checked `request_write` wrapper. This establishes requested call
order and error propagation only; no underlying sink contents are modeled.

Fresh Coma was generated with Creusot 0.13 at
`diagnostics/encoded-trace-run03/verif`. Explicit direct Why3/Z3 checking of
`format_trace/request_write` and `encoded_pair_trace` closed all 11 positive
roots. The report and solver inputs are in
`direct-checks-encoded-trace-run04/diagnostic-report.json`. Earlier run02 had
one timeout because its probe precondition expanded the full encoder chunk
model; run03 removes that unrelated expansion and closes all trace roots.
