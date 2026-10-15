# Creusot 0.13 string / formatter diagnostics

Pinned compiler: nightly-2026-06-22, commit
`91fe22da8084a1c9e993d78d4a56f22ab8396236`. These are failed translation
experiments, not successful proof evidence. The final implementation uses the
same executable scalar-byte code in native and Creusot configurations.

- A ghost postcondition containing `"string contains no or an invalid date"@`
  caused `Unsupported literal` at `translation/pearlite/from_thir.rs:330`.
  [Saved compiler backtrace](ghost-string-literal-ice.txt).
- A runtime `*b"string contains no or an invalid date"` reached
  `Literal::Bytes => todo!()` at `backend/term.rs:578`.
  [Saved compiler backtrace](runtime-byte-string-ice.txt).
- A runtime string literal is translated as a Why3 `string`, but its
  `str` view has no content axiom in the reviewed configuration. A successful
  formatter call with that literal alone therefore did not prove exact message
  characters. The final Error implementation builds explicit scalar bytes,
  uses the reviewed ASCII UTF-8 boundary, and specifies the exact byte positions.
- `&array[..]` reached an external RangeFull indexing operation without a
  contract, creating an impossible precondition. Passing `&array` directly
  performs the supported slice coercion and preserves the content relation.

The legacy grammar predicates are intentionally opaque outside their child
modules. Initial kernel completeness attempts left obligations containing
uninterpreted `asctime_encoding` / `rfc850_encoding` predicates. Checked
`encoding_laws` expose only length bounds and record uniqueness; raw parser
error contracts also rule out every encoding witness. This closed the kernel
without exposing all grammar internals or trusting an application lemma.

The forward `From<SystemTime>` implementation needs the supported timestamp
precondition. Its generated trait refinement asks an unconditional standard
`From` precondition to imply that range. Native pre-epoch and year-10000 inputs
are counterexamples. The bounded implementation body and its callers are
proved; the refinement remains explicitly open in the manifest and is never
counted as a successful goal. No fake SystemTime invariant or application-level
trusted declaration was added.
