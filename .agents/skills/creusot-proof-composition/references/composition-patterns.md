# Examples of connecting model boundaries

These examples primarily come from Creusot 0.13 and the `percent-encoding 2.3.2` verification fork.
Reuse the method of separating and proving relations; do not automatically adopt that crate's
specification or standard-library assumptions. Check current results, scope, and exclusions in the
[result report](../../../../percent-encoding/2.3.2/verification/results.md),
[specification](../../../../percent-encoding/2.3.2/verification/specification.md), and
[assumptions ledger](../../../../percent-encoding/2.3.2/verification/assumptions.md).

## Carry equality across views

**Use when:** runtime equality provides a contract in a different model from the caller's equality claim.
Identify both types and their conversion instead of relying on an intuition that their contents match.

In this example, a slice's `deep_model()` uses an integer sequence, while the encoder's state contract
uses a byte sequence.
[`slice_byte_views_ext_eq_from_model`](../../../../percent-encoding/2.3.2/crate/src/equality_models.rs)
starts from integer-model equality and proves equal lengths, equal integer values at every in-range
byte index, then `ext_eq` of the byte views. The caller uses that checked contract.

When adapting this approach, check whether the element conversion distinguishes the original values.
Unlike the integer view of `u8` here, a lossy conversion cannot justify input equality from output equality.
**Completion:** both the bridge and the equality implementation/refinement consuming its postcondition close.

## Prove sequence boundaries in small steps

**Use when:** element processing passes, but an empty sequence or a rearranged suffix blocks proof.
Isolate the required equation and separate empty/nonempty cases, index positions, and both sides of the conversion.

[`decoder_lemmas.rs`](../../../../percent-encoding/2.3.2/crate/src/decoder_lemmas.rs) gives separate
contracts for byte-to-integer mapping over concatenation, nested suffixes, and adding a byte to a prefix.
The encoder's `produces_refl` aligns the element type of `map(empty)`, proves `ext_eq(empty)`, and
connects that result to the empty-concatenation law.
[`produces_append`](../../../../percent-encoding/2.3.2/crate/src/encoder_display.rs) supplies extensional
equality between `push_back` and concatenation with a singleton. Check the actual VC for the missing
empty or associativity law instead of scattering the same assertions across callers.

For strings, concatenating scalars and concatenating UTF-8 bytes are distinct relations.
[`string_bytes_lemmas.rs`](../../../../percent-encoding/2.3.2/crate/src/string_bytes_lemmas.rs) separates
the byte view of an empty prefix, index relations for nonempty concat/tail, and byte-to-integer conversion.
It proves `string_bytes_concat` recursively with decreasing prefix length.
[`append_string`](../../../../percent-encoding/2.3.2/crate/src/encoder_cow.rs) uses this to connect
`String::push_str`'s scalar contract to the caller's byte contract. Do not assume equal character and byte counts.

**Completion:** base-case, recursive/step, and caller-connection VCs all close. Also check that the
caller actually establishes every length and index precondition used by the lemma.

## Connect an iterator to its consumer

**Use when:** the `next` body passes, but repeated calls, collection, or the final result do not connect.
First define the state being modeled. In this example, clone/equality concern the current remaining
bytes after partial consumption and the encoder's configured set, rather than initial input or final output.

The [`IteratorSpec` implementations](../../../../percent-encoding/2.3.2/crate/src/lib.rs) connect
initial and remaining state through this conceptual relation:

```text
trace(initial) = model(visited).concat(trace(current))
```

`completed`, `produces_refl`, `produces_trans`, and the `next` refinement are separate targets.
Prove empty and map/concat laws, then connect the terminal state condition. For `size_hint`, distinguish
input bytes, output bytes, and output chunks. Derive bounds from the target algorithm instead of
copying another iterator's formula.

The loop in [`encoder_cow::into_cow`](../../../../percent-encoding/2.3.2/crate/src/encoder_cow.rs)
maintains three relations:

- The initial iterator produced `visited` and reached the current iterator.
- The configured set is preserved.
- The output String's UTF-8 bytes equal the flattened chunk bytes of `visited`.

Include already retrieved chunks at initialization, use before/after snapshots for each step, and
connect termination to an empty remaining trace. The iterator's production relation alone does not
prove the consumer's accumulated value.
**Completion:** selected bodies, laws/refinements, consumers, and bounds helpers close. Unselected
standard default methods such as `fold` and `collect` are outside that result.

## Separate Cow and UTF-8 guarantees

**Use when:** the byte decoder and String/Cow contracts use different models.
Check contents, borrowed/owned conditions, validity, error observers, and storage identity separately.

Choose the concrete-type boundary first. Callers can implement `ToOwned` for `Cow<T>`, so a blanket
model that every `Cow::into_owned` preserves contents would assume an unmodeled law. Use the checked
or authorized contract for the actual concrete type, such as `str`. See the
[form model design](../../../../form_urlencoded/1.2.2/verification/stdlib-model-design.md) for the reasoning and limits.

[`utf8_models.rs`](../../../../percent-encoding/2.3.2/crate/src/utf8_models.rs) connects strict conversion's
successful contents and validity, and failure observers `valid_up_to` / `error_len`, at the standard-library
boundary. A checked definition of a local recognizer is distinct from proof of its correspondence with
the standard validator. That correspondence depends on the external assumptions in the
[ledger](../../../../percent-encoding/2.3.2/verification/assumptions.md). Do not infer equivalence between
independently written UTF-8 parsers.

Lossy conversion preserves an existing public postcondition through a relation. In the
[lossy-postcondition probe](../../../../percent-encoding/2.3.2/verification/probes/lossy-postcondition/README.md),
that relation referred to prophetic `FnExt::postcondition` and therefore needed a matching logic declaration.
In the owned branch, binding the actual conversion result and explicitly exposing its existing
postcondition and witness closed the remaining existential VCs. This instantiates existing facts;
it does not add an extern specification or axiom. Recheck translation and VCs before assuming the
same attributes or witnesses are needed with future tools or models.

**Completion:** contents and specified variant/error conditions reach the production caller in every
branch. A successful isolated probe or finite UTF-8 edge tests do not establish whole-API proof.
Cow variants and byte equality do not establish allocation, capacity, pointer identity, or OOM guarantees.

## Separate callback arguments from external effects

**Use when:** an external call's roots close, but its contract has no guarantee about output or side effects.
Read its postcondition. A VC establishing a legal call is distinct from a meaningful output contract.

In the [formatting probe](../../../../percent-encoding/2.3.2/verification/probes/formatting/README.md),
some Creusot 0.13 formatter declarations had no content postconditions, so closed roots did not
establish rendered contents. An unspecified numeric Display call instead produced an impossible
precondition. Inspect the actual declaration to determine which success/failure form applies.

To guarantee call structure, a checked wrapper can make the real call exactly once and record its
arguments and actual return value in a ghost trace.
[`format_trace.rs`](../../../../percent-encoding/2.3.2/crate/src/format_trace.rs) and
[`debug_trace.rs`](../../../../percent-encoding/2.3.2/crate/src/debug_trace.rs) use this approach for
ordered chunks/typed fields and status. Display records the first Err and then stops.
**Completion:** the wrapper and actual consumer close, preserving call order, count, and error propagation.
That trace does not model text accepted by the sink or its side effects. A successful request-trace
proof does not fulfill an original requirement to prove rendered contents.
