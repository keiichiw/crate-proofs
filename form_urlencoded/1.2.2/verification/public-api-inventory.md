# Public API and trait coverage inventory

This inventory defines the selected first-order proof scope and public items Creusot cannot translate. Run status, completed integrated evidence, and current-input freshness are maintained in [results.md](results.md). Standard-library assumptions are listed in [assumptions.md](assumptions.md). Selection here is not a claim that edited inputs have been freshly proved.

| Public item | Required behavior | Current scope/status |
|---|---|---|
| `parse(input)` | Begin with exactly `input` as remaining raw state. | Selected; constructor and refinement goals are in the generated inventory. |
| `Parse` state, `clone`, `into_owned` | Preserve the exact remaining suffix. | Selected, with state contracts and explicit clone body. `Copy` remains compiler-derived. |
| `Parse::next` | Skip empty `&` fields, split each pair at the first `=`, map `+`, decode valid `%HH`, preserve malformed escape behavior, apply lossy UTF-8, return the exact name/value Cow variants, and advance to the exact consumed suffix. | Selected body, trait refinement, iterator laws, scalar trace, and separate Cow borrowed/owned trace. Shared runtime body across native and Creusot. |
| `ParseIntoOwned::next` | Same scalar values and suffix progression, returning owned strings. | Selected body, refinement, and iterator laws. The explicit Cow match uses concrete `str::to_owned` behavior. |
| `byte_serialize(input)` and `ByteSerialize` state | Begin with exactly the supplied bytes and expose the current remaining suffix. | Selected constructor and state model. |
| `ByteSerialize::next` | Emit maximal unchanged ASCII runs, `+` for space, uppercase `%HH` for other bytes, and consume exactly the represented bytes. | Selected exact chunk sequence, body, and trait refinement. Runtime body is shared. |
| `ByteSerialize::size_hint` | Return `(0, Some(0))` when empty and `(1, Some(remaining_bytes))` otherwise. | Selected helper, trait body, and refinement. |
| Iterator laws and inherited defaults | Concrete `IteratorSpec` supports empty/concatenated production, and standard defaults operate over that iterator behavior. | `produces_refl`/`produces_trans` and refinements for the three concrete iterators are selected. Standard-library default/adaptor bodies are not separately verified; their behavior is conditional on the checked concrete iterator contract and reviewed library boundary. `rev`, `rfold`, and `rfind` are unavailable because the types do not implement `DoubleEndedIterator`. |
| `Target for String` and `Target for &mut String` | Mutable access and finish preserve the relevant contents/borrow relation. | Concrete implementation bodies and refinements are selected; run status is recorded in results.md. This does not establish arbitrary caller-defined `Target` laws. |
| `Serializer::new`, `for_suffix`, `clear`, `append_pair`, `append_key_only`, `extend_pairs`, `extend_keys_only`, `finish`, and `encoding_override` | State, suffix/prefix mutation, separator rules, callback call order and returned bytes, panic behavior, and single finish. | Outside current proof scope. Creusot 0.13 rejects the exact public `dyn Fn(&str) -> Cow<[u8]>` callback type as `forbidden dyn type`; no erased or substitute callback is used. This leaves the serializer methods and callback-dependent behavior unverified. In particular, `for_suffix("é", 1)` succeeds because the position is within the byte length, while `clear` then panics on the non-character-boundary truncation. |
| `ByteSerialize: Debug` | Derived formatting of the remaining-byte field. | Explicitly excluded generated target; no custom Debug-formatting guarantee. |
| Auto traits and blanket `IntoIterator` | Compiler-derived type properties and standard iterator conversion. | Accounted for at the Rust type-system / standard-library boundary; not individual function-body proof goals. |

The selected machine-readable target list is `target-inventory.json`. Its selected names classify generated proof targets; the one `ByteSerialize` Debug target is excluded. It does not imply that untranslatable serializer methods are covered. The isolated dynamic-callback probe and error are under `probes/encoding-override/`.

## Claim rule

A public method counts as formally covered only when its body and relevant trait refinement have positive, fresh, closed goals for the current source fingerprint. A helper result does not replace the caller's proof, and a method body does not replace its trait refinement. The archived integrated result and any subsequent current-input run must be distinguished in results.md. Native differential tests are finite observations, not an all-input proof.
