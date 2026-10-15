# Specification: form_urlencoded 1.2.2 public API

This document states intended observable behavior, not proof status. The selected first-order API and current exclusions are in `verification/public-api-inventory.md`. No behavior may be claimed verified solely because it is described here; run status and input freshness are recorded in [results.md](results.md).

## Constructors and iterator state

`parse(input)` starts a parser at exactly the supplied raw byte sequence. `byte_serialize(input)` starts a byte serializer at exactly the supplied sequence. Iterator state models the remaining suffix, not the original input after calls to `next`. `Parse::into_owned` preserves the current remaining parse suffix. `Parse::clone` preserves the exact current state. `ByteSerialize::size_hint` is exactly `(0, Some(0))` for empty remaining input and `(1, Some(remaining_bytes))` otherwise; the current checked helper computes this pair.

## Parsing

Raw form pair scanning splits on `&`, skips empty segments, and splits each nonempty segment at its first `=`. A missing equals sign yields an empty value. The public parser then maps `+` to space, decodes valid `%HH` escapes, retains upstream malformed-escape behavior, and applies lossy UTF-8 conversion. The result contains the decoded name and value and advances the parser to the exact suffix consumed through the next delimiter. `ParseIntoOwned` has the same pair and progression behavior, with owned strings.

## Byte serialization

The unchanged alphabet is ASCII `*`, `-`, `.`, digits, uppercase/lowercase letters, and `_`. Space encodes as `+`. Every other byte encodes as `%` plus two uppercase hexadecimal digits. `ByteSerialize::next` groups each maximal run of unchanged bytes into one borrowed UTF-8 chunk, or emits one special-encoding chunk, and advances over exactly those bytes. Chunk concatenation is the encoded byte serialization.

## Serializer

`Serializer::new` records start position zero; `for_suffix` records the requested start when it does not exceed the target length and panics otherwise. Existing prefix bytes are preserved. `clear` truncates the target to the recorded start. Appending a pair or key emits `&` iff content since start is nonempty, applies the selected encoding override, and adds `=` only for a pair. Extend methods preserve iterator order and repeat the corresponding append operation. `finish` returns the target exactly once; operations after finish and repeated finish panic as documented.

`Target` behavior is conditional on its explicit law. The built-in implementations for `String` and `&mut String` are part of the selected proof scope. The `Serializer` API takes a caller-supplied encoding override. Its returned bytes, call order, and panic/effect behavior are part of the behavior, but serializer methods are outside the current proof scope because Creusot 0.13 rejects the exact public dynamic callback type. No callback behavior or arbitrary caller-defined `Target` behavior is assumed.

## Standard-library boundary

Standard-library correctness may be assumed only through reviewed, explicit models recorded in `verification/assumptions.md` and `crate/src/stdlib_models.rs`. The UTF-8 lossy-conversion model matches maximal valid UTF-8 decoding and U+FFFD replacement semantics, with `Cow` borrowed/owned conditions. Percent decoding is local application logic. The selected contracts cover content and observable Cow variants; they do not claim pointer identity, allocation identity, OOM behavior, or serializer callback behavior. Other boundaries and exclusions are listed in the public API inventory.
