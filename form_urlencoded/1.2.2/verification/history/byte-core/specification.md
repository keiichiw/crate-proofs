# Specification: form_urlencoded 1.2.2 selected byte core

This specification covers a proposed first verification milestone for release source. It does not claim that the whole parser or serializer is verified.

The selected function contracts cover five local helpers: unchanged-byte classification, exact percent-encoded triples for all `u8` values, raw pair bounds, first-plus search, and in-place plus replacement. The exhaustive encoder match uses literal numeric ASCII bytes; its postcondition specifies byte 0 as `%`, bytes 1 and 2 as uppercase hexadecimal for the high and low nibbles, and all three bytes below 128. It is called by the runtime `ByteSerialize::next` path. The iterator wrapper, unsafe UTF-8 conversion, and chunk progression are outside the formal proof surface.

The byte serializer's unescaped alphabet is exactly ASCII `*`, `-`, `.`, `0` through `9`, `A` through `Z`, `_`, and `a` through `z`. For one input byte, serialization emits `+` for space, emits the byte unchanged when it belongs to that alphabet, and otherwise emits `%` followed by the two uppercase hexadecimal digits for its high and low nibbles. The iterator may group consecutive unescaped bytes into a borrowed UTF-8 chunk; concatenation of its yielded chunks is the byte serialization.

Raw form pair scanning operates on bytes before percent decoding. It splits segments on `&`, skips empty segments, and splits each nonempty segment at the first `=`. A missing equals sign means an empty value. The scanner preserves byte slices and consumes through the delimiter when one exists. Empty input ends iteration; trailing and repeated ampersands contribute no pair.

Plus mapping preserves length and replaces every `+` byte by ASCII space; all other bytes are unchanged. If no plus exists, the release implementation returns a borrowed `Cow`; ownership shape is outside the first formal contract.

The public `parse` result applies percent decoding and lossy UTF-8 conversion after plus mapping. Correctness of those dependency/standard-library operations, malformed percent sequences, `Cow` ownership, allocation, and callback effects are outside this milestone. `Serializer` methods and their panic/state behavior are also outside this milestone.
