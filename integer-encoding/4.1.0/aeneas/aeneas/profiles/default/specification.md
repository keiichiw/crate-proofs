# Independent encoding specification — integer-encoding 4.1.0

This is the intended mathematical contract, not a report of completed proofs. Source-specific acceptance and effects are identified separately. Round-trip identities are consequences, not substitutes for exact encoding and decoding correctness.

## Sources actually consulted

- [Protocol Buffers encoding guide](https://protobuf.dev/programming-guides/encoding/), particularly Base 128 Varints, Signed Integers and the condensed reference: authoritative independent definitions of low-group-first base-128 encoding, ZigZag, and little-endian fixed integers.
- [4.1.0 VarInt documentation](https://docs.rs/integer-encoding/4.1.0/integer_encoding/trait.VarInt.html): crate buffer, consumption and signed-encoding promises.
- [4.1.0 FixedInt documentation](https://docs.rs/integer-encoding/4.1.0/integer_encoding/trait.FixedInt.html): explicit little-endian methods and byte reversal; contradictory overview noted below.
- [4.1.0 crate documentation](https://docs.rs/integer-encoding/4.1.0/integer_encoding/): public exports.
- Release source from [the registry archive](https://static.crates.io/crates/integer-encoding/integer-encoding-4.1.0.crate), inspected after the independent core specification to determine crate-specific permissiveness, failures and I/O effects. Registry version selected from [the sparse index](https://index.crates.io/in/te/integer-encoding).

The external encoding standard does not, by itself, determine this library's malformed-input policy. Neither protobuf signed `intN` nor signed LEB128 is the signed contract here: this crate uses ZigZag followed by unsigned varint.

## Domain and fixed-width representation

For a built-in scalar of width w bits, w is 8, 16, 32 or 64; usize/isize use the compilation target's pointer width. Let m=w/8. Unsigned values are in [0,2^w); signed values are in [-2^(w-1),2^(w-1)). Define U(z)=z mod 2^w, using the nonnegative residue.

The exact little-endian representation is the list of m bytes

    fixed_w(z)[i] = floor(U(z)/256^i) mod 256,  0 <= i < m.

Given exactly m bytes, let u=sum_i bytes[i]*256^i. Unsigned decoding returns u. Signed decoding returns u if u<2^(w-1), otherwise u-2^w. This definition is independent of host byte order.

- `encode_fixed_light` and `encode_fixed_vec` return exactly fixed_w(z).
- `encode_fixed` succeeds with Some(()) exactly when destination length equals m, replacing it with fixed_w(z). For every other length it returns None and leaves the complete destination unchanged.
- `decode_fixed` returns the above value exactly when input length equals m; otherwise None. It does not decode a prefix of an oversized slice.
- `switch_endianness` returns the scalar whose fixed representation is reverse(fixed_w(z)); equivalently unsigned residue sum_i fixed_w(z)[i]*256^(m-1-i), interpreted with the scalar's signedness.

## Canonical varint and ZigZag

For unsigned u in [0,2^64), let k be the least positive integer with u<128^k. Let d_i=floor(u/128^i) mod 128. Canonical bytes are

    var(u)[i] = d_i + (128 if i<k-1 else 0),  0 <= i < k.

In particular var(0)=[0], 1<=k<=10, and the tenth byte, if present, is 1. A multi-byte canonical encoding has nonzero last payload. For signed z define Z(z)=2z if z>=0, otherwise -2z-1. Its inverse is Q(u)=u/2 for even u, otherwise -(u+1)/2 (integer quotients). These formulas include both signed extrema.

For each built-in unsigned scalar, encode var(z); for each signed scalar, encode var(Z(z)). `required_space` equals that exact canonical list length. With destination length at least k, `encode_var` terminates successfully, returns k, writes precisely these first k bytes, and preserves every suffix byte. `encode_var_vec` returns exactly the canonical list. A short destination is outside that successful contract: source may panic, rather than return an error value.

## Permissive slice decoder

Define a valid unsigned prefix of input s by a length k satisfying:

1. 1<=k<=min(length(s),10).
2. s[i]>=128 for all i<k-1, and s[k-1]<128.
3. u=sum_(i<k) (s[i] mod128)*128^i is less than 2^64.

The continuation conditions make k unique. For k=10 the bound is equivalent to the last byte being 0 or 1. Return Some((u,k)) for unsigned target width w iff additionally u<2^w. For signed target width w return Some((Q(u),k)) iff Q(u) is within its signed range. Otherwise return None. Input and suffix remain untouched. An arbitrary suffix after a successful prefix is irrelevant, even if malformed.

This is intentionally more permissive than canonical encoding. High zero payload groups may pad any value up to ten bytes, even when the target is u8/i8. For example [128,0] and nine 128 bytes followed by 0 both decode to zero. Conversely empty input, no terminal byte in the available prefix, a tenth byte greater than 1, and target range overflow are rejected. An eleventh terminator cannot rescue an invalid first ten bytes. Range overflow is not numeric truncation.

Consequences to prove include decode(var(value) ++ suffix)=Some(value,length(var(value))) and normalization: re-encoding a successful decode returns the unique canonical encoding of its value. Re-encoding need not reproduce the original noncanonical prefix.

## Stream effects: separate contracts

For built-in width w let M=ceil(w/7), giving 2,3,5,10. This is the reader limit, distinct from the ten-byte slice acceptance bound. A model must expose consumed input and observable errors, not only the return value.

`read_varint` reads one byte at a time until a terminal byte, subject to M stored bytes. A terminated prefix of length<=M returns its slice-decoded value if valid; numeric range failure returns UnexpectedEof despite a terminator having been consumed. End of input before any terminator also returns UnexpectedEof. If M continuation bytes have been stored, the implementation attempts another read: a successful extra byte is consumed before push returns InvalidData; immediate EOF instead produces UnexpectedEof. Thus it may consume M+1 bytes on InvalidData. Underlying read errors propagate and prior consumption is not rolled back. The implementation uses `read`, so it does not itself retry Interrupted errors.

A fixed reader for built-ins reads exactly m bytes using read_exact and decodes the fixed representation. Writers use write_all on exactly the canonical representation and return its byte length upon success. Underlying failures can occur after partial consumption/output; no transactional rollback is promised. Async counterparts require their runtime's read/write semantics, polling and cancellation model, and must not inherit a synchronous proof without justification.

These I/O statements are restricted to built-in scalar implementations and a lawful I/O model. The public traits permit custom implementations: fixed readers/writers allocate eight bytes and use size_of::<FI>(), not FI::ENCODED_SIZE. A valid custom FixedInt larger than eight bytes therefore panics at slicing; a custom decoder returning None can panic at unwrap. Varint I/O likewise uses a ten-byte buffer and a size_of-derived limit that need not describe a custom encoding. Generic trait-wide total success is not justified by the builtin contracts.

## Documentation discrepancies and limits

1. FixedInt's overview claims machine endianness, whereas its specific methods, switch_endianness documentation and source require little-endian. The independent contract follows the explicit LE methods.
2. encode_fixed says insufficient space returns None; the implementation rejects oversized buffers too. Record exact-length behavior instead of silently adopting an at-least-sized success precondition.
3. VarIntReader says an out-of-range value is truncated. Source delegates to checked decoding and reports UnexpectedEof instead. This is a documentation/behavior discrepancy, not a license to prove truncating semantics.
4. Slice padding acceptance and stream width limits differ. The stream reader does not always consume a whole overlong varint, despite the broad prose claim.
5. Custom trait implementations have undocumented buffer-size/consistency assumptions in I/O. Builtin proofs do not eliminate this limitation.

## Oracle and proof obligations

Use arbitrary-precision arithmetic digits, weighted sums and signed range comparisons for an independent oracle; avoid reproducing the source's shifts/OR loop. Cover every scalar's zero/extrema, every 7-bit length boundary, fixed signed bit patterns, arbitrary suffixes, exact/short/oversized fixed destinations, noncanonical zero padding, tenth-byte overflow, narrow-target overflow, truncated prefixes, and stream byte counts with sentinel suffixes. Native checks are evidence, not universal proofs.

Formal roots should state total success for all valid scalar values and buffers, exact bytes/value/count, preserved suffix or unchanged failure state, and complete malformed-input classification where proved. Actual generated source operations and explicit standard-library/representation models must remain visible. Separately label allocation, I/O, pointer-width and feature assumptions. Round-trip-only, finite catalogue or example tests do not discharge these contracts.
