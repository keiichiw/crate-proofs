# Independent native observations — integer-encoding 4.1.0

These are finite observations against the unchanged published implementation,
not formal proofs and not upstream reports. The tested source is Git
`e0a10d01e86a38d0df177676c62f9a10c845ab53`, whose release archive and mutually
present source bytes were checked by root. No library source, unsafe surrogate
or generated Lean was used in these tests.

## Reproduction and scope

Run `bash integer-encoding/4.1.0/scripts/native-check.sh` from repository root.
Set `INTEGER_NATIVE_LOG_DIR` to a fresh evidence directory to retain logs there.
The runner compiles actual `upstream/src/lib.rs` with pinned Rust 1.91.1, default
features and no active external dependencies. Its Cargo metadata/lock hashes
are retained. Direct rustc avoids compiling unused Cargo dev dependencies; it
is not a substituted Rust library. The native harness itself is forbidden from
using unsafe code.

Debug uses overflow-checks=yes/debug-assertions=yes/opt-level=0. Release uses
no/no/3. Both modes pass 15 harness tests. The unmodified upstream default test
suite passes 31 tests, and the original rustdoc example passes 1 test. Test
`--list` output, compilation logs, observations and SHA-256s are retained by
`native-results.json`. The executable `tests/reproduce.rs` independently
reproduces the three grouped observations below in both build modes.

All ten builtin scalar types exercise 90 core callable instances (five FixedInt
and four VarInt methods per type) and forty synchronous I/O builtin
instantiations. ENCODED_SIZE constants are checked but do not increase callable
coverage. The independent oracle uses base-128 division/remainder, arithmetic
signed ZigZag and positional base-256; it does not reuse library loops, tables,
endian conversion or ZigZag helpers. Cases include every bit boundary, scalar
extrema, all byte values, 2048 deterministic random words per type, and 4096
arbitrary byte slices per type. Exact encoded bytes, consumed lengths, trailing
input, mutable suffixes, required space, non-shortest encodings, range failures,
truncation and partial/erroring I/O are checked separately from roundtrips.

Optional asynchronous backends and simultaneous optional-feature configuration
are excluded from this default native result. Native coverage is distinct from
Lean theorem coverage and is not whole-crate verification.

## IE-S1: stream width cap can leave a complete varint partially consumed

`VarIntReader` documents: “this always reads a whole varint” and describes
truncation when the numeric value exceeds the target type. With a stream

    80 80 80 80 01 2a

(the complete canonical u64 varint for 2^28, followed by the separate value42),
`read_varint::<u8>()` returns InvalidData after consuming only the first three
bytes. A subsequent u8 read decodes the leftover `80 01` as128; only the next
read reaches42. This contradicts the documented whole-varint consumption on
out-of-range values and loses logical framing if a caller resumes after error.

The cause is the target-type maximum in `VarIntProcessor::new`/`push`, checked
only after `read_varint` reads one more byte (reader.rs42–57,94–109). For u8,
maxsize is2, so byte3 is consumed before rejection. The reader cap also rejects
three-byte padded zero although `u8::decode_var` accepts it; this is a related
acceptance-policy inconsistency, not an additional root cause. A u64 stream of
ten continuation bytes reads an eleventh byte before rejecting. That last
observation concerns malformed framing and does not by itself prove the
eleventh byte was a distinct valid value.

This is one grouped consumption/capacity issue, affecting synchronous and
source-equivalent asynchronous reader logic. Only synchronous executions were
performed here; async effects are a source observation.

## IE-S2: complete numeric overflow is reported as UnexpectedEof

For the stream `ac 02 2a` (300 followed by42), `read_varint::<u8>()` reads the
complete two-byte first varint and returns UnexpectedEof, despite42 remaining
unread. Source conversion deliberately checks numeric range; the reader then
maps every decode None to UnexpectedEof (reader.rs112–114), conflating numeric
range rejection with actual EOF.

This disagrees with the “value is truncated” documentation and gives an EOF
error for a complete out-of-range input. The interface does not explicitly
mandate one particular alternative error kind. Classify this as an error/
documentation discrepancy rather than a wrong integer result. Its root cause
(range rejection followed by unconditional EOF mapping) is distinct from IE-S1;
this two-byte example is within the target's stream byte cap.

## IE-G1: public generic FixedInt I/O has an undocumented eight-byte limit

A safe, correct `Fixed128(u128)` implements the public FixedInt trait with
sixteen-byte little-endian representation. Its own encode/decode methods work.
Both `read_fixedint::<Fixed128>()` and `write_fixedint(Fixed128(1))` panic before
performing any I/O, because the adapters slice an eight-byte stack buffer at
`size_of::<FI>()` (reader.rs143–147, writer.rs69–75).

The public trait and generic method signatures contain no size<=8 restriction.
This is a generic-adapter panic/capacity limitation, not a failure of the ten
builtin implementations, all of which have size<=8 on the tested host. The
asynchronous adapters have the same source pattern; they were not executed in
this native run. It is one cause shared by read and write, not two bugs.

The reproduction uses a full fixed-width integer representation and valid
trait results; it does not depend on an implementation lying about its size or
returning None for a correctly sized byte string.

## Documentation precision and expected preconditions

- FixedInt encode_fixed/decode_fixed require exact slice length. For u32, a
  five-byte slice returns None; encode leaves every byte unchanged. The docs
  describe insufficient-space failure without stating the exact-length rule.
  Their wording is ambiguous rather than an unequivocal promise that every
  larger destination succeeds. Keep this documentation omission separate from
  confirmed framing/panic observations.
- FixedInt's overview says machine endianness, while the detailed methods and
  switch_endianness description say always little-endian. The tested builtin
  methods emit/receive little-endian, including signed two's-complement bytes.
- Too-small encode_var destinations panic in both modes. This violates its
  explicit required_space precondition and is not counted as a library defect.
- Varint read propagates Interrupted; fixed read_exact and both write_all paths
  retry it through their standard-library defaults. No stronger retry guarantee
  is documented for read_varint, so this difference is not counted as a defect.
- Partial reads/writes, EOF, PermissionDenied and WriteZero observations retain
  exact processed prefixes. They pass the stated default I/O behavior tests.

No external issue, pull request, source fix, push or publication was performed.
