# Public API inventory and proposed coverage denominator

This inventory defines counting scope; it does not assert that any listed contract is proved. Read alongside SPEC.md and eventual per-instance theorem mappings. Version 4.1.0 implements both scalar traits for exactly ten built-ins: u8, u16, u32, u64, usize, i8, i16, i32, i64, isize. There is no built-in u128/i128 implementation. Pointer-sized instances have target-specific widths and must not be counted as arbitrary-width proofs.

## Finite builtin scalar surface: 90 callable instances

| Public family | Builtin instances | Strong desired contract |
|---|---:|---|
| FixedInt::encode_fixed | 10 | Exact LE bytes on exact length; None and unchanged buffer otherwise |
| FixedInt::encode_fixed_light | 10 | Exact LE array |
| FixedInt::decode_fixed | 10 | Exact signed/unsigned LE value on exact length; None otherwise |
| FixedInt::encode_fixed_vec | 10 | Exact LE vector, subject to allocation model |
| FixedInt::switch_endianness | 10 | Exact byte reversal, signed reinterpretation |
| VarInt::required_space | 10 | Minimal positive base-128 length of unsigned/ZigZag value |
| VarInt::decode_var | 10 | Permissive first-prefix decoding, count, overflow/truncation classification |
| VarInt::encode_var | 10 | Canonical bytes, exact count, unchanged suffix under capacity bound |
| VarInt::encode_var_vec | 10 | Exact canonical vector, subject to allocation model |
| **Total** | **90** | **9 families × 10 built-in types** |

FixedInt::ENCODED_SIZE and associated Bytes are public associated items, not callable methods. Record their ten value/layout obligations separately; do not inflate the callable denominator. Default Vec methods count once per built-in instance, even though their source bodies are shared. Internal helpers (ZigZag, required-space helper, VarIntMaxSize, VarIntProcessor) are separately tracked dependencies and add no public-instance credit by themselves. MSB and VarIntProcessor are not accessible through the crate's public exports because their containing modules are private.

## I/O and generic surfaces: separate from the finite denominator

Four synchronous families are public: VarIntReader::read_varint, FixedIntReader::read_fixedint, VarIntWriter::write_varint, FixedIntWriter::write_fixedint. They are blanket implementations for arbitrary lawful Read/Write receivers and accept custom integer-trait types. A selected builtin-by-family matrix has 40 integer instantiations, but each still quantifies over or models receiver behavior; it is not a complete enumeration of the truly generic API.

Four async families add read_varint_async, read_fixedint_async, write_varint_async, write_fixedint_async under either tokio_async or futures_async. Runtime models, feature combinations, cancellation and generic receiver assumptions must be explicit. Do not silently add 40 async instances to a default-feature claim or treat two runtimes as one verified implementation environment.

Suggested reporting is therefore:

- Builtin scalar callable coverage: N/90, with per-instance mappings and strength (full/error/success-only).
- Synchronous I/O: covered families and builtin integer domains plus precise Read/Write model, consumption, partial-effect and error guarantees.
- Async I/O: runtime/feature-specific coverage, separately.
- Generic/custom scalar traits: explicit assumptions and limitations; no universal claim inferred from builtin coverage.
- Internal helper theorems, associated-item/layout checks and native tests: separate evidence, never extra public-instance numerator credit.

A combined 130 denominator (90 core + 40 selected synchronous builtin instantiations) is permissible only if explicitly named that restricted matrix. It must not be described as the whole public API. Prefer the 90 core denominator with separate I/O reporting to avoid giving a finite count to an open generic surface.

## Recommended proof order and strength

1. Independent ZigZag arithmetic correspondence including extrema and inverse; exact required_space minimality. These support but do not replace public method proofs.
2. Fixed-width array encode/decode and byte reversal across all ten built-ins; slice wrappers with exact-length success/failure and unchanged failure buffers; Vec wrapper only with an explicit allocation boundary.
3. Actual u64 encode/decode loops connected to mathematical base-128 digits/weighted sums, then actual i64 and narrow checked-conversion wrappers. Keep canonical encoding and permissive decoding distinct.
4. Vec wrappers and suffix/consumed-count composition, then I/O if actual extraction and explicit stateful standard-library models permit.

Success-only decoder theorems on canonical encodings are useful but weaker than the total arbitrary-slice classification in SPEC.md. A roundtrip theorem alone provides neither canonical representation nor malformed-input behavior. Report these differences, rather than counting every theorem as equal semantic coverage.

## Contract discrepancies relevant to coverage

- FixedInt overview says machine-endian, whereas explicit method contracts and code are LE.
- Fixed encode rejects oversized destinations too; exact-length requirement is not explicit in its prose.
- VarIntReader prose promises truncation and generally whole-varint consumption; actual checked-range errors and target byte limits violate those expectations.
- Slice decoding allows zero padding through ten bytes even on small targets; readers enforce a smaller width-specific limit and can consume one extra byte before InvalidData.
- A lawful custom FixedInt larger than eight bytes is not covered by the blanket I/O adapters' internal buffers; arbitrary generic totality is false without further restrictions. Custom decode consistency and custom VarInt maximum length likewise require assumptions.

These source observations require independent native reproductions for issue evidence; none is an excuse to modify the upstream implementation during verification.
