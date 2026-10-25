# Transparent standard-library source identity

These source files are copied byte-for-byte from rust-src of the pinned
nightly-2026-09-17 extraction toolchain. The manifest records that compiler's
verbose identity and SHA-256 digests. `scripts/check-source.py` compares the
copies with the installed sources before and after verification; the fingerprint
also covers those live source files. Apache-2.0 and MIT license texts are
preserved from the installed toolchain.

Only selected definitions are transparently extracted: the u64-to-usize
conversion, Cursor's structure/get_ref/position/set_position, Slice AsRef and
shared-reference AsRef forwarding, and the Bound/RangeBounds declarations used by
the original range normalizer. Capturing an entire source file is an identity
record, not a proof of its other definitions. The selected Cursor/AsRef bodies
are ordinary safe field/reference operations. Other standard-library primitives
continue to use the existing reviewed backend models.

The relation between a pinned Rust toolchain, its compiled standard library and
its shipped source remains part of translation/compiler trust. Hash checking is
source consistency evidence, not a formal correctness proof of rustc or the
whole Rust standard library.
