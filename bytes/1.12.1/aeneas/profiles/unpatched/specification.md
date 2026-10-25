# Unpatched profile: Take structural contracts

Target: unchanged bytes 1.12.1 release, pinned by `source.lock.json`.
All contracts quantify over every `Take<T>` state, with no relation assumed
between its limit and the length or contents of its inner value. `T` is arbitrary.
The independent observable `visible view s` is `(view s.inner).take s.limit.val`;
it does not assume that `T` implements Buf or obeys any Buf laws.

Each theorem asserts total modeled success (`exists out, actual = Result.ok out`)
and the following result or updated state:

| Public method | Required property |
| --- | --- |
| `Take::into_inner` | Returns the stored inner value |
| `Take::get_ref` | Returns the stored inner value in the extracted shared-reference representation |
| `Take::get_mut` | Returns the stored inner value and a writeback function; every replacement becomes the inner value while preserving limit |
| `Take::limit` | Returns the stored limit |
| `Take::set_limit` | Stores the requested limit and preserves the inner value; visible contents follow the independent take specification |

No Rust source, generated Lean, Aeneas compiler, Charon compiler or Aeneas Lean
backend/standard library is patched. Authored proof files establish contracts on
the generated bodies; they are not replacements for those bodies. Lean itself is
the pinned distribution. Only propext, Classical.choice and Quot.sound are allowed
by the theorem dependency audit.

This profile does not claim constructors, Buf operations, consumption, checked
copying, numeric readers, other adapters, Bytes/BytesMut, unsafe memory safety or
whole-crate correctness. The historical default profile's wider theorems are not
included in this profile's inventory or report.

## Signed-reader obligation and finding

For 1 <= n <= 8, interpret n input bytes as an unsigned integer U in the specified
endianness. The expected signed result is U when U < 2^(8*n-1), otherwise
U - 2^(8*n). Successful reads must consume exactly n bytes. In particular, one
byte 0xff denotes -1. This contract is not weakened to match zero extension.

The desired public-reader theorem remains unestablished. Source review during
formal-verification work identified the mismatch, and native execution confirmed
it. The reproduction tests all-0xff inputs at widths 1 through 8 for BE/LE/NE,
checks exact remaining slices, and uses width 8 as a control. They assert the
known discrepancy in this pinned release, so their exit status is zero when the
counterexample is reproduced. These native observations are not Lean theorems.
See [BYTES-001](../../../verification/findings/BYTES-001.md) for
historical provenance and upstream fix status.
