# Unresolved IPv4 parser callback translation

2026-10-16, unchanged ipnet 2.12.2. This is a backend limitation, not an
ipnet implementation counterexample. Astra independently reviewed the diagnosis.
The user requested stopping on a genuinely unresolved problem; this is the
stopping point after completion of actual IPv4 subnet enumeration.

## Concrete mismatch

After extracting actual FromStr/Parser bodies, generated read_atomically has:

```lean
(coreopsfunctionFnOnceFTupleMutAParserOptionInst :
  core.ops.function.FnOnce F parser.Parser (Option T))
...
let (r, self1) ←
  coreopsfunctionFnOnceFTupleMutAParserOptionInst.call_once cb self
```

Existing Aeneas Std/Core/Ops.lean defines call_once as
`Self → Args → Result Output`. Here that is Result (Option T), but actual
borrowed Parser state must accompany the output as Result (Option T × Parser).
The closure definitions already return that pair. Lean rejects 13 sites,
including lines 1764/1785 (expected product, got Option T), and instance
assignments at 1806, 1891, 1957, 2137, 2223, 2353, 2472, 2522, 2572.
The historical rejected generated source is preserved only in the ignored local
`verification/runs/historical-parser-callback/` archive, excluded from commit and
never imported or counted as proof. The fresh standalone borrowed-callback
reproduction and commit-ready logs are in
`verification/issue-repros/aeneas/evidence/latest/`. Erasing self1 or assuming
the callback leaves Parser unchanged
would lose the implementation's updates and rollback behavior.

## Attempts and outcomes

1. Baseline actual extraction failed context matching in read_seq_3, parser.rs86.
   Loop-to-rec, loops-no-rec and optimized MIR probes retained that failure.
2. A narrow, reviewed candidate changed only failed recoverable context matching
   to Errors.RFailure. The existing caller then duplicates the continuation;
   mismatched contexts are not accepted, strict/loop matching remains an error.
   This cleared the context failure.
3. Lean-only U8↔Char casts were added with exact byte value/modulo256 models
   and five kernel-checked value/roundtrip lemmas. Actual Option.and_then was
   included. Actual str.as_bytes hit unsupported transmute<&str,&[u8]>;
   reviewed normal identity on existing Str=SliceU8 cleared that dependency.
4. Shared extraction then succeeded with no generated axioms/sorry, but generated
   Lean failed with the mutable-callback type mismatch above. Extraction success
   is not proof or even a successful Lean build.
5. --monomorphize-mut=all caused Option/Option<&mut_> naming collisions and still
   emitted the same insufficient FnOnce type. The historical `mutall.log` is in
   the ignored local archive, not packaged as freshly rerun evidence.
6. --monomorphize-mut=except-types with the explicit required remove-adt-clauses
   and lift-associated-types flags failed in NameMatcher with a generic-argument
   mismatch. `mutex-command.json` records the attempted options; its historical
   `mutex.log` is in the ignored local archive.
7. Full monomorphization conflicts with the current Aeneas preset's
   no_gen_tuple_structs and operator/index-to-function settings; no compatible
   supported configuration was established in these attempts. Fuel or trait-field
   filtering cannot add the missing borrowed-argument result type.

No small supported extraction configuration was found. A principled solution
needs borrowed-callback trait/instance translation preserving argument backward
outputs, plus regression coverage. A global change making every FnOnce return
all Args is not valid. No parser body was replaced with a desired model, and no
application axiom, state erasure or hand-edited generated proof was accepted.

## Saved research patch and restoration

attempted-combined-aeneas.patch is an experimental full diff against pinned
Aeneas 8e62dc3dc765602833c86b68dceb18a475a50a8f. It includes previously accepted
compatibility changes as well as the attempted parser additions. It is NOT the
active tool patch; do not apply it on top of the active patch. To investigate,
use a separate checkout of that exact revision, apply this full patch, build
backend Aeneas and its extraction metadata, then rebuild the OCaml executable.
Use parser-extraction-config.json with the shared extractor into a fresh ignored
run directory and run lake env lean on the generated file using that dependency.
This reproduces rejected output, not a completed parser verification.

The active source diff and Aeneas executable were restored byte-for-byte to the
accepted subnet checkpoint, checked against the active compatibility patch and
pinned binary hash. The speculative character/string models are not active and
add no trust to the final accepted scope. No upstream source change or external
publication occurred. Aggregate remains open; its small pure merge helpers do
not establish actual aggregation correctness.
