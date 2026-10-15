# English documentation and historical proof evidence

The maintained skills and documentation were translated into English after
commit `da7ba78`. Release captures, proof manifests, generated obligations, and
recorded solver outputs were preserved byte for byte.

Some translated documents are inputs fingerprinted by earlier proof runs.
Those runs remain historical evidence for their original frozen inputs; they
are not fresh proofs of the translated working tree. A strict audit against
the current files will report changed document hashes. Recover the matching
inputs from the recorded commit or snapshot when reviewing an old run.

Do not rewrite recorded hashes to make an old run match translated documents.
A current-input proof claim requires a new run and matching dependency evidence
under the applicable crate's workflow. This translation did not rerun the
formal proofs or change their contracts, assumptions, or recorded scope.

The non-ASCII test string in the httpdate correspondence harness now spells
one existing character as a Rust Unicode escape, preserving its runtime value.
