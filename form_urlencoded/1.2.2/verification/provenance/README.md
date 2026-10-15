# Release provenance inputs

The raw crates.io sparse-index response is `form_urlencoded.sparse-index.jsonl`, saved on 2026-10-13 UTC from `https://index.crates.io/fo/rm/form_urlencoded`. Its SHA-256 is `439570e716416752772cd2157d368d483e7710def266f352d7365e7dd4789b09`. The 1.2.2 row lists archive checksum `cb4cb245038516f5f85277875cdaa4f7d2c9a0fa0468de06ed190163b1581fcf` and is not yanked.

The corresponding archive is preserved as `../../capture/release.crate`; the capture manifest records its hash and extracted file hashes. The capture tool's registry metadata input was locally synthesized from the saved sparse-index 1.2.2 row because the crates.io version API returned HTTP 403. It is not an API response. `../../capture/manifest.json` records this supplied-input provenance.

`../../Cargo.lock` pins the workspace dependency graph. The published dependency requirement is `percent-encoding = ^2.3.0`; the resolved workspace version is 2.3.2 (registry checksum `9b4f627cb1b25917193a259e49bdad08f671f8d9708acfd5fe0a8c1455d87220`).
