# Known raw subnet prefix domain — native reproduction

This is **not a newly discovered valid-input algorithm bug**. The supplied expert
review already states this behavior in expert-review.txt (nonempty q>w), and
set-operations-specification.md explicitly gives it a separate panic domain.
The continuation independently reproduced it on unchanged ipnet 2.12.2.

`Ipv4Subnets::new` stores any u8 minimum prefix without checking it. On a nonempty
range, q>32 reaches `Ipv4Net::new(...).unwrap()` and panics with PrefixLenError.
On a reversed/empty range the same invalid q yields None. q=32 works normally.

Reproduce from the repository root, with the pinned environment:

```bash
source ipnet/2.12.2/scripts/env.sh
cargo run --offline --locked --manifest-path ipnet/2.12.2/verification/bugs/subnets-domain-repro/Cargo.toml
```

Observed output:

```text
0.0.0.0..=0.0.0.0 q=33: panic(called `Result::unwrap()` on an `Err` value: PrefixLenError)
0.0.0.0..=0.0.0.0 q=255: panic(called `Result::unwrap()` on an `Err` value: PrefixLenError)
0.0.0.1..=0.0.0.0 q=33: Ok(None)
0.0.0.0..=0.0.0.0 q=32: Ok(Some(0.0.0.0/32))
```

A future documentation PR could explicitly document the admissible minimum
prefix and delayed panic behavior. Changing constructor validation or introducing
a fallible constructor is a separate API-design decision. Do not assert that the
current code promises normal enumeration for impossible IPv4 prefixes. No issue
or PR was published. Formal nonempty-valid-prefix verification continues; this
native reproduction does not establish a Lean theorem about panic behavior.
