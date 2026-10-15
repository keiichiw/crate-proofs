# How the final RFC850 timeout was resolved

The final timeout under the strong grammar / encoding contract was `Err => !rfc850_syntax(input)` when every weekday-name candidate in the Option chain returned `None`. Neither proof-tree node `.0.37.11` nor the word Jun in the expanded postcondition identified this runtime branch. Adding cuts for month selection or year parsing did not resolve it.

I extracted the actual solver input from the saved Why3 session and confirmed its assumption that all weekday candidates were `None`.

```bash
# Save the session for the failed target. It exits nonzero if the target is unresolved.
cargo creusot --only=prove --why3session --no-cache \
  --why3find-arg=-d --why3find-arg=2 <exact-target.coma>

# Successful extraction command used here (see the ignored run from that time):
why3 session output \
  -C /workspace/.local/share/creusot/creusot_why3.conf \
  -L /workspace/.local/share/creusot/share/why3find/packages/creusot \
  --filter-status=timeout --output-dir=/tmp/rfc-exact-task \
  verif/trial-rfc850-exact-yearcuts-20261007T200032Z/coma/verif/httpdate_rlib/date/rfc850/parse_rfc850_date
```

The helper's old contract conveyed only the structural Seq inequality `None => prefix != name`. The grammar compares individual bytes, so the caller's task did not have enough extensionality to connect those two facts. I added `!prefix.ext_eq(name)` to the helper's rejection contract, bound the Option result to a variable, and added the ghost cut `None => rfc850_weekday(input)==0`. The helper's own VC also resolved, closing the parser without weakening its strong contract or adding a trusted function.

- RFC source SHA-256 before the fix: `2a42d0686da9ad034848066c46f08ffd53130ed30e25298dd316cae59cecbcca`
- RFC source SHA-256 after the fix: `60797ac4ba799a3106222f3d48b05309b81a0e1bc6c5a57a3ae36fda7e40b126`
- Focused run: `verif/trial-rfc850-astra-02/`. Parser: 28 root goals / 254 leaves; helper: 5 roots / 5 leaves; all resolved.

The two source hashes above record the source before and after the fix; they do not show that inputs remained unchanged during proof. Refer to [the main fresh manifest](../evidence/latest/manifest.json) for the final connection to current source and the closed proofs of the full core and callees. Past working sessions are not tracked by Git, but the final Coma and proof.json are saved in the main evidence.
