# Packaged current verification evidence

`latest/` is produced only after `bash scripts/verify.sh` completes successfully
on a fresh ignored `verification/runs/check-*` directory. Run
`python3 scripts/package-evidence.py verification/runs/check-XXXXXXXX` with the
reported fresh path to check the verifier's recorded file hashes and copy the
result, before/after input fingerprints, extraction diagnostics, native test
logs, Lake build and transitive axiom audit logs. `latest/package.json` hashes
the selected committed files and names the source run.

Older named `check-*` directories cited by historical results reports are local
research archives under ignored `verification/runs/`. They are not packaged as
fresh evidence for the current result and are not required in a clean checkout.
The maintained proof, inventory, configuration, source checks, tool pins and
full verifier remain the basis of the current 625-theorem claim.
