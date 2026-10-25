# Independent oracle finding: checked variable-width signed reads

Target: bytes1.12.1 release76c0fbb54ed4336caf9d2311658a2f4a5627c21d.

Independent source review finds that get_int/get_int_le call sign_extend on the unsigned n-byte value, whereas try_get_int/try_get_int_le use the i64 variant of buf_try_get_impl's zero-initialized8byte buffer and convert directly using i64::from_be_bytes/from_le_bytes. The checked path omits n-byte sign extension. Native variants delegate by target endianness.

The desired signed n-byte specification is fixed independently: for n>0, U below2^(8n-1) denotes U, otherwise it denotes U-2^(8n). Therefore input[255] at width1 denotes-1. The checked implementation instead returns Ok(255). This is a failed desired correctness obligation, not grounds to redefine signed semantics.

The reproduction main.rs and observed.txt were reviewed. For every width1..7 it checks all-255 input, confirms unchecked BE/LE/NE results-1, confirms checked results2^(8n)-1, and confirms exact consumption by comparing every remaining slice to the original suffix. Width8 returns-1 for both. Assertions cover actual return values and residual bytes; the observation is runtime evidence, not a universal theorem. The oracle did not rerun the executable independently.

A universal proof of checked zero-extension behavior would be a useful implementation characterization but would not establish the desired signed API contract. Exact consumption can still be verified separately. Keep the pinned source unchanged for verification; any proposed upstream fix is separate work and must not erase this release finding. No unsafe operation in the reproduction is needed to trigger the discrepancy.
