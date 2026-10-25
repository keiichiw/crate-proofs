# Independent oracle review — safe buffer consumption

Reviewer: independent specification/oracle agent (Astra role). Target: bytes1.12.1, unchanged release76c0fbb54ed4336caf9d2311658a2f4a5627c21d.

## Verdict and counting

Accept semantic adequacy of the current126 theorem roots and56 public API mappings for their explicitly stated domains and translation boundaries, subject to successful separate regeneration, compilation and strict transitive axiom audit. Root count includes helpers, generic laws, concrete instances, error/sequence corollaries and tool correspondence; it is not a count of126 APIs. This is a semantic review, not a claim that the oracle independently ran the mechanical checks. The reviewer defined specifications and reviewed artifacts, but implemented no proofs.

The original independent specification is retained. No universal whole-crate or all-safe-API correctness claim is accepted. In particular, the signed variable-width checked-read discrepancy remains a failed desired obligation, not a proved intended behavior.

## Accepted mathematical contracts

The previously reviewed structural Take, Chain, Limit and IntoIter methods preserve exact fields and universal mutable-reference writebacks. Reader/Writer structural methods add three public accessors plus an internal constructor each. Seven public construction wrappers preserve exact inputs, order and stored limit through actual constructors, including BufMut wrappers with unused operational bounds. These field proofs imply no unsafe BufMut correctness. Prefix/concatenation view definitions are mathematical abstractions, not independent guarantees about writable storage.

The sign-extension helper covers every u64 value and widths0..8 with exact integer low-bit signed interpretation; negative subtraction is Int subtraction. Two Cursor arithmetic helpers retain explicit64-bit hypotheses, arbitrary operands and exact min/truncated-subtraction results. Arithmetic conversion helpers in VariableReads are supporting mathematical results, not proofs of variable-width Buf APIs.

Concrete slice advance and copy_to_slice retain exact suffix/prefix and both mutable outputs, with all valid lengths including zero/exhaustion. Invalid lengths yield modeled panic, not post-unwinding-state claims. Consecutive advances consume the exact combined suffix.

BufferLaws is an explicit Prop record of conditional total-success interface laws, using saturated remaining counts. It introduces no global application axiom. slice_laws discharges all four fields using the generated actual slice dictionary and bodies. Take and Chain generic proofs therefore have both honest hypotheses and concrete grounding. Take remaining/chunk/advance cover arbitrary limits including limits beyond inner length, exact inner suffix and limit decrease; over-limit advance yields assertionFailure. Chain remaining is min(usize::MAX,concatenated length), chunk selects the first nonempty side's chunk, and advance consumes first then second with exact component drops. No unnecessary combined-length representability premise excludes large conceptual chains. Closure proofs assemble dictionaries from actual generated methods, and compose Take with Chain. Two-step consumption corollaries preserve exact visible suffixes.

Iterator next returns exact head and drops one byte, or returns None with identical state on exhaustion. Size hint characterizes the actual saturated count pair; exact mathematical length requires representability and is discharged for slices. Two-step exhausted stability is proved; this is not mislabeled as a universal exported iteration-history theorem.

The full original default try_copy_to_slice loop is proved for arbitrary lawful chunk partitions. Nonempty chunk progress yields a strictly decreasing destination-length measure; no artificial assumption that the first chunk covers the destination remains. Success copies exactly the original prefix and consumes the complementary suffix. Insufficient input returns recoverable Rust Err with exact requested/available values and identical input and destination states. Concrete slice and Take/Chain/nested-Take-of-Chain applications use proved method dictionaries. The default checked loop is distinct from the overridden concrete slice unchecked copy method; neither alone proves every generic unchecked wrapper.

Four actual concrete slice byte-reader methods get_u8/get_i8/try_get_u8/try_get_i8 have exact byte value and suffix contracts. Signed8 is x below128, otherwise integer x-256. Checked empty reads are successful model evaluations returning Rust Err{requested:1,available:0} with the identical input state. Unchecked empty reads produce modeled panic. The emitted dictionary binds actual slice operations; forwarding shared-reference bodies are not assumed correct.

Cursor remaining/chunk/advance cover every raw position, including beyond end and u64::MAX, under explicit64-bit target premise. Generic proofs require only the actual AsRef result for the current inner value; this is sufficient because methods preserve inner and AsRef is represented as a pure function. Array and actual standard-library shared-slice AsRef instances discharge this condition. Remaining is truncated length-minus-position, chunk is exact drop(position), advance preserves inner exactly and increments position without overflow. Zero advance preserves the entire Cursor for all positions. Invalid amounts produce modeled panic. Residual-view and two-step sequence corollaries are exact.

Reader::consume is separately verified as the actual direct call to inner.advance: generic lawful-state suffix consumption and concrete slice suffix grounding. No Reader read/fill_buf or general I/O contract is inferred from it.

## Source correspondence and translation boundaries

Seven maintained generated models are reviewed: Bytes, BytesConsumption, BytesAdapters, BytesCopy, BytesNumeric, BytesCursorSlice and BytesReader. They retain actual upstream algorithm bodies/source spans, not convenient replacement Rust algorithms. Cross-model dictionary/helper equalities and generated slice grounding support the composition proofs. Standard indexing/copying/scalar models, valid borrowing, Rust-to-Lean translation and the Lean kernel remain trusted boundaries; functional list results do not prove raw-pointer aliasing or unsafe memory invariants.

The pinned core repair preserves Never-returning calls and inserts only unreachable normal-success continuations. never_continuation_exact proves the semantic equality for every Result Never, preserving original effects/failure/divergence. It does not verify the OCaml implementation. Formatting dictionary erasure is definitionally equal to the PREEXISTING model that ignores formatting and returns unit; it is not a proof of real diagnostic formatting/effects. Namespace hygiene and the trait-filter-length correction are reviewed translation changes.

BytesBuf projects only remaining/chunk/advance/has_remaining types and contains no laws. Rooted slicing preserves executable bodies and their referenced dependencies, removes only unused modeled trait fields, and fails on reachable omitted methods/missing dependencies. Metadata used for name resolution remains available. Regression evidence is bounded, not an exhaustive verified dependency analysis. It is not acceptable to infer correctness of erased unsafe methods.

A separately pinned stage2 tool is used for numeric extraction. Its shared-reborrow normalization applies only to the adjacent NoRetag temporary-copy/shared-reborrow pattern, with exact types, nonargument temporary and unique-use guards; calls and other operations remain untouched. Negative extra-use/retag/mutable-borrow/nonadjacency tests support that boundary. The argument-temporary mutant was invalid input, so that test is weak evidence and is not counted as a valid semantic regression. This is reviewed/tested compiler normalization, not a formal Rust aliasing theorem.

Stage2 declaration ordering permutes intact original groups, preserving each definition text. Its dependency ordering excludes registered backend trait-declaration emission edges (no generated definition) and initializer provenance backedges, while retaining executable dependencies and rejecting remaining cross-group cycles. These exclusions govern emission ordering, not permission to erase reachable code. Separate core/numeric pins and exact patch hashes are essential. Full compiler correctness is not claimed.

## Outstanding obligations and finding

See the safe-scope ledger and blocker evidence for uncompleted safe families. Variable-width numeric reader API correctness is not covered by scalar conversion lemmas. The independently found checked signed-read issue is preserved: width1 byte255 returns Ok255 in try_get_int while get_int returns-1; analogous widths1..7 differ for all-255 input. The reproduction checks actual results and exact consumed suffixes, but is runtime evidence rather than a universal theorem. A proof characterizing zero extension would not discharge the desired signed specification.

Range normalization, unproved I/O/vectored operations, excluded unsafe-dependent readers/Bytes ownership/BufMut operations, allocation/refcounts/concurrency and whole-crate memory safety remain outside accepted coverage unless explicitly mapped by a later audited extension. The current result must remain described as partial verification with concrete safe consumption, not full verification of bytes.

No semantic deficiency was found in the claims actually accepted above. Mechanical proof/build/source identity outcomes belong to the integrated verifier's separate evidence. Snapshot hashes below identify what this oracle reviewed.

## Reviewed snapshot hashes (SHA-256)

- `verification/specification.md`: `c824b39384c6433fc5befd696a0cc92bee1bfc8496084b226b48d3142878212c`
- `verification/safe-scope-ledger.md`: `560c435535d5ed92b8dc316d4d5c4da11bef1cc9afc70d0343dbca4a3099c0ed`
- `proofs/Bytes.lean`: `ac3682f665770ed7df5decf383f9e4215982fc3ea312a80c0419404d77363916`
- `proofs/BytesAdapters.lean`: `78aa0fd1cb2b230091ccd72034a7bf4d0111d8e4c05bb7746453a7ab2766eeae`
- `proofs/BytesConsumption.lean`: `7e3b03675c2845c759748967e720dcd368b0d156933e1b2c41fe4e7a6c0b9bc1`
- `proofs/BytesCopy.lean`: `e6f0c1fded561b4c90be395504cb2401ec292ca46443ead78109ffb12cf99ea9`
- `proofs/BytesCursorSlice.lean`: `0c1ecd72eacc36374ab441a2ad41a08a7222c1669ae5b02d7269bc9a8189b91a`
- `proofs/BytesNumeric.lean`: `5f5c1bd91e00e8e4c98bd163c7dd0c622aad4698179d6b73fec9a1f9155e2917`
- `proofs/BytesReader.lean`: `84eedef5c0c7f04ae7f158dec7608cdc3d32ce8dce2172433acb187d49841c2f`
- `proofs/Proofs/AdapterConsumption.lean`: `20472d8bb0ef9bd171aa6b75b6d7f0eb246a0bd82ec2080e0d7a0eea58967d39`
- `proofs/Proofs/BufferLaws.lean`: `3be7e1cd04b26809268a78eaed9e02c458db975bfb5cf13bdb8834b1df19c681`
- `proofs/Proofs/Chain.lean`: `80f44e2f0f3c514d3eddb783648b5cbcbb5a9f10c26231a192f44adc155ee6da`
- `proofs/Proofs/ChainConsumption.lean`: `a4d56a45850cff515b3c70b935a932014c8fb047bb4b7c6f39189dc54738428c`
- `proofs/Proofs/Consumption.lean`: `29272a60e8fee5e343a426c20d1b30ec2bb71e17599a79fce8e603abe36dc58c`
- `proofs/Proofs/CopyApplications.lean`: `975f43bb0d8c71efc9ca278f0e67d1b47744b6739d1a4e3d57a04697d3e7b696`
- `proofs/Proofs/CopyConsumption.lean`: `2935e9d068107c115d05e29a172d50e824a1a138812f56ff25ba10a35a98da5e`
- `proofs/Proofs/CopyListLemmas.lean`: `11a2d24583e789206857c526334d405130fdefe4be0de837c42a190dcf25a73d`
- `proofs/Proofs/CopyLoop.lean`: `dfb6d6cffe935904e45040dcf45ea04e631d6ec0599c23488e8e008ef649f726`
- `proofs/Proofs/CursorConsumption.lean`: `8d1f44726c2537f6af8a28e7cc08d66c2fbaab29f720542184974a220c406713`
- `proofs/Proofs/CursorHelpers.lean`: `5a31b148d5179f3d7a951766342cf42faf4cbbdcdedff079edd293b4ef739d26`
- `proofs/Proofs/IntoIter.lean`: `4028beeed743a0d5ad51e6fc81f5def7e4b9cd6dba51a16027a82b5de9979276`
- `proofs/Proofs/IoWrappers.lean`: `24103b69c8e1941d6c45e67566ccd633460694fde8be9c15b656617bf6cb569d`
- `proofs/Proofs/IteratorConsumption.lean`: `2822d9a766a1c59f1db227c6844f1b861879c9d2d0d7754d6aa37ab58d93a9e1`
- `proofs/Proofs/Limit.lean`: `e7ca2c3b6b4dd988fc3244f99bfb08d939036dc2c900d1b326dbb3bb58c19018`
- `proofs/Proofs/NumericConsumption.lean`: `e934d3ae5172f30cba5ecfddd617a0fcb497f041af2ef330beb6cb38c0cd3404`
- `proofs/Proofs/PublicConstructors.lean`: `ff3170c7134199cb3f7962285bf4bf39ce399c352b945f50e8594ceda07b5b9c`
- `proofs/Proofs/ReaderConsumption.lean`: `a973219e67626bd5adea2eb81e16947ab3a9b4d6cc203e660b4371a1e6e554d3`
- `proofs/Proofs/SignExtend.lean`: `aea1272a1fc7ae5d8726a41ac9be74941267b4a2e27be278dcc6589ad32c5d9a`
- `proofs/Proofs/Take.lean`: `6f9f60cbc4ce2c5ac0991d52f192941b0f3af038a1f3978d0b5dfce08f380008`
- `proofs/Proofs/ToolCorrespondence.lean`: `7a9d77626088ef954e4fd9caef49df3bd8523f4058e953bdde20a8b6025a3538`
- `proofs/Proofs/VariableReads.lean`: `524a15d23046ec6f541be566737c43f340a185dea31224a98e873aeda01205f7`
- `verification/theorems.json`: `b45a0d3fbaa09fe80b5ab982bc09b4dc254f7e8f00660cf5aa8941ca2cb6ac77`
- `proofs.toml`: `be257da302545a9404a77f5cc0db2a97d3794c86a59d0b4618f700d4b7db046d`
- `verification/tool-repair.json`: `32547d59e4cd1f7939fc261a1bd781501c8be71bd83337228718b6c9e65488e6`
- `verification/numeric-tool-repair.json`: `e344850b68616cadea962fa922406682d4100b49670b8a5e73f96a38acf97670`
- `verification/patches/aeneas-consumption.patch`: `4d1c6c54e0e9519b23ceffcd6624aea0c5915bc98421fd6d6a7db953bf2e9002`
- `verification/patches/aeneas-numeric.patch`: `b5132af4be62d65a1be7454684ade3cde11a4100e0999788a9c273b0788d0049`
