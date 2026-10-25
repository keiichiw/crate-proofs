# Independent bytes specification (Astra oracle)

Specification frozen before proof construction, 2026-10-17.
Target: tokio-rs/bytes, release v1.12.1 commit 76c0fbb54ed4336caf9d2311658a2f4a5627c21d. Initially inspected master d38faf7c9d003d6074405dd480db6bdb813cb80f; the selected contracts are unchanged on the release source.
This document states desired semantics, not claims that they have been proved.
Proof status belongs in a separate ledger/report. Proof feasibility must not weaken these contracts.

## Mathematical model

A byte is an integer in [0,255]. A buffer's observable unread content is a finite sequence B of bytes. |B| is its length, take(n,B) its prefix of length min(n,|B|), and drop(n,B) the remaining suffix. Rust usize quantities range over the target machine's unsigned word domain; all lengths and counts in the Rust interface must be representable. Mathematical addition/subtraction has no wrapping interpretation.

For the nonsaturating model below, a valid Buf implementation with abstraction A and representable unread length must satisfy:
* remaining returns |A(s)| without changing state.
* chunk returns some prefix C of A(s). C is empty exactly when A(s) is empty; it need not expose every remaining byte. Reading chunk must not change state or content.
* advance(n), for n <= |A(s)|, terminates successfully with A(s') = drop(n,A(s)). The discarded count is exactly n. No arithmetic overflow or out-of-bounds indexing occurs in this domain.
* Queries and advances preserve the implementation's validity invariant.
These are hypotheses for a generic adapter proof. They must be discharged for every concrete Buf implementation covered by a crate claim. They are not arbitrary axioms that establish the implementation itself.

## Checked reads (initial independent target)

For width w in {1,2,4}, on input content B:
* If |B| >= w, result is Ok(v), unread output is drop(w,B), and consumption is exactly w.
* For little endian, v = sum(i=0..w-1, B[i] * 256^i).
* For big endian, v = sum(i=0..w-1, B[i] * 256^(w-1-i)).
* If |B| < w, result is Err(TryGetError { requested: w, available: |B| }); the entire input state is unchanged. No byte is consumed and no read past the input occurs.
* All branches terminate without panic for valid buffers. w=1 has v=B[0] on success and empty-buffer error {1,0}.

Concrete methods: Buf::try_get_u8, try_get_u16, try_get_u16_le, try_get_u32, try_get_u32_le. Source: src/buf/buf_impl.rs, try_get_u8 lines 1209ff; u16 lines 1280ff; u32 lines 1454ff. The macro at lines 13ff uses an unsafe pointer cast for its contiguous path for wider reads. Therefore a safe rewrite of wider reads is not automatically a proof of those upstream methods. Their contracts remain in scope as unproved obligations when this translation is unsupported.

A proof specialized to &[u8] must establish concrete slice suffix equality, not merely the returned byte or remaining length. A generic proof must handle every legal chunk partition, including a one-byte chunk for a larger read. Invalid/malicious Buf implementations do not satisfy the hypotheses.

## Take adapter (substantive safe-source target)

State is (inner,L), with B=A(inner) and visible content V=take(L,B). L may exceed |B|; imposing L<=|B| would incorrectly exclude valid inputs.
* new(inner,L): preserves inner, stores exactly L, visible content take(L,B).
* limit(): returns L (not min(L,|B|)); no mutation.
* set_limit(K): inner unchanged, limit becomes K, visible content take(K,B). Increasing the limit may reveal previously hidden bytes; it does not rewind bytes already consumed.
* into_inner(): returns the entire current inner state, including any unread bytes beyond L.
* remaining(): returns min(|B|,L), equivalently |V|.
* chunk(): returns take(L,C), where C is the current inner chunk. This is a prefix of V, and nonempty exactly when V is nonempty, assuming the inner Buf laws.
* advance(n), for n <= min(|B|,L): calls a valid inner advance, yields inner content drop(n,B), yields limit L-n, and has visible content drop(n,V). There is no underflow or panic in this domain. n=0, L=0, empty B, L>|B|, and n=remaining must be included.
* For n>L the upstream explicit assertion fails before changing inner or L. For n<=L but n>|B|, upstream delegates to inner.advance; generic Buf does not guarantee identical panic behavior/state after panic for all implementations. Do not invent a generic error-atomicity claim here.
* get_ref exposes the same inner; get_mut changes the inner according to the caller's mutation while leaving L unchanged. Re-establish the inner invariant after mutations.

Source: src/buf/take.rs at pinned commit. The safe selected methods are separable from copy_to_bytes (depends on Bytes) and chunks_vectored (contains unsafe lifetime conversion). Excluding those methods must be explicit. A selected-method extraction is not whole-crate extraction.

## Internal integer helpers (independently frozen extension)

Source: src/lib.rs lines 116–130 at the release commit, behind the std feature. These are private arithmetic helpers; proving them does not prove any consuming Cursor or adapter method. The following specifications derive from the original conversion branches and standard arithmetic meaning before helper proofs are finalized.

* min_u64_usize(a:u64,b:usize) terminates successfully for every raw input and returns r with natural value r = min(a,b). No extra bound such as a<=usize::MAX is permitted as an input precondition. The output is representable since r<=b<=usize::MAX. If conversion of a fails on a narrower platform, a>usize::MAX>=b, so returning b satisfies exactly the same contract.
* saturating_sub_usize_u64(a:usize,b:u64) terminates successfully for every raw input and returns r with natural value r = max(a-b,0), using natural truncated subtraction. No input restriction b<=a or b<=usize::MAX is permitted. If conversion of b fails on a narrower platform, b>usize::MAX>=a, so returning zero satisfies the same contract.
* Neither function wraps, panics, or mutates caller state. Boundary inputs include zero, equal operands, maximum values, and b>a for subtraction.

The desired arithmetic meaning is independent of pointer width. The current selected extraction target is x86_64, with usize width 64; a proof using its compiler-specialized infallible u64-to-usize conversion establishes this contract only for that target. It must not be reported as verification of the separate 32-bit conversion-error branch. Platform-width hypotheses belong in the report and theorem assumptions, not silently in the input domain.

## Continuation: sign extension (independently frozen before proofs)

Source: private sign_extend in src/buf/buf_impl.rs, release lines 88–97. This is an algorithmic helper, not itself a proof of the public signed Buf readers that call it.

For every val:u64 and nbytes:usize with 0 <= nbytes <= 8, the function terminates successfully without arithmetic failure, returning an i64 with this mathematical integer value:
* nbytes=0: return 0, for every val, including nonzero val.
* 1<=nbytes<=8: let k=8*nbytes and u=val mod 2^k. Return u if u<2^(k-1), otherwise return u-2^k.

This is signed two's-complement interpretation of exactly the low k bits. Input val is arbitrary; a premise val<2^k would improperly exclude valid raw helper inputs. The output lies in [-2^(k-1),2^(k-1)-1] for positive widths and always fits i64. In particular, width8 must handle the entire u64 range, with values >=2^63 interpreted negatively. Width1 must discard high bits, e.g. val=511 gives -1. There is no mutation. For nbytes>8, the checked-arithmetic source evaluation underflows at 8-nbytes; no total-success claim applies. Do not promise identical overflow behavior for Rust build configurations that disable overflow checks, and do not model invalid widths as successful zero results.

## Continuation: Chain state operations (independently frozen before proofs)

Source: src/buf/chain.rs lines 27–128. Abstract content of state (a,b) is A(a) concatenated with B(b). Here A and B may be any content views; these structural specifications do not establish Buf trait behavior.

All six operations terminate successfully for every raw state, with no Buf-law or representable-combined-length precondition:
* Chain::new(a,b), internal pub(crate) constructor: store exactly a and b, so abstract content is A(a) ++ B(b). This is not a proof of the public Buf::chain wrapper.
* first_ref: return exactly a, preserving the state in the shared-reference semantics.
* last_ref: return exactly b, preserving the state in the shared-reference semantics.
* first_mut: return current a and a writeback map which, for EVERY replacement a', produces fields (a',b). The untouched last field is exactly preserved; abstract content becomes A(a') ++ B(b).
* last_mut: return current b and a writeback map which, for EVERY replacement b', produces fields (a,b'). The untouched first field is exactly preserved; abstract content becomes A(a) ++ B(b').
* into_inner: return exactly the ordered pair (a,b), retaining both entire current values.

Five are externally public inherent methods; new is internal. No claim follows for Chain::remaining/chunk/advance, unsafe BufMut operations, or iterator behavior merely from these structural contracts. The existing saturation caveat on remaining is unchanged.

## Optional continuation: range normalization obligation

Source: private range helper src/lib.rs lines 138–170. This specification is frozen as an obligation even if extraction is blocked. For a lawful RangeBounds implementation whose bound queries terminate and return the declared stable endpoints, normalize start Included(n) to n, Excluded(n) to n+1, Unbounded to0; normalize end Included(n) to n+1, Excluded(n) to n, Unbounded to len. Addition here is mathematical, not wrapping. Success occurs exactly when normalized endpoints are representable usize values and begin<=end<=len; result is exactly (begin,end). Empty ranges at len are valid. All other normalized-bound cases follow the explicit checked-add/assert panic path. Generic query effects/failure require separate assumptions and cannot be silently eliminated. Proving this helper does not prove all Bytes range consumers.

## Continuation: Limit state operations (independently frozen before proofs)

Source: src/buf/limit.rs, struct and inherent functions before its unsafe BufMut implementation. State is (inner,L), with no requirement L <= inner writable capacity. Every function below must terminate successfully for all raw inner values and all usize limits.

* Internal limit::new(inner,L): store exactly inner and L.
* Limit::into_inner and get_ref: return exactly the current inner value. The getter preserves the shared-reference state.
* Limit::get_mut: return the current inner and a writeback map that, for EVERY replacement inner', produces (inner',L). The stored limit is unchanged even when caller mutation changes the inner writable capacity.
* Limit::limit: return exactly L, not any clamp against inner capacity.
* Limit::set_limit(K): preserve inner exactly and set the limit to exactly K. No bytes are written, initialized, or discarded by this structural update.

Five are externally public inherent methods; the free constructor is pub(super), hence internal. The unsafe BufMut implementation is excluded from these structural claims: no proof of remaining_mut/chunk_mut/advance_mut, memory initialization, capacity safety, or caller unsafe preconditions follows. In particular, reading the stored limit does not promise that many bytes of writable inner storage exist.

## Continuation: IntoIter state operations (independently frozen before proofs)

Source: src/buf/iter.rs lines 22–105, together with public IntoIter re-export in src/buf/mod.rs. State is just inner; an abstract unread content view, if supplied, is A(inner). All four methods are public and must terminate successfully for every raw inner value, without a Buf trait hypothesis.

* IntoIter::new(inner): store exactly inner, preserving its entire content view.
* IntoIter::into_inner and get_ref: return exactly the current inner, preserving its entire current unread content. The shared getter does not mutate it.
* IntoIter::get_mut: return the current inner and a writeback map which for EVERY replacement inner' produces a wrapper with exactly inner'. Its new view is A(inner').

These contracts establish storage/access behavior only. They do not establish Iterator::next, size_hint, ExactSizeIterator length, fusion, or correspondence between iteration and Buf consumption. Unlike the internal Take/Chain/Limit free constructors, IntoIter::new is an actual public associated constructor and may be recorded as public API coverage.

## Buffer-consumption request: prioritized concrete obligations

This extension is frozen before new consumption proofs. Unlike structural accessor coverage, these obligations require actual unread state changes implemented by the selected upstream consumption bodies. A newly written safe implementation with similar intent is not a substitute. If a tool patch is necessary, preserve the original implementation and separately audit how the patch changes extraction/standard-library boundaries.

Priority 1 — actual Buf for &[u8], src/buf/buf_impl.rs:
* For every valid immutable Rust slice s (including empty), represent its exact byte list B. No extra restrictions on byte values or slice length beyond a valid representable Rust slice are permitted.
* remaining() terminates successfully with |B|; chunk() terminates successfully with the exact original slice contents B. These must ground the dictionary used by consumers, not be assumptions about it.
* advance(n), for every usize n<=|B|, terminates successfully and returns through the mutable-reference writeback the exact suffix drop(n,B). Length is |B|-n. The underlying immutable bytes are not modified. Include n=0 and n=|B|. Proving only length decrease is insufficient.
* For n>|B| the original slice implementation takes its panic path before assigning the slice state. A successful-consumption theorem may use n<=|B|, but must label the failure domain separately rather than silently claim all-input success. Exact panic text is not required. A model that erases panic state cannot itself establish unwinding-state atomicity; report that boundary explicitly.

Priority 1b — actual overridden Buf for &[u8]::copy_to_slice, src/buf/buf_impl.rs lines 2919–2931:
* Input is any valid immutable source slice S and valid mutable destination slice D allowed by Rust's aliasing rules. Let n=|D|. For every such pair with n<=|S|, the actual implementation terminates successfully, updates the destination to exactly take(n,S), and updates the source cursor to exactly drop(n,S). Destination length remains n. The source's underlying immutable byte contents are unchanged; only its slice cursor changes.
* Destination's initial byte values are completely arbitrary and impose no precondition. Zero-length destination, empty source with empty destination, partial copy, and exact exhaustion n=|S| are included. All n output bytes equal the original source prefix in order; checking only copied count or remaining length is insufficient.
* Both mutable outputs must be covered by the generated backward/writeback result. The theorem must concern the real overridden slice copy implementation plus its actual advance call and standard slice-copy model, not a manually written copy-and-drop implementation.
* For n>|S| the source checks and calls panic_advance before executing destination copy or source advance. This is a source-level failure-path observation; do not claim a proved exact unwinding state or rollback unless the extracted observable model supports that claim. No unconditional-success theorem is intended on this invalid domain.
* Rust borrow validity is part of the valid-state domain: a mutable destination cannot overlap live immutable source storage in a way forbidden by Rust. In the pure extracted model, inputs are value-level slices; do not infer a separate theorem about raw-pointer aliasing from the functional copy theorem.

Priority 2 — actual Buf::try_get_u8 specialized to the real slice instance:
* B=x::xs: total successful function evaluation returning Rust Ok(x), with exact new slice contents xs. Exactly one byte is consumed and no underlying byte is modified.
* B=[]: total successful function evaluation returning Rust Err(TryGetError{requested:1,available:0}), with exactly the same empty slice state. Do not confuse Rust's recoverable Result::Err with an Aeneas execution failure.
* Thus all valid slice states are admitted. Chunk indexing and advancing must themselves be proved safe on the success branch, grounded by the extracted slice dictionary.

Priority 3 — actual Take::advance and checked consumption on slices:
* Valid raw Take states are every valid inner slice B and every usize L, including L>|B|. Visible content is take(L,B).
* For n<=min(|B|,L), total success gives inner drop(n,B) and limit L-n, hence visible drop(n,take(L,B)). Exact underlying suffix and limit are both required; no assumption L<=|B| is allowed.
* An actual try_get_u8 over this grounded adapter obeys the existing checked-read law on its visible sequence. If L=0 with nonempty hidden B, it returns the empty-visible error without consuming B or changing L.
* Generic versions may instead be conditional on explicit total-success remaining/chunk/advance laws and validity preservation for the inner implementation. Those are interface hypotheses, not discharged concrete correctness. Concrete claims require an instantiation proof with the actual extracted slice implementation and its dictionary.

Priority 4 — actual Chain::advance:
* State consists of arbitrary valid slices A and B; the conceptual content is A++B. For any representable n<=|A|+|B|, total success must yield first content drop(n,A), and second content drop(max(n-|A|,0),B). Equivalently, the first buffer is consumed before any byte in the second, and combined content becomes drop(n,A++B).
* n=0, empty first or second, n<|A|, n=|A|, n>|A|, and n=combined length whenever representable must be covered. Combined length is mathematical; do not require |A|+|B|<=usize::MAX merely to prove advance. A premise n<=saturating remaining is equivalent here for representable n. If the proof separately uses exact remaining=combined length, that lemma does need the representability condition already stated earlier.
* Generic exact-state output may be replaced with exact abstract content plus explicit validity/interface assumptions. Source n beyond total length can partially consume the first before the second panics; do not assert generic failure atomicity for Chain.

Priority 5 — actual IntoIter::next:
* On an actual slice-backed iterator, B=x::xs gives total success returning Some(x), inner xs; empty B gives total success returning None with unchanged inner. Each Some consumes exactly one byte and preserves every later byte.
* Repeated consumption should compose to return exactly a prefix and leave the complementary suffix; repeated None on an empty slice leaves it empty. These may be corollaries, but single-step correctness must concern the actual extracted next implementation.
* Generic proof requires actual has_remaining behavior or a proved reduction to remaining>0, nonempty prefix chunk, and exact advance semantics. Replacing next with a hand-written recursive list operation proves only a model and is insufficient.

For all priorities, total success means existence of an output with generated implementation = Aeneas Result.ok output, plus the stated Rust-level return and resulting state. Report original source, generated body/dictionary, model trust, interface hypotheses, concrete instances, and omitted panic/unwinding obligations separately. No arbitrary axiom, assumed target-function correctness, disabled bounds checks, or opaque replacement of a consuming function may discharge these obligations.

## Safe adapter completion: laws and projection boundary

These contracts are frozen before projected-interface proofs. All earlier concrete and generic specifications remain binding.

A projected Buf dictionary is lawful relative to a state invariant Inv and view V only if the following are PROVED for its actual methods: (1) remaining terminates with the representable unread count; (2) chunk terminates with a prefix of V, empty iff V is empty, with no state change; (3) valid advance n terminates with V dropped by n and preserves Inv; (4) actual has_remaining terminates with remaining>0. Generic proofs may quantify over dictionaries and these hypotheses; they must not install axioms asserting the laws for a concrete implementation. An actual slice instance has V=s.val and Inv=true within the valid Slice model, and its leaf laws must be proved from generated bodies.

For ordinary representable views, remaining=|V|. For Chain with potentially unrepresentable total length, remaining=min(usize::MAX,|A|+|B|). Such a saturated buffer must not be slipped into an exact-length law without proving its total length representable. Generic composition may either support a saturated-count variant of the laws, or explicitly restrict only the exact-count theorem to representable total length. Concrete Chain advance and chunk retain the broader domains specified earlier.

Take remaining/chunk/advance are exact functions of a lawful inner dictionary, arbitrary inner state satisfying Inv, and arbitrary usize L: remaining=min(inner remaining,L); chunk=take(L,inner chunk); advance n under n<=min(inner remaining,L) yields inner suffix and L-n, preserving the view law. For slice grounding, inner remaining=|B|, inner chunk=B, so chunk equals take(L,B), including hidden content when L=0. No premise L<=|B| is allowed.

Chain remaining is saturating addition. Its chunk is exactly the first chunk when the first has remaining bytes, otherwise exactly the second chunk. On slices this is exactly A when A is nonempty and exactly B when A is empty. Generic chunks may be shorter than their full content; a theorem must not assert that the whole concatenated sequence is returned. Advance consumes first then second with the exact split already specified, preserving validity.

IntoIter::next obeys the previously frozen head/tail contract for every lawful dictionary, with exact resulting view. size_hint returns (r,Some r) where r is the actual inner remaining count. For slice, Take-of-slice and representable Chain content, r is the exact unread list length; without the representability premise, a Chain-backed size hint is a saturated count, not a theorem that an unrepresentable mathematical iteration length equals usize. Empty iterator calls are unchanged and may repeat indefinitely; positive calls consume exactly one byte.

get_u8: nonempty view x::xs gives total success returning x and new view xs; empty view follows the modeled panic path, without unwinding-state claims. try_get_u8 returns a recoverable Rust error with requested1/available0 on empty input and unchanged state, and returns Rust Ok(x) with xs otherwise. No generic interface law may assume these target functions' correctness to prove themselves.

try_copy_to_slice with destination length n: if n<=|V|, total success Rust Ok(()) yields exact destination take(n,V), residual drop(n,V), and preserved destination length; if n>|V|, total successful evaluation returns Rust Err{requested:n,available:remaining}, preserving the entire input state and destination. In the saturated variant, n is usize-representable, so comparison against remaining still correctly determines whether n<=mathematical length. Loop termination requires lawful chunk progress: nonempty remaining view implies nonempty chunk. The ranking measure is the number of destination bytes still to fill. copy_to_slice's default unwrap wrapper has the same success result and modeled panic on insufficient input. A concrete overridden slice copy theorem does not itself prove this generic loop or default wrapper.

Projection acceptance: removed dictionary fields must be unused by EVERY retained body and all its retained callees. Keep every referenced method, associated type, supertrait dependency and dictionary identity needed for dispatch. Preserve upstream method bodies and their control/data flow; do not replace them with list models. A projection is an extraction boundary, not evidence that erased unsafe methods are correct. Require reproducible projection configuration, source provenance, closed generated dependency graph, and concrete instance proofs using retained actual leaf methods. The projection principle is extensional independence from unused fields; a tool-level implementation of filtering is still a reviewed/tested translation component unless separately verified.

## Independently frozen numeric completion contracts and discrepancy

For width n in0..8 and unread byte sequence B, let U_LE(n,B)=sum(i=0..n-1,B[i]*256^i), and U_BE(n,B)=sum(i=0..n-1,B[i]*256^(n-1-i)). Empty sums equal0. All unsigned get/try_get_uint methods consume exactly n bytes on success and leave drop(n,B), returning the appropriate U. Native-endian methods use the compile target's endianness (current x86_64: little endian); a current native proof does not cover a big-endian build automatically.

For signed n-byte interpretation, S(0,U)=0; for positive n, S(n,U)=U when U<2^(8*n-1), and S(n,U)=U-2^(8*n) otherwise, with integer subtraction. This is the desired signed-reader contract for both unchecked and checked families. get_int/get_int_le/get_int_ne implement this through sign_extend and must satisfy it.

Independent inspection found a discrepancy in release source: try_get_int and try_get_int_le invoke the i64 form of the zero-filled8byte macro and do NOT call sign_extend. Their actual successful numeric result is signed64(U), where U is the zero-extended n-byte value. For n<8 this is nonnegative U, not S(n,U) whenever the selected width's sign bit is1. Example: byte[255], width1 should represent -1 by the desired n-byte signed contract, but the checked implementation's macro yields255. Width8 agrees with signed64 interpretation. try_get_int_ne delegates to the affected endian method. A proof of this actual zero-extension behavior must be labelled implementation characterization and must NOT be reported as discharge of the desired signed contract. Preserve a counterexample/regression and report the discrepancy; do not weaken the desired specification to fit the implementation.

For all12 variable-width methods: n>8 reaches panic_does_not_fit before any shortage check/copy and must not return a recoverable insufficient-input error. For n<=8 and n>|B|, try methods return Rust Err{requested:n,available:remaining}, preserving input state; unchecked methods panic through their unwrap path. n=0 always succeeds with0 and no consumption, even on an empty buffer. Generic proofs assume proved lawful copy/count semantics; concrete claims require actual instance grounding. Panic observables retain previously stated formatting/unwinding boundaries.

get_i8/try_get_i8 on nonempty B=x::xs return integer x when x<128 else x-256, leaving exactly xs. On empty B, get_i8 panics; try_get_i8 returns Rust Err{requested:1,available:0} and unchanged state. All input byte values are included.

## Independently frozen std wrapper structural contracts

Reader and Writer free new constructors store the exact supplied buf and are internal because their modules are private. Public get_ref and into_inner return exactly the current buf. Public get_mut returns that buf and a writeback map that accepts EVERY replacement and yields a wrapper containing exactly that replacement. All these structural operations terminate successfully for every raw state admitted by their trait-bound Rust signatures; no Buf/BufMut operational law is needed because the bodies invoke no such methods. A projected empty or restricted dictionary must preserve this distinction and cannot imply the unsafe BufMut interface is proved. There are three public methods and one internal constructor per wrapper, not four public methods. These statements do not establish Reader read/fill_buf/consume or Writer write/flush. The independent range normalization contract already frozen above remains unchanged.

## Public construction wrappers (independently frozen)

For every state accepted by the original method trait bounds, the following original wrappers must terminate successfully and preserve exact input values through their calls to the original constructors:
* Buf::take(self,L) returns Take with inner=self and limit=L, for every usize L.
* Buf::chain(self,next) returns Chain with a=self and b=next, in that order.
* Buf::reader(self) returns Reader with buf=self.
* BufMut::limit(self,L) returns Limit with inner=self and limit=L for every usize L; no writable-capacity premise or operational BufMut claim is introduced.
* BufMut::chain_mut(self,next) returns Chain with a=self and b=next, exactly and in order; this does not establish unsafe mutable-buffer consumption.
* BufMut::writer(self) returns Writer with buf=self. No BufMut operational correctness follows from this unused-bound structural method.
* IntoIterator::into_iter for Chain returns IntoIter whose inner is exactly the original Chain, preserving both fields and order. Other selected concrete into_iter implementations must be identified separately; this is not a blanket proof of all IntoIterator instances.

No byte consumption, allocation, or interface-law hypothesis is required for these field-level wrapper contracts. Their operational callees must be actual extracted constructors or proven exact projections of those constructors. Wrappers are public methods, distinct from the internal constructors already covered.

## Independently frozen Cursor consumption contracts

Source: actual Buf implementation for std::io::Cursor<T:AsRef<[u8]>>, src/buf/buf_impl.rs. State is (inner,position:u64). Supply an explicit AsRef law: for every admitted inner, the actual AsRef method terminates successfully returning an immutable slice whose contents are a stable view B(inner), without changing inner. The view length must be representable as a valid slice. Concrete slice/array cases must discharge this law for the actual standard-library instance; it cannot be assumed as a concrete implementation fact.

For every inner satisfying this law and every raw u64 position p, including p>|B|:
* remaining terminates successfully and returns max(|B|-p,0) as a natural usize value.
* chunk terminates successfully and returns exactly drop(p,B), equivalently the slice beginning at min(p,|B|); p beyond end gives empty, not panic.
* advance(n) for representable usize n<=max(|B|-p,0) terminates successfully, preserves inner EXACTLY and changes position to integer p+n, without overflow. In particular n=0 is valid for every p, including u64::MAX and positions beyond end, and preserves the whole Cursor. Do not impose p<=|B| as a raw-state invariant.
* advance(n) beyond that remaining count takes panic_advance; modeled panic is admissible, with no unsupported claim about unwinding/destructors.

The prior internal conversion helper proofs use the extracted64-bit-target premise. A Cursor proof depending on them must state that premise explicitly and cannot advertise32-bit coverage. Under64-bit target the positive-count sum is bounded by the valid slice length; zero count never changes p. A theorem about visible content alone is insufficient for advance: exact underlying value and position update are required. These are actual Cursor Buf method contracts, distinct from modeling Cursor storage or proving only the arithmetic helpers.

## Reader consumption contract

Independently derived from the previously inspected src/buf/reader.rs BufRead::consume body, which delegates directly to self.buf.advance(amt). For every Reader state whose actual inner projected Buf dictionary satisfies the frozen laws, and every usize n<=the inner unread view length, consume terminates successfully with the exact residual inner view drop(n,old view). Concrete slice grounding must use actual slice methods/laws, giving exact stored slice contents drop(n,old slice). Zero and exhaustion are valid; no byte-value restriction applies. No generic invalid-count error atomicity or unwinding state is claimed because failure behavior delegates to the inner implementation. This proves consume only, not Reader::read or fill_buf or all BufRead guarantees. Structural-only Reader exclusions earlier in this document refer to those structural theorems and do not preclude this separately scoped obligation.

## Full-crate obligation ledger (desired scope, no proof claims)

P0. Source-to-model correspondence: exact commit, configurations, selected definitions, extraction commands, unmodified generated Lean, every omitted/opaque definition, every manual rewrite and its refinement evidence. No sorry/admit, false axiom, external replacement of the target result, or circular specification assumptions.

P1. Buf foundational laws for actual slice instance and Take; checked read success/value/consumption/error atomicity; copy-to-slice exact prefix copy, unchanged destination and input on insufficient bytes, and progress/termination across fragmented chunks. Chain must expose concatenation and consume first then second. Its actual remaining() is saturating_add of the two counts: min(usize::MAX, r1+r2). An exact remaining=concatenated-length law requires the additional representability condition r1+r2 <= usize::MAX; for arbitrary states retain saturation semantics and do not assume that condition silently; Take obeys the contracts above. Wider integer and signed reads need endian/sign-extension correctness, valid variable widths, and documented panic domains.

P1. Bytes immutable content operations: len/is_empty and indexing/slicing match its abstract byte sequence; valid slice/range bounds produce exact subsequences; split_to(at) returns prefix and retains suffix, split_off(at) retains prefix and returns suffix; truncate(n) keeps take(n,B), clear empties; clone preserves content and subsequent independent cursor/split changes do not alter peers' byte contents. Invalid range/bound arithmetic follows documented panic contracts. Zero-copy complexity and sharing need separate resource/representation reasoning.

P1. BytesMut content operations: len <= capacity and initialized prefix invariant; extend/put append exact bytes; resize truncates or appends the requested fill byte; split operations give documented content and capacity ownership; freeze preserves bytes and yields immutable Bytes; reserve preserves content and provides documented capacity, allowing allocator failure semantics. Spare capacity is not readable initialized content.

P0 for a claim of memory-safe whole crate: unsafe pointer provenance, allocation/deallocation layout, uniqueness and aliasing, initializedness, pointer arithmetic, refcount lifetime, panic/drop cleanup, ownership across split/freeze/clone, concurrent Send/Sync/refcount synchronization. These are not established by safe functional extraction or abstract Buf laws.

P2. BufMut advance_mut obligations and unsafe caller preconditions; chain/take/reader/writer vectored and std I/O consistency; native endian dependence; floats bit-pattern preservation; exhaustive API/configuration matrix, no_std/std and target-width behavior. Efficiency and allocation bounds are distinct nonfunctional claims.

## Oracle acceptance requirements

For each theorem, identify the exact extracted Rust function and which contract above it establishes, its invariant hypotheses, whether it establishes termination and absence of runtime failure, and whether it is generic or slice-specific. Runtime differential tests add evidence but are not refinement proofs. Separate proved selected-source behavior, assumed library semantics, tested correspondence, unsupported features, and remaining obligations. Whole bytes verification is accepted only when the complete applicable ledger is discharged, including unsafe/concurrent implementation obligations; a bounded safe subset must be labelled a partial result.

## Stage3 extension: default unchecked copying and exact error correspondence

The accepted126-root/56-API baseline is preserved. This extension freezes new obligations before stage3 proof work and does not revise previous signed-reader expectations.

The original default Buf::copy_to_slice invokes actual try_copy_to_slice then unwrap_or_else(panic_advance). For every lawful input state s with view V and destination D of length n, n<=|V| must give total success with residual view drop(n,V) and destination exactly take(n,V), preserving destination length. No constraint on the first chunk size or initial destination values is allowed. If n>|V|, the checked callee returns Err{requested:n,available:actual remaining}, unchanged s/D, then the default wrapper takes modeled panic. This is not a Rust recoverable error returned by copy_to_slice; no unwinding-state theorem is implied. A generic wrapper proof may assume an explicitly stated exact checked-copy contract, but that contract must be discharged for the actual default loop or actual concrete instance before claiming grounded correctness. Do not substitute the already proved slice override for the generic wrapper body.

Stage3 may register a backend representation for the existing public bytes::TryGetError ONLY with its exact two fields requested:Usize and available:Usize. Every pair of usize values is admissible: do not add requested>available, requested>0, or any constructor invariant, since the original public fields admit arbitrary raw values. The representation is a pure two-field product; a bidirectional structural correspondence to the original extracted record must preserve both projections and record construction and have inverse roundtrips. Rust Result::Err wrapping this value remains an ordinary recoverable outcome, distinct from Aeneas execution failure. A model cannot erase either field, conflate different pairs, replace errors by unit, or assume formatting/Error/From behavior. If equality is exposed it must be precisely pairwise field equality, not an axiom asserting an API property. Layout/ABI or Rust diagnostic formatting are separate and unclaimed.

For widened Buf dictionaries, retain actual required try_copy_to_slice/copy_to_slice/reader operation types and exact state/writeback result shapes. New error-type registration must refer to the single correct source identity bytes::TryGetError; mappings and generated references must agree. Adding fields to a dictionary does not assert behavioral laws. Prove any projection/cross-prelude bridges by exact equality or explicit inverse structural maps, not by assuming the consuming function's desired result. Keep stage3 compiler/prelude pins separate from accepted core/numeric artifacts until complete regeneration and audits succeed.

The12 variable-width reader contracts previously frozen remain unchanged, including width0, width>8 precedence, exact consumption, checked shortage atomicity, endian dependence and the desired signed result. For checked signed methods, stage3 should prove actual signed64(zeroextended U) as a separately named implementation characterization and retain a formal counterexample to the desired S(n,U) contract when possible. It must not mark the desired short-width sign-extension contract successful. The original release remains unchanged; no publication or upstream fix is part of these proof obligations.

The original range helper contract remains exact normalization plus checked-add/ordering/end bounds, with valid empty ranges and both overflow boundaries. Any stage3 extraction must preserve original assertions/query dispatch; a hand-written range normalizer would only prove a replacement model.
