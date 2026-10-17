# Independent corrected heapless serialization specification

Astra, 2026-10-16. Scope: a separately identified candidate correcting feature
selection in ipnet 2.12.2 serialization. This does not alter or retroactively
verify the downloaded release. Freeze candidate source diff/hash, feature set,
Rust/dependency pins and extraction configuration in the evidence.

## Intended correction and feature domain

Both concrete human-readable Serialize branches select their existing bounded
buffer path when `any(feature="heapless", feature="ser_as_str")`; the fallback
collect_str branch uses the complementary predicate. No other application
behavior is replaced by a model. `heapless` implies serde; legacy ser_as_str
alone does not. Required configurations, with std enabled and disabled where
buildable: heapless alone, serde+heapless, serde+ser_as_str, serde+both, and serde
without either flag as compatibility control. Legacy ser_as_str without serde
has no Serialize implementation and is compile-only, not a serialization claim.

## Independent output meaning

For all valid Ipv4Net/Ipv6Net values, including arbitrary host bits, define
text(n) = standard address Display of the STORED address ++ "/" ++ decimal
stored prefix. Prefix domains are 0..32 and 0..128. Tagged IpNet text delegates
to its payload without a V4/V6 label. Output must equal ordinary default-option
Display, not a normalized network address or Debug representation. This exact
text is ASCII/UTF-8; IPv4 address text has at most15 bytes, IPv6 at most39,
decimal prefix at most2/3 respectively, giving capacities18/43. IPv6 compressed
and IPv4-mapped address formatting must obey the same39-byte bound. No global
claim about user-selected format width/alignment/precision is intended.

The ipnet Display bodies are application code, not an allowed external axiom:
ipnet.rs Ipv4Net/Ivp6Net Display invokes write!("{}/{}",self.addr,self.prefix_len),
and IpNet Display matches the tag and delegates. Prove these exact compositions
against external address/u8 formatting laws and the formatting engine contract.
A source review alone must not be reported as a checked actual Display proof.

## Human-readable Serialize contract

Assume a serializer's is_human_readable observation is true for every queried
state along this call. (IpNet queries once then concrete serialization queries
again; a malicious/stateful serializer need not be stable without this explicit
hypothesis.) For each concrete type and tagged IpNet, bounded temporary buffer
creation and rendering succeed; no internal fmt::write unwrap can fail. The
single delegated serialize_str receives exactly text(n). The serializer result
is propagated EXACTLY: Ok(value) stays Ok(value), Err(error) stays Err(error).
Do not assume arbitrary serializers succeed. If external serializer work may
panic/diverge, preserve that external outcome or restrict it by an explicit
termination/no-panic hypothesis; do not claim internal capacity proves serializer
safety. Preserve original serializer state/effects as specified by its call law.

For human-readable IPNet, prove tag dispatch and the second readability query,
not just equality of final strings. Capacity/no-internal-failure claims apply
to buffer construction and ipnet formatting before invoking serialize_str.

## Allocation claim and non-human-readable behavior

The ipnet-owned temporary text construction uses only bounded inline storage,
stack/scalar operations and the stipulated nonallocating formatting callbacks;
its dynamic allocation event count is zero. Count excludes all serializer-owned
work, including is_human_readable and serialize_str, and excludes allocations
performed by a caller to consume/retain output. The serializer is free to allocate.
No blanket 'all serialization allocates zero' statement is permitted.

Non-human-readable concrete serialization remains actual serialize_tuple(5/17),
stored octets in network order followed by prefix, then end, propagating the first
external error. Tagged binary serialization uses serialize_newtype_variant
("IpNet",0,"V4",payload) or ("IpNet",1,"V6",payload). Feature correction must
leave these source paths unchanged. Unless these bodies are also conditionally
proved, classify them as reviewed unchanged/native compatibility evidence, not
proved by the human-readable theorem. Deserialize and schema behavior are outside
this scoped correction.

## Finish criteria

1. Independently specified mathematical byte lengths and18/43 capacity bounds
   kernel-check for every valid stored address/prefix under explicit external
   address-format assumptions.
2. Actual candidate ipnet Display and Serialize bodies refine this text/state/
   error behavior; no assumed ipnet callback correctness or hand-edited generated
   body. Extern-library obligations appear as explicit theorem hypotheses or
   separately listed reviewed standard-model correspondences, never custom axioms.
3. Zero internal allocation is proved only with an event/effect semantics or an
   explicitly reviewed structural allocation boundary. Plain Aeneas Result success
   cannot observe allocation; numeric capacity proof alone is insufficient.
4. Fresh reproducible extraction/build/axiom audit and feature-matrix evidence
   are recorded. Native allocation counters are supporting finite tests only.

If actual-body extraction remains blocked, deliver conditional mathematical and
model results with that limitation explicit; do not call the functionality fully
formally verified. These criteria concern corrected heapless serialization only,
not the entire crate.
