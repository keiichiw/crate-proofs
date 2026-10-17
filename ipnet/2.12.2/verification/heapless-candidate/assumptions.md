# Explicit external assumptions and trust ledger

Prospective ledger; each entry must be linked to actual theorem hypotheses or a
reviewed model before final acceptance. No custom Lean axioms. Application
Display/Serialize behavior itself must never be an assumption.

| Boundary | Required external law | Not implied |
| --- | --- | --- |
| core/std address Display | Default formatting yields specified address text, ASCII, byte length<=15/39; all stored addresses; callbacks terminate normally if writes succeed; no dynamic allocations in address formatting | General Formatter options, proof of std formatting internals |
| u8 decimal Display | Default text exact natural decimal; length<=2 for p<=32, <=3 for p<=128; ASCII; nonallocating | Arbitrary numeric formatting options |
| format_args/write/fmt::write | Literal/placeholder evaluation and argument order accurately compose actual ipnet Display callbacks; bounded write failures propagated; no hidden allocation | Permission to assume the ipnet callback emits desired text |
| heapless::String<N> | Empty inline buffer; append retains exact bytes/length, succeeds when total<=N, reports capacity error otherwise; as_str exact UTF-8 view; operations no dynamic allocation | Allocator behavior of arbitrary fmt::Display callbacks |
| serde Serializer | Exact method-call semantics/state/errors; readability stable true along human-readable path when so hypothesized; serialize_str observes supplied text within borrow lifetime | Success, no panic/divergence or no allocation for arbitrary serializer |
| conversion to str/borrows | String reference exposes exact current byte contents and valid lifetime; no text copy/allocation | Generic unsafe-layout correctness beyond reviewed dependency implementation |
| error/effect model | Exact ordinary serializer Err preserved; explicit distinction of external failure and internal formatting/unwrap failure; allocation trace labels distinguish ipnet temporaries from external serializer | Inference of allocation freedom from Result.ok alone |

Version-pin std/core, serde and heapless source for every reviewed external
correspondence. If using executable dependency abstractions, record functions,
input domains, representation and update/error laws and allocation labels.
Hypotheses must remain visible in final theorem statements or stated as named
assumption structures; an axiom-free audit does not discharge those hypotheses.

Native tests may validate selected strings, serializer errors and allocation
counts across feature combinations; they neither prove the external laws nor
universal candidate application correctness.
