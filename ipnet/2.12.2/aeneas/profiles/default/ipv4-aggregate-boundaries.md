# Independent minimal aggregate boundary contract

Astra oracle review, 2026-10-16. This is a proposed dependency contract, not
accepted aggregate verification. The source-level aggregate contract remains
exact input/output CIDR union with canonical ordered disjoint output, for all
valid possibly noncanonical IPv4 networks. Existing expert-contains-review.txt
§4.1 expressly permits normal successful sorting, permutation and sortedness
as a documented external trust boundary. It does not verify Rust's sort body.

## Concrete sorting boundary

Prefer a concrete slice of U32 pairs with the actual lexicographic comparator
(first numeric component, then second). An executable model may use a total
list sort, but must kernel-prove normal success, full List.Perm (including
multiplicities), lexicographic sortedness and unchanged length. This preserves
slice representation bounds. SortedByStart follows; sorting only by start is
an unnecessarily weaker correspondence when equal starts have unequal ends.
With this full order equal keys are identical pair values, so unstable equal-key
ordering does not change the modeled list. Rust/model correspondence remains
reviewed trusted, including any abstracted allocation behavior. Do not silently
extend this review to arbitrary Ord callbacks which can panic, mutate state,
or violate ordering laws. A generic registration must still retain and discharge
the exact concrete comparator condition at the selected application.

## last_mut: value and backward update

The pinned Rust slice source is `core/src/slice/mod.rs:306`: a direct pattern
match returns Some mutable reference to the last element or None. The narrow
extraction probe fails on lowered raw-pointer metadata, not on a demonstrated
ipnet algorithm failure. A small executable external slice model is acceptable
as a reviewed trusted boundary after checking its exact registered signature
and generated call/backward-use sites. It must expose both observations below.

Write the input slice list as xs, and the model result as normal `(o,back)`:

* If xs=[], then o=None, and back(None) has list [].
* If xs=prefix++[last], then o=Some(last), and for every replacement last',
  back(Some(last')) has exactly list prefix++[last'].

Length is unchanged; every earlier element is unchanged; replacing by the
original last recovers the input slice. For aggregate the element type is
U32×U32, so updating only current_end must also preserve the old pair's start.
The function must not return a value-only approximation or a backward closure
that ignores the update. The backward closure's syntactic Option domain includes
impossible Rust transitions None→Some and Some→None. Give the executable model
an explicit total definition for those cases, but do not claim Rust correspondence
there. Prove generated aggregate calls preserve the Option shape at every
backward invocation. A deterministic unchanged-slice fallback for impossible
shapes is permissible only with that reachable-call proof; it must not hide a
real reachable write or be used as an axiom.

## Iterator and Vec boundaries

First isolate actually executed methods from unused trait dictionary fields.
The parent narrow/tuple/chain probes demonstrate concrete extraction failures:
last_mut raw metadata, Iterator/Map try_fold signatures, and Ord min/max FnMut
or FnOnce method-item adapters. Broad inclusion produces unrelated defaults;
this is not evidence that each default executes in aggregate.

Smallest next path: retain successfully extracted map/tuple/is_empty wrappers;
register a reviewed last_mut lens and narrowly select sorting as above; probe
Map.next and the concrete collect/extend chain independently. If unused default
fields alone block clean generation, prefer sound metadata omission of genuinely
unused fields or exact existing baseline registrations. Do not hand-edit generated
Lean or silently replace a reachable fold callback.

Any Vec.extend fallback must execute the supplied iterator's actual next calls
(or an independently proved equivalent fold), append each Some exactly once,
stop on None, preserve existing elements, and propagate modeled failure/divergence.
It cannot simply append the subnet mathematical list without an actual-trace
refinement. Likewise initial interval collect needs the real map closure on
each input in order. Capacity/length representability and allocation abstraction
must be documented; unrestricted generic iterator termination cannot be assumed.
A concrete finite subnet trace supplies termination, not generic Extend typing.

## What remains an ipnet proof

Even after these reviewed boundaries, prove the actual merge loop's invariant:
processed input union equals merged union, output intervals are ordered and
nonempty, and all completed intervals are strictly separated. Show the actual
last_mut backward closure writes max(old_end,new_end), and push retains prior
intervals. Then connect actual subnet enumeration and actual extension to exact
union preservation and canonical output. Native tests and dependency extraction
success are not substitutes. The current probes justify targeted boundary work,
not a declaration that aggregate is already verified or inherently impossible.
