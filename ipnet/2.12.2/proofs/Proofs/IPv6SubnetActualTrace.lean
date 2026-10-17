module
public import Proofs.IPv6SubnetTraceMath
public import Proofs.IPv6SubnetStep
public import Proofs.IPv6SubnetIterator
public import Proofs.IPv6NetOps

public section

open Aeneas Aeneas.Std Result

namespace IPv6SubnetActualTrace

abbrev State := ipnet.ipnet.Ipv6Subnets
abbrev Net := ipnet.ipnet.Ipv6Net

def nextCall (r : State) :=
  ipnet.ipnet.Ipv6Subnets.Insts.CoreIterTraitsIteratorIteratorIpv6Net.next r

def observe (n : Net) : Nat × Nat :=
  (CidrModel.ipv6Value n.addr, n.prefix_len.val)

/-- A logical list witnesses consecutive calls to the actual extracted `next`
and includes the final `None` call. It says nothing about runtime collection. -/
inductive ActualTrace : State → List Net → State → Prop
  | done (r : State) (hnext : nextCall r = Result.ok (none, r)) :
      ActualTrace r [] r
  | cons (r r' rf : State) (n : Net) (ns : List Net)
      (hnext : nextCall r = Result.ok (some n, r'))
      (hrest : ActualTrace r' ns rf) :
      ActualTrace r (n :: ns) rf

theorem actual_trace_terminal {r rf : State} {ns : List Net}
    (h : ActualTrace r ns rf) :
    nextCall rf = Result.ok (none, rf) := by
  induction h with
  | done _ hnext => exact hnext
  | cons _ _ _ _ _ _ _ ih => exact ih

/-- The live-state property expected from the separately proved actual body. -/
def LiveLaw : Prop :=
  ∀ (r : State) (hq : r.min_prefix_len.val ≤ 128)
    (hse : CidrModel.ipv6Value r.start ≤ CidrModel.ipv6Value r.end),
    ∃ net r', nextCall r = Result.ok (some net, r') ∧
      CidrModel.ipv6Value net.addr = CidrModel.ipv6Value r.start ∧
      net.prefix_len.val =
        IPv6SubnetMath.bestPrefix (CidrModel.ipv6Value r.start)
          (CidrModel.ipv6Value r.end + 1) r.min_prefix_len.val hq (by omega) ∧
      IPv6SubnetStep.remaining r' =
        IPv6SubnetMath.residual (CidrModel.ipv6Value r.start)
          (CidrModel.ipv6Value r.end + 1) r.min_prefix_len.val hq (by omega) ∧
      r'.min_prefix_len = r.min_prefix_len

theorem transfer_of_law (hLive : LiveLaw)
    {q : Nat} {rem : RangeMath.HalfOpen} {bs : List (Nat × Nat)}
    (htrace : IPv6SubnetTraceMath.Trace q rem bs) :
    ∀ r : State, IPv6SubnetStep.remaining r = rem →
      r.min_prefix_len.val = q →
      ∃ ns rf, ActualTrace r ns rf ∧
        ns.map observe = bs ∧
        rf.min_prefix_len = r.min_prefix_len := by
  induction htrace with
  | empty =>
      intro r hrem hqeq
      have hend : CidrModel.ipv6Value r.end < CidrModel.ipv6Value r.start := by
        exact (RangeMath.ofInclusive_empty_iff _ _).1 (by simpa [IPv6SubnetStep.remaining] using hrem)
      have hdone := (IPv6SubnetStep.next_empty_spec r hend).1
      exact ⟨[], r, ActualTrace.done r hdone, rfl, rfl⟩
  | next s t hq hst rest hrest ih =>
      intro r hrem hqeq
      have hraw : CidrModel.ipv6Value r.start ≤ CidrModel.ipv6Value r.end ∧
          s = CidrModel.ipv6Value r.start ∧
          t = CidrModel.ipv6Value r.end + 1 := by
        exact (RangeMath.ofInclusive_live_iff _ _ s t).1 (by simpa [IPv6SubnetStep.remaining] using hrem)
      obtain ⟨hse, hs, ht⟩ := hraw
      have hq' : r.min_prefix_len.val ≤ 128 := by omega
      obtain ⟨net, r', hnext, haddr, hp, hres, hpres⟩ := hLive r hq' hse
      have hrem' : IPv6SubnetStep.remaining r' = IPv6SubnetMath.residual s t q hq hst := by
        simpa [hs, ht, hqeq] using hres
      have hqeq' : r'.min_prefix_len.val = q := by rw [hpres, hqeq]
      obtain ⟨ns, rf, hactual, hobs, hfinal⟩ := ih r' hrem' hqeq'
      refine ⟨net :: ns, rf, ActualTrace.cons r r' rf net ns hnext hactual, ?_, ?_⟩
      · simp only [List.map_cons, hobs, observe]
        exact congrArg (fun b => b :: rest)
          (congrArg₂ (fun a b => (a, b)) (haddr.trans hs.symm)
            (by simpa [hs, ht, hqeq] using hp))
      · rw [hfinal, hpres]

theorem remaining_valid (r : State) :
    IPv6SubnetTraceMath.Valid (IPv6SubnetStep.remaining r) := by
  have hstop := CidrModel.ipv6Value_bound r.end
  by_cases hse : CidrModel.ipv6Value r.start ≤ CidrModel.ipv6Value r.end
  · simp only [IPv6SubnetStep.remaining, RangeMath.ofInclusive, hse,
      ↓reduceIte, IPv6SubnetTraceMath.Valid]
    constructor
    · omega
    · simp only [IPv6RangeMath.limit]
      omega
  · simp [IPv6SubnetStep.remaining, RangeMath.ofInclusive, hse,
      IPv6SubnetTraceMath.Valid]

/-- Conditional refinement of the pure finite trace into exact calls of the
extracted iterator body. Once `next_live_spec` is checked, its theorem discharges
the only premise. -/
theorem actual_trace_exists_of_law (hLive : LiveLaw)
    (r : State) (hq : r.min_prefix_len.val ≤ 128) :
    ∃ (ns : List Net) (rf : State) (bs : List (Nat × Nat)),
      ActualTrace r ns rf ∧ ns.map observe = bs ∧
      IPv6SubnetTraceMath.Trace r.min_prefix_len.val
        (IPv6SubnetStep.remaining r) bs ∧
      ns.length ≤ RangeMath.size (IPv6SubnetStep.remaining r) ∧
      rf.min_prefix_len = r.min_prefix_len := by
  obtain ⟨bs, htrace, hlen⟩ :=
    IPv6SubnetTraceMath.trace_exists r.min_prefix_len.val hq
      (IPv6SubnetStep.remaining r) (remaining_valid r)
  obtain ⟨ns, rf, hactual, hobs, hprefix⟩ :=
    transfer_of_law hLive htrace r rfl rfl
  refine ⟨ns, rf, bs, hactual, hobs, htrace, ?_, hprefix⟩
  simpa [← hobs] using hlen

theorem actual_trace_properties_of_law (hLive : LiveLaw)
    (r : State) (hq : r.min_prefix_len.val ≤ 128) :
    ∃ (ns : List Net) (rf : State),
      ActualTrace r ns rf ∧
      ns.length ≤ RangeMath.size (IPv6SubnetStep.remaining r) ∧
      (∀ x, RangeMath.mem (IPv6SubnetStep.remaining r) x ↔
        ∃ n ∈ ns, IPv6SubnetTraceMath.blockMem (observe n) x) ∧
      (ns.map observe).Pairwise
        (fun a b => CidrModel.upper 128 a.1 a.2 + 1 ≤ b.1) ∧
      (ns.map observe).Pairwise
        (fun a b => ∀ x, ¬ (IPv6SubnetTraceMath.blockMem a x ∧
          IPv6SubnetTraceMath.blockMem b x)) ∧
      rf.min_prefix_len = r.min_prefix_len := by
  obtain ⟨ns, rf, bs, hactual, hobs, htrace, hlen, hprefix⟩ :=
    actual_trace_exists_of_law hLive r hq
  refine ⟨ns, rf, hactual, hlen, ?_, ?_, ?_, hprefix⟩
  · intro x
    rw [IPv6SubnetTraceMath.trace_partition htrace x, ← hobs]
    simp only [List.mem_map]
    constructor
    · rintro ⟨b, ⟨n, hn, rfl⟩, hb⟩
      exact ⟨n, hn, hb⟩
    · rintro ⟨n, hn, hb⟩
      exact ⟨observe n, ⟨n, hn, rfl⟩, hb⟩
  · rw [hobs]
    exact IPv6SubnetTraceMath.trace_ordered htrace
  · rw [hobs]
    exact IPv6SubnetTraceMath.trace_pairwise_disjoint htrace

theorem actual_trace_canonical_of_law (hLive : LiveLaw)
    (r : State) (hq : r.min_prefix_len.val ≤ 128) :
    ∃ (ns : List Net) (rf : State),
      ActualTrace r ns rf ∧
      ∀ n ∈ ns,
        r.min_prefix_len.val ≤ n.prefix_len.val ∧
        n.prefix_len.val ≤ 128 ∧
        CidrModel.lower 128 (CidrModel.ipv6Value n.addr)
          n.prefix_len.val = CidrModel.ipv6Value n.addr := by
  obtain ⟨ns, rf, bs, hactual, hobs, htrace, _, _⟩ :=
    actual_trace_exists_of_law hLive r hq
  refine ⟨ns, rf, hactual, ?_⟩
  intro n hn
  have hmem : observe n ∈ bs := by
    rw [← hobs]
    exact List.mem_map.mpr ⟨n, hn, rfl⟩
  simpa [observe] using IPv6SubnetTraceMath.trace_canonical htrace (observe n) hmem

/-- For a valid, possibly noncanonical network, the actual constructor result
has exactly the fixed-prefix mathematical trace when the live-body law holds. -/
theorem constructor_fixed_trace_of_law (hLive : LiveLaw)
    (n : Net) (q : U8)
    (hp : n.prefix_len.val ≤ 128)
    (hpq : n.prefix_len.val ≤ q.val) (hq : q.val ≤ 128) :
    ∃ (r : State) (ns : List Net) (rf : State),
      ipnet.ipnet.Ipv6Net.subnets n q = Result.ok (.Ok r) ∧
      ActualTrace r ns rf ∧
      ns.map observe = IPv6SubnetTraceMath.fixedBlocks
        (CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val)
        q.val (2 ^ (q.val - n.prefix_len.val)) ∧
      ns.length = 2 ^ (q.val - n.prefix_len.val) ∧
      (∀ i, (ns.map observe)[i]? =
        if i < 2 ^ (q.val - n.prefix_len.val) then
          some (CidrModel.lower 128 (CidrModel.ipv6Value n.addr)
            n.prefix_len.val + i * 2 ^ (128 - q.val), q.val)
        else none) ∧
      rf.min_prefix_len = q := by
  obtain ⟨out, hcall, hspec⟩ := IPv6NetOps.subnets_spec n q hp
  have hgood : ¬ (q.val < n.prefix_len.val ∨ 128 < q.val) := by omega
  simp only [hgood, ↓reduceIte] at hspec
  obtain ⟨r, hout, hstart, hstop, hqstate⟩ := hspec
  rw [hout] at hcall
  let a := CidrModel.ipv6Value n.addr
  let p := n.prefix_len.val
  let lo := CidrModel.lower 128 a p
  let hi := CidrModel.upper 128 a p
  have hlohi : lo ≤ hi := CidrModel.lower_le_upper 128 a p
  have hrem : IPv6SubnetStep.remaining r = .live lo (hi + 1) := by
    simp [IPv6SubnetStep.remaining, RangeMath.ofInclusive, hstart,
      hstop, hlohi, lo, hi, a, p]
  have htrace : IPv6SubnetTraceMath.Trace q.val (.live lo (hi+1))
      (IPv6SubnetTraceMath.fixedBlocks lo q.val (2 ^ (q.val-p))) :=
    IPv6SubnetTraceMath.network_origin_fixed_trace a p q.val hpq hq
  obtain ⟨ns, rf, hactual, hobs, hfinal⟩ :=
    transfer_of_law hLive htrace r hrem (by rw [hqstate])
  refine ⟨r, ns, rf, hcall, hactual, hobs, ?_, ?_, ?_⟩
  · have hlen := congrArg List.length hobs
    simpa [IPv6SubnetTraceMath.fixed_blocks_length] using hlen
  · intro i
    rw [hobs]
    exact IPv6SubnetTraceMath.fixed_blocks_get_opt lo q.val
      (2 ^ (q.val-p)) i
  · rw [hfinal, hqstate]

/-- The premise used for finite-trace composition is discharged by the
kernel-checked theorem about the actual extracted iterator body. -/
theorem liveLaw_checked : LiveLaw := by
  intro r hq hse
  simpa only [nextCall] using IPv6SubnetStep.next_live_spec r hq hse

theorem actual_trace_exists (r : State)
    (hq : r.min_prefix_len.val ≤ 128) :
    ∃ (ns : List Net) (rf : State) (bs : List (Nat × Nat)),
      ActualTrace r ns rf ∧ ns.map observe = bs ∧
      IPv6SubnetTraceMath.Trace r.min_prefix_len.val
        (IPv6SubnetStep.remaining r) bs ∧
      ns.length ≤ RangeMath.size (IPv6SubnetStep.remaining r) ∧
      rf.min_prefix_len = r.min_prefix_len :=
  actual_trace_exists_of_law liveLaw_checked r hq

theorem actual_trace_properties (r : State)
    (hq : r.min_prefix_len.val ≤ 128) :
    ∃ (ns : List Net) (rf : State),
      ActualTrace r ns rf ∧
      ns.length ≤ RangeMath.size (IPv6SubnetStep.remaining r) ∧
      (∀ x, RangeMath.mem (IPv6SubnetStep.remaining r) x ↔
        ∃ n ∈ ns, IPv6SubnetTraceMath.blockMem (observe n) x) ∧
      (ns.map observe).Pairwise
        (fun a b => CidrModel.upper 128 a.1 a.2 + 1 ≤ b.1) ∧
      (ns.map observe).Pairwise
        (fun a b => ∀ x, ¬ (IPv6SubnetTraceMath.blockMem a x ∧
          IPv6SubnetTraceMath.blockMem b x)) ∧
      rf.min_prefix_len = r.min_prefix_len :=
  actual_trace_properties_of_law liveLaw_checked r hq

theorem actual_trace_canonical (r : State)
    (hq : r.min_prefix_len.val ≤ 128) :
    ∃ (ns : List Net) (rf : State),
      ActualTrace r ns rf ∧
      ∀ n ∈ ns,
        r.min_prefix_len.val ≤ n.prefix_len.val ∧
        n.prefix_len.val ≤ 128 ∧
        CidrModel.lower 128 (CidrModel.ipv6Value n.addr)
          n.prefix_len.val = CidrModel.ipv6Value n.addr :=
  actual_trace_canonical_of_law liveLaw_checked r hq

theorem constructor_fixed_trace
    (n : Net) (q : U8)
    (hp : n.prefix_len.val ≤ 128)
    (hpq : n.prefix_len.val ≤ q.val) (hq : q.val ≤ 128) :
    ∃ (r : State) (ns : List Net) (rf : State),
      ipnet.ipnet.Ipv6Net.subnets n q = Result.ok (.Ok r) ∧
      ActualTrace r ns rf ∧
      ns.map observe = IPv6SubnetTraceMath.fixedBlocks
        (CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val)
        q.val (2 ^ (q.val - n.prefix_len.val)) ∧
      ns.length = 2 ^ (q.val - n.prefix_len.val) ∧
      (∀ i, (ns.map observe)[i]? =
        if i < 2 ^ (q.val - n.prefix_len.val) then
          some (CidrModel.lower 128 (CidrModel.ipv6Value n.addr)
            n.prefix_len.val + i * 2 ^ (128 - q.val), q.val)
        else none) ∧
      rf.min_prefix_len = q :=
  constructor_fixed_trace_of_law liveLaw_checked n q hp hpq hq

end IPv6SubnetActualTrace
