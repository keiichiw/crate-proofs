module
public import Proofs.IPv4SubnetTraceMath
public import Proofs.IPv4SubnetStep
public import Proofs.IPv4SubnetIterator

public section

open Aeneas Aeneas.Std Result

namespace IPv4SubnetActualTrace

abbrev State := ipnet.ipnet.Ipv4Subnets
abbrev Net := ipnet.ipnet.Ipv4Net

def nextCall (r : State) :=
  ipnet.ipnet.Ipv4Subnets.Insts.CoreIterTraitsIteratorIteratorIpv4Net.next r

def observe (n : Net) : Nat × Nat :=
  (CidrModel.ipv4Value n.addr, n.prefix_len.val)

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
  ∀ (r : State) (hq : r.min_prefix_len.val ≤ 32)
    (hse : CidrModel.ipv4Value r.start ≤ CidrModel.ipv4Value r.end),
    ∃ net r', nextCall r = Result.ok (some net, r') ∧
      CidrModel.ipv4Value net.addr = CidrModel.ipv4Value r.start ∧
      net.prefix_len.val =
        IPv4SubnetMath.bestPrefix (CidrModel.ipv4Value r.start)
          (CidrModel.ipv4Value r.end + 1) r.min_prefix_len.val hq (by omega) ∧
      IPv4SubnetStep.remaining r' =
        IPv4SubnetMath.residual (CidrModel.ipv4Value r.start)
          (CidrModel.ipv4Value r.end + 1) r.min_prefix_len.val hq (by omega) ∧
      r'.min_prefix_len = r.min_prefix_len

theorem transfer_of_law (hLive : LiveLaw)
    {q : Nat} {rem : RangeMath.HalfOpen} {bs : List (Nat × Nat)}
    (htrace : IPv4SubnetTraceMath.Trace q rem bs) :
    ∀ r : State, IPv4SubnetStep.remaining r = rem →
      r.min_prefix_len.val = q →
      ∃ ns rf, ActualTrace r ns rf ∧
        ns.map observe = bs ∧
        rf.min_prefix_len = r.min_prefix_len := by
  induction htrace with
  | empty =>
      intro r hrem hqeq
      have hend : CidrModel.ipv4Value r.end < CidrModel.ipv4Value r.start := by
        exact (RangeMath.ofInclusive_empty_iff _ _).1 (by simpa [IPv4SubnetStep.remaining] using hrem)
      have hdone := (IPv4SubnetStep.next_empty_spec r hend).1
      exact ⟨[], r, ActualTrace.done r hdone, rfl, rfl⟩
  | next s t hq hst rest hrest ih =>
      intro r hrem hqeq
      have hraw : CidrModel.ipv4Value r.start ≤ CidrModel.ipv4Value r.end ∧
          s = CidrModel.ipv4Value r.start ∧
          t = CidrModel.ipv4Value r.end + 1 := by
        exact (RangeMath.ofInclusive_live_iff _ _ s t).1 (by simpa [IPv4SubnetStep.remaining] using hrem)
      obtain ⟨hse, hs, ht⟩ := hraw
      have hq' : r.min_prefix_len.val ≤ 32 := by omega
      obtain ⟨net, r', hnext, haddr, hp, hres, hpres⟩ := hLive r hq' hse
      have hrem' : IPv4SubnetStep.remaining r' = IPv4SubnetMath.residual s t q hq hst := by
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
    IPv4SubnetTraceMath.Valid (IPv4SubnetStep.remaining r) := by
  have hstop := CidrModel.ipv4Value_bound r.end
  by_cases hse : CidrModel.ipv4Value r.start ≤ CidrModel.ipv4Value r.end
  · simp only [IPv4SubnetStep.remaining, RangeMath.ofInclusive, hse,
      ↓reduceIte, IPv4SubnetTraceMath.Valid]
    constructor
    · omega
    · simp only [RangeMath.limit]
      omega
  · simp [IPv4SubnetStep.remaining, RangeMath.ofInclusive, hse,
      IPv4SubnetTraceMath.Valid]

/-- Conditional refinement of the pure finite trace into exact calls of the
extracted iterator body. Once `next_live_spec` is checked, its theorem discharges
the only premise. -/
theorem actual_trace_exists_of_law (hLive : LiveLaw)
    (r : State) (hq : r.min_prefix_len.val ≤ 32) :
    ∃ (ns : List Net) (rf : State) (bs : List (Nat × Nat)),
      ActualTrace r ns rf ∧ ns.map observe = bs ∧
      IPv4SubnetTraceMath.Trace r.min_prefix_len.val
        (IPv4SubnetStep.remaining r) bs ∧
      ns.length ≤ RangeMath.size (IPv4SubnetStep.remaining r) ∧
      rf.min_prefix_len = r.min_prefix_len := by
  obtain ⟨bs, htrace, hlen⟩ :=
    IPv4SubnetTraceMath.trace_exists r.min_prefix_len.val hq
      (IPv4SubnetStep.remaining r) (remaining_valid r)
  obtain ⟨ns, rf, hactual, hobs, hprefix⟩ :=
    transfer_of_law hLive htrace r rfl rfl
  refine ⟨ns, rf, bs, hactual, hobs, htrace, ?_, hprefix⟩
  simpa [← hobs] using hlen

theorem actual_trace_properties_of_law (hLive : LiveLaw)
    (r : State) (hq : r.min_prefix_len.val ≤ 32) :
    ∃ (ns : List Net) (rf : State),
      ActualTrace r ns rf ∧
      ns.length ≤ RangeMath.size (IPv4SubnetStep.remaining r) ∧
      (∀ x, RangeMath.mem (IPv4SubnetStep.remaining r) x ↔
        ∃ n ∈ ns, IPv4SubnetTraceMath.blockMem (observe n) x) ∧
      (ns.map observe).Pairwise
        (fun a b => CidrModel.upper 32 a.1 a.2 + 1 ≤ b.1) ∧
      (ns.map observe).Pairwise
        (fun a b => ∀ x, ¬ (IPv4SubnetTraceMath.blockMem a x ∧
          IPv4SubnetTraceMath.blockMem b x)) ∧
      rf.min_prefix_len = r.min_prefix_len := by
  obtain ⟨ns, rf, bs, hactual, hobs, htrace, hlen, hprefix⟩ :=
    actual_trace_exists_of_law hLive r hq
  refine ⟨ns, rf, hactual, hlen, ?_, ?_, ?_, hprefix⟩
  · intro x
    rw [IPv4SubnetTraceMath.trace_partition htrace x, ← hobs]
    simp only [List.mem_map]
    constructor
    · rintro ⟨b, ⟨n, hn, rfl⟩, hb⟩
      exact ⟨n, hn, hb⟩
    · rintro ⟨n, hn, hb⟩
      exact ⟨observe n, ⟨n, hn, rfl⟩, hb⟩
  · rw [hobs]
    exact IPv4SubnetTraceMath.trace_ordered htrace
  · rw [hobs]
    exact IPv4SubnetTraceMath.trace_pairwise_disjoint htrace

theorem actual_trace_canonical_of_law (hLive : LiveLaw)
    (r : State) (hq : r.min_prefix_len.val ≤ 32) :
    ∃ (ns : List Net) (rf : State),
      ActualTrace r ns rf ∧
      ∀ n ∈ ns,
        r.min_prefix_len.val ≤ n.prefix_len.val ∧
        n.prefix_len.val ≤ 32 ∧
        CidrModel.lower 32 (CidrModel.ipv4Value n.addr)
          n.prefix_len.val = CidrModel.ipv4Value n.addr := by
  obtain ⟨ns, rf, bs, hactual, hobs, htrace, _, _⟩ :=
    actual_trace_exists_of_law hLive r hq
  refine ⟨ns, rf, hactual, ?_⟩
  intro n hn
  have hmem : observe n ∈ bs := by
    rw [← hobs]
    exact List.mem_map.mpr ⟨n, hn, rfl⟩
  simpa [observe] using IPv4SubnetTraceMath.trace_canonical htrace (observe n) hmem

/-- For a valid, possibly noncanonical network, the actual constructor result
has exactly the fixed-prefix mathematical trace when the live-body law holds. -/
theorem constructor_fixed_trace_of_law (hLive : LiveLaw)
    (n : Net) (q : U8)
    (hp : n.prefix_len.val ≤ 32)
    (hpq : n.prefix_len.val ≤ q.val) (hq : q.val ≤ 32) :
    ∃ (r : State) (ns : List Net) (rf : State),
      ipnet.ipnet.Ipv4Net.subnets n q = Result.ok (.Ok r) ∧
      ActualTrace r ns rf ∧
      ns.map observe = IPv4SubnetTraceMath.fixedBlocks
        (CidrModel.lower 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val)
        q.val (2 ^ (q.val - n.prefix_len.val)) ∧
      ns.length = 2 ^ (q.val - n.prefix_len.val) ∧
      (∀ i, (ns.map observe)[i]? =
        if i < 2 ^ (q.val - n.prefix_len.val) then
          some (CidrModel.lower 32 (CidrModel.ipv4Value n.addr)
            n.prefix_len.val + i * 2 ^ (32 - q.val), q.val)
        else none) ∧
      rf.min_prefix_len = q := by
  obtain ⟨out, hcall, hspec⟩ := IPv4NetOps.subnets_spec n q hp
  have hgood : ¬ (q.val < n.prefix_len.val ∨ 32 < q.val) := by omega
  simp only [hgood, ↓reduceIte] at hspec
  obtain ⟨r, hout, hstart, hstop, hqstate⟩ := hspec
  rw [hout] at hcall
  let a := CidrModel.ipv4Value n.addr
  let p := n.prefix_len.val
  let lo := CidrModel.lower 32 a p
  let hi := CidrModel.upper 32 a p
  have hlohi : lo ≤ hi := CidrModel.lower_le_upper 32 a p
  have hrem : IPv4SubnetStep.remaining r = .live lo (hi + 1) := by
    simp [IPv4SubnetStep.remaining, RangeMath.ofInclusive, hstart,
      hstop, hlohi, lo, hi, a, p]
  have htrace : IPv4SubnetTraceMath.Trace q.val (.live lo (hi+1))
      (IPv4SubnetTraceMath.fixedBlocks lo q.val (2 ^ (q.val-p))) :=
    IPv4SubnetTraceMath.network_origin_fixed_trace a p q.val hpq hq
  obtain ⟨ns, rf, hactual, hobs, hfinal⟩ :=
    transfer_of_law hLive htrace r hrem (by rw [hqstate])
  refine ⟨r, ns, rf, hcall, hactual, hobs, ?_, ?_, ?_⟩
  · have hlen := congrArg List.length hobs
    simpa [IPv4SubnetTraceMath.fixed_blocks_length] using hlen
  · intro i
    rw [hobs]
    exact IPv4SubnetTraceMath.fixed_blocks_get_opt lo q.val
      (2 ^ (q.val-p)) i
  · rw [hfinal, hqstate]

/-- The premise used for finite-trace composition is discharged by the
kernel-checked theorem about the actual extracted iterator body. -/
theorem liveLaw_checked : LiveLaw := by
  intro r hq hse
  simpa only [nextCall] using IPv4SubnetStep.next_live_spec r hq hse

theorem actual_trace_exists (r : State)
    (hq : r.min_prefix_len.val ≤ 32) :
    ∃ (ns : List Net) (rf : State) (bs : List (Nat × Nat)),
      ActualTrace r ns rf ∧ ns.map observe = bs ∧
      IPv4SubnetTraceMath.Trace r.min_prefix_len.val
        (IPv4SubnetStep.remaining r) bs ∧
      ns.length ≤ RangeMath.size (IPv4SubnetStep.remaining r) ∧
      rf.min_prefix_len = r.min_prefix_len :=
  actual_trace_exists_of_law liveLaw_checked r hq

theorem actual_trace_properties (r : State)
    (hq : r.min_prefix_len.val ≤ 32) :
    ∃ (ns : List Net) (rf : State),
      ActualTrace r ns rf ∧
      ns.length ≤ RangeMath.size (IPv4SubnetStep.remaining r) ∧
      (∀ x, RangeMath.mem (IPv4SubnetStep.remaining r) x ↔
        ∃ n ∈ ns, IPv4SubnetTraceMath.blockMem (observe n) x) ∧
      (ns.map observe).Pairwise
        (fun a b => CidrModel.upper 32 a.1 a.2 + 1 ≤ b.1) ∧
      (ns.map observe).Pairwise
        (fun a b => ∀ x, ¬ (IPv4SubnetTraceMath.blockMem a x ∧
          IPv4SubnetTraceMath.blockMem b x)) ∧
      rf.min_prefix_len = r.min_prefix_len :=
  actual_trace_properties_of_law liveLaw_checked r hq

theorem actual_trace_canonical (r : State)
    (hq : r.min_prefix_len.val ≤ 32) :
    ∃ (ns : List Net) (rf : State),
      ActualTrace r ns rf ∧
      ∀ n ∈ ns,
        r.min_prefix_len.val ≤ n.prefix_len.val ∧
        n.prefix_len.val ≤ 32 ∧
        CidrModel.lower 32 (CidrModel.ipv4Value n.addr)
          n.prefix_len.val = CidrModel.ipv4Value n.addr :=
  actual_trace_canonical_of_law liveLaw_checked r hq

theorem constructor_fixed_trace
    (n : Net) (q : U8)
    (hp : n.prefix_len.val ≤ 32)
    (hpq : n.prefix_len.val ≤ q.val) (hq : q.val ≤ 32) :
    ∃ (r : State) (ns : List Net) (rf : State),
      ipnet.ipnet.Ipv4Net.subnets n q = Result.ok (.Ok r) ∧
      ActualTrace r ns rf ∧
      ns.map observe = IPv4SubnetTraceMath.fixedBlocks
        (CidrModel.lower 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val)
        q.val (2 ^ (q.val - n.prefix_len.val)) ∧
      ns.length = 2 ^ (q.val - n.prefix_len.val) ∧
      (∀ i, (ns.map observe)[i]? =
        if i < 2 ^ (q.val - n.prefix_len.val) then
          some (CidrModel.lower 32 (CidrModel.ipv4Value n.addr)
            n.prefix_len.val + i * 2 ^ (32 - q.val), q.val)
        else none) ∧
      rf.min_prefix_len = q :=
  constructor_fixed_trace_of_law liveLaw_checked n q hp hpq hq

end IPv4SubnetActualTrace
