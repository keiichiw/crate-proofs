module
public import Proofs.SubnetMinimumMath
public import Proofs.IPv4SubnetActualTrace
public import Proofs.IPv6SubnetActualTrace

public section

namespace SubnetMinimumActual

/-- The actual IPv4 iterator admits a finite call trace whose output count is
minimal among all canonical CIDR covers with prefix at least the requested
minimum. `ActualTrace` records each extracted `next` call, including the
terminal `None`; this theorem does not assert that a Rust collection API ran. -/
theorem ipv4_actual_trace_minimum
    (r : IPv4SubnetActualTrace.State)
    (hq : r.min_prefix_len.val ≤ 32) :
    ∃ (ns : List IPv4SubnetActualTrace.Net)
      (rf : IPv4SubnetActualTrace.State),
      IPv4SubnetActualTrace.ActualTrace r ns rf ∧
      (∀ (cs : List (Nat × Nat)),
        (∀ c ∈ cs, SubnetMinimumMath.Candidate 32 r.min_prefix_len.val c) →
        (∀ x, RangeMath.mem (IPv4SubnetStep.remaining r) x ↔
          ∃ c ∈ cs, CidrModel.member 32 c.1 c.2 x) →
        ns.length ≤ cs.length) := by
  obtain ⟨ns, rf, bs, hactual, hobs, htrace, _, _⟩ :=
    IPv4SubnetActualTrace.actual_trace_exists r hq
  refine ⟨ns, rf, hactual, ?_⟩
  intro cs hvalid hcover
  have hmin := SubnetMinimumMath.ipv4_trace_minimum htrace hvalid hcover
  have hlen : ns.length = bs.length := by
    have := congrArg List.length hobs
    simpa using this
  simpa [hlen] using hmin

/-- The same actual-call minimality statement for IPv6, including full-width
Nat cardinalities and noncanonical initial endpoints. -/
theorem ipv6_actual_trace_minimum
    (r : IPv6SubnetActualTrace.State)
    (hq : r.min_prefix_len.val ≤ 128) :
    ∃ (ns : List IPv6SubnetActualTrace.Net)
      (rf : IPv6SubnetActualTrace.State),
      IPv6SubnetActualTrace.ActualTrace r ns rf ∧
      (∀ (cs : List (Nat × Nat)),
        (∀ c ∈ cs, SubnetMinimumMath.Candidate 128 r.min_prefix_len.val c) →
        (∀ x, RangeMath.mem (IPv6SubnetStep.remaining r) x ↔
          ∃ c ∈ cs, CidrModel.member 128 c.1 c.2 x) →
        ns.length ≤ cs.length) := by
  obtain ⟨ns, rf, bs, hactual, hobs, htrace, _, _⟩ :=
    IPv6SubnetActualTrace.actual_trace_exists r hq
  refine ⟨ns, rf, hactual, ?_⟩
  intro cs hvalid hcover
  have hmin := SubnetMinimumMath.ipv6_trace_minimum htrace hvalid hcover
  have hlen : ns.length = bs.length := by
    have := congrArg List.length hobs
    simpa using this
  simpa [hlen] using hmin

end SubnetMinimumActual
