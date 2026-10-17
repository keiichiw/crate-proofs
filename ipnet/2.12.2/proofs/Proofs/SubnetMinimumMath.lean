module
public import Proofs.IPv4SubnetTraceMath
public import Proofs.IPv6SubnetTraceMath

public section

namespace SubnetMinimumMath

theorem aligned_no_cross (L a u : Nat) (hL : 0 < L)
    (ha : L ∣ a) (hu : L ∣ u) (hau : a < u) : a + L ≤ u := by
  rcases ha with ⟨i, rfl⟩
  rcases hu with ⟨j, rfl⟩
  have hij : i < j := by
    exact (Nat.mul_lt_mul_right hL).mp (by simpa [Nat.mul_comm] using hau)
  have hsucc : i + 1 ≤ j := by omega
  have hmul := Nat.mul_le_mul_right L hsucc
  nlinarith [hmul]

def eligible (w s t q p : Nat) : Prop :=
  q ≤ p ∧ p ≤ w ∧ s % 2 ^ (w - p) = 0 ∧ s + 2 ^ (w - p) ≤ t

/-- No canonical eligible competitor block can cross the next greedy boundary. -/
theorem greedy_boundary_no_cross
    (w s t q g a p : Nat) (_hq : q ≤ w) (hg : eligible w s t q g)
    (hbest : ∀ p, eligible w s t q p → g ≤ p)
    (hcp : q ≤ p) (hpw : p ≤ w)
    (ha : a % 2 ^ (w - p) = 0) (hs_le_a : s ≤ a)
    (hfit : a + 2 ^ (w - p) ≤ t)
    (hleft : a < s + 2 ^ (w - g))
    (hright : s + 2 ^ (w - g) < a + 2 ^ (w - p)) : False := by
  let K := 2 ^ (w - g)
  let L := 2 ^ (w - p)
  have hKpos : 0 < K := by simp [K]
  have hLpos : 0 < L := by simp [L]
  have hsalign : K ∣ s := Nat.dvd_of_mod_eq_zero hg.2.2.1
  have halign : L ∣ a := Nat.dvd_of_mod_eq_zero ha
  by_cases hgp : g ≤ p
  · have hdiv : L ∣ K := Nat.pow_dvd_pow 2 (by omega)
    have hsL : L ∣ s := dvd_trans hdiv hsalign
    have huL : L ∣ s + K := dvd_add hsL hdiv
    have hbound := aligned_no_cross L a (s + K) hLpos halign huL hleft
    omega
  · have hdiv : K ∣ L := Nat.pow_dvd_pow 2 (by omega)
    have haK : K ∣ a := dvd_trans hdiv halign
    have hsa : s = a := by
      by_contra hne
      have hlt : s < a := by omega
      have hbound := aligned_no_cross K s a hKpos hsalign haK hlt
      omega
    have he : eligible w s t q p := by
      refine ⟨hcp, hpw, ?_, ?_⟩
      · simpa [hsa] using ha
      · simpa [hsa] using hfit
    exact hgp (hbest p he)

def blockMem (w : Nat) (b : Nat × Nat) (x : Nat) : Prop :=
  CidrModel.member w b.1 b.2 x

def Candidate (w q : Nat) (b : Nat × Nat) : Prop :=
  q ≤ b.2 ∧ b.2 ≤ w ∧ b.1 < 2 ^ w ∧
    CidrModel.lower w b.1 b.2 = b.1

theorem candidate_interval (w q : Nat) (b : Nat × Nat)
    (hb : Candidate w q b) (x : Nat) :
    blockMem w b x ↔ b.1 ≤ x ∧ x < b.1 + 2 ^ (w - b.2) := by
  obtain ⟨_, _, _, hlo⟩ := hb
  simp only [blockMem, CidrModel.member, CidrModel.upper_eq,
    CidrModel.size, hlo]
  have hpos : 0 < 2 ^ (w - b.2) := by positivity
  omega

def residual (w s t g : Nat) : RangeMath.HalfOpen :=
  if s + 2 ^ (w - g) < t then .live (s + 2 ^ (w - g)) t else .empty

inductive Trace (w q : Nat) : RangeMath.HalfOpen → List (Nat × Nat) → Prop
  | empty : Trace w q .empty []
  | next (s t g : Nat) (hst : s < t)
      (hg : eligible w s t q g)
      (hbest : ∀ p, eligible w s t q p → g ≤ p)
      (bs : List (Nat × Nat))
      (hrest : Trace w q (residual w s t g) bs) :
      Trace w q (.live s t) ((s,g)::bs)

theorem candidate_inside_of_cover (w q s t : Nat)
    (cs : List (Nat × Nat))
    (hcover : ∀ x, RangeMath.mem (.live s t) x ↔
      ∃ c ∈ cs, blockMem w c x)
    (c : Nat × Nat) (hc : c ∈ cs) (hvalid : Candidate w q c) :
    s ≤ c.1 ∧ c.1 + 2 ^ (w - c.2) ≤ t := by
  let L := 2 ^ (w - c.2)
  have hL : 0 < L := by simp [L]
  have hstartMem : blockMem w c c.1 :=
    (candidate_interval w q c hvalid c.1).2 (by omega)
  have hendMem : blockMem w c (c.1 + L - 1) :=
    (candidate_interval w q c hvalid (c.1 + L - 1)).2 (by
      dsimp [L]
      omega)
  have hs := (hcover c.1).2 ⟨c, hc, hstartMem⟩
  have ht := (hcover (c.1 + L - 1)).2 ⟨c, hc, hendMem⟩
  simp only [RangeMath.mem] at hs ht
  omega

theorem trace_minimum {w q : Nat} {r : RangeMath.HalfOpen}
    {bs cs : List (Nat × Nat)} (htrace : Trace w q r bs)
    (hvalid : ∀ c ∈ cs, Candidate w q c)
    (hcover : ∀ x, RangeMath.mem r x ↔
      ∃ c ∈ cs, blockMem w c x) :
    bs.length ≤ cs.length := by
  induction htrace generalizing cs with
  | empty => simp
  | next s t g hst hg hbest bs hrest ih =>
      let K := 2 ^ (w - g)
      let u := s + K
      let right := cs.filter (fun c => decide (u ≤ c.1))
      have hu : u ≤ t := hg.2.2.2
      have hKpos : 0 < K := by simp [K]
      have hright_valid : ∀ c ∈ right, Candidate w q c := by
        intro c hc
        exact hvalid c ((List.mem_filter.mp hc).1)
      have hright_cover : ∀ x, RangeMath.mem (residual w s t g) x ↔
          ∃ c ∈ right, blockMem w c x := by
        intro x
        constructor
        · intro hx
          have hxorig : RangeMath.mem (.live s t) x := by
            simp only [residual] at hx
            split at hx
            · change u ≤ x ∧ x < t at hx
              exact ⟨by omega, hx.2⟩
            · simp [RangeMath.mem] at hx
          obtain ⟨c, hc, hcm⟩ := (hcover x).1 hxorig
          have hcb := candidate_inside_of_cover w q s t cs hcover c hc (hvalid c hc)
          have hcx := (candidate_interval w q c (hvalid c hc) x).1 hcm
          have hux : u ≤ x := by
            simp only [residual] at hx
            split at hx
            · exact hx.1
            · simp [RangeMath.mem] at hx
          have hcu : u ≤ c.1 := by
            by_contra hnot
            have hleft : c.1 < u := by omega
            have hcross : u < c.1 + 2 ^ (w - c.2) := by omega
            exact greedy_boundary_no_cross w s t q g c.1 c.2
              (Nat.le_trans hg.1 hg.2.1) hg hbest
              (hvalid c hc).1 (hvalid c hc).2.1
              (by
                have hcanon := (hvalid c hc).2.2.2
                change (c.1 / 2 ^ (w - c.2)) * 2 ^ (w - c.2) = c.1 at hcanon
                have hmod := Nat.mod_add_div c.1 (2 ^ (w - c.2))
                have hcanon' : 2 ^ (w - c.2) *
                    (c.1 / 2 ^ (w - c.2)) = c.1 := by
                  simpa [Nat.mul_comm] using hcanon
                omega)
              hcb.1 hcb.2 hleft hcross
          exact ⟨c, List.mem_filter.mpr ⟨hc, by simp [hcu]⟩, hcm⟩
        · rintro ⟨c, hc, hcm⟩
          have hc0 := (List.mem_filter.mp hc).2
          have hcU : u ≤ c.1 := by simpa using hc0
          have hxorig := (hcover x).2 ⟨c, (List.mem_filter.mp hc).1, hcm⟩
          change s ≤ x ∧ x < t at hxorig
          have hcx := (candidate_interval w q c
            (hvalid c (List.mem_filter.mp hc).1) x).1 hcm
          have hmore : u < t := by
            have : x < t := hxorig.2
            omega
          simpa [residual, u, K, hmore, RangeMath.mem] using
            (show u ≤ x ∧ x < t by omega)
      have hshort : right.length < cs.length := by
        obtain ⟨c, hc, hcm⟩ := (hcover s).1 (by
          simp [RangeMath.mem]
          omega)
        have hcb := candidate_inside_of_cover w q s t cs hcover c hc (hvalid c hc)
        have hcx := (candidate_interval w q c (hvalid c hc) s).1 hcm
        have hstart : c.1 = s := by omega
        apply List.length_filter_lt_length_iff_exists.mpr
        refine ⟨c, hc, ?_⟩
        simp [hstart, u, K]
      have hrec := ih hright_valid hright_cover
      simp only [List.length_cons]
      omega

theorem from_ipv4_trace {q : Nat} {r : RangeMath.HalfOpen}
    {bs : List (Nat × Nat)} (h : IPv4SubnetTraceMath.Trace q r bs) :
    Trace 32 q r bs := by
  induction h with
  | empty => exact Trace.empty
  | next s t hq hst rest hrest ih =>
      apply Trace.next s t (IPv4SubnetMath.bestPrefix s t q hq hst) hst
      · exact IPv4SubnetMath.best_eligible s t q hq hst
      · intro p hp
        exact IPv4SubnetMath.best_le_of_eligible s t q p hq hst hp
      · exact ih

theorem from_ipv6_trace {q : Nat} {r : RangeMath.HalfOpen}
    {bs : List (Nat × Nat)} (h : IPv6SubnetTraceMath.Trace q r bs) :
    Trace 128 q r bs := by
  induction h with
  | empty => exact Trace.empty
  | next s t hq hst rest hrest ih =>
      apply Trace.next s t (IPv6SubnetMath.bestPrefix s t q hq hst) hst
      · exact IPv6SubnetMath.best_eligible s t q hq hst
      · intro p hp
        exact IPv6SubnetMath.best_le_of_eligible s t q p hq hst hp
      · exact ih

theorem ipv4_trace_minimum {q : Nat} {r : RangeMath.HalfOpen}
    {bs cs : List (Nat × Nat)} (h : IPv4SubnetTraceMath.Trace q r bs)
    (hvalid : ∀ c ∈ cs, Candidate 32 q c)
    (hcover : ∀ x, RangeMath.mem r x ↔
      ∃ c ∈ cs, CidrModel.member 32 c.1 c.2 x) :
    bs.length ≤ cs.length :=
  trace_minimum (from_ipv4_trace h) hvalid hcover

theorem ipv6_trace_minimum {q : Nat} {r : RangeMath.HalfOpen}
    {bs cs : List (Nat × Nat)} (h : IPv6SubnetTraceMath.Trace q r bs)
    (hvalid : ∀ c ∈ cs, Candidate 128 q c)
    (hcover : ∀ x, RangeMath.mem r x ↔
      ∃ c ∈ cs, CidrModel.member 128 c.1 c.2 x) :
    bs.length ≤ cs.length :=
  trace_minimum (from_ipv6_trace h) hvalid hcover

end SubnetMinimumMath
