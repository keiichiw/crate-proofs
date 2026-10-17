module
public import Proofs.IPv6SubnetMath

public section

namespace IPv6SubnetTraceMath

open IPv6SubnetMath

/-- A mathematical output is its stored numeric address and prefix. -/
def blockMem (b : Nat × Nat) (x : Nat) : Prop :=
  CidrModel.member 128 b.1 b.2 x

/-- A finite sequence of greedy steps. This is a logical trace, not a claim
that the Rust iterator allocates or collects a list. -/
inductive Trace (q : Nat) : RangeMath.HalfOpen → List (Nat × Nat) → Prop
  | empty : Trace q .empty []
  | next (s t : Nat) (hq : q ≤ 128) (hst : s < t)
      (rest : List (Nat × Nat))
      (hrest : Trace q (residual s t q hq hst) rest) :
      Trace q (.live s t) ((s, bestPrefix s t q hq hst) :: rest)

@[expose] def Valid : RangeMath.HalfOpen → Prop
  | .empty => True
  | .live s t => s < t ∧ t ≤ IPv6RangeMath.limit

theorem residual_valid (s t q : Nat) (hq : q ≤ 128)
    (hst : s < t) (ht : t ≤ IPv6RangeMath.limit) :
    Valid (residual s t q hq hst) := by
  by_cases hmore : s + blockSize s t q hq hst < t
  · simpa [residual, hmore, Valid] using
      (show s + blockSize s t q hq hst < t ∧
        t ≤ IPv6RangeMath.limit from ⟨hmore, ht⟩)
  · simp [residual, hmore, Valid]

theorem trace_length_bound {q : Nat} {r : RangeMath.HalfOpen}
    {bs : List (Nat × Nat)} (h : Trace q r bs) :
    bs.length ≤ RangeMath.size r := by
  induction h with
  | empty => simp [RangeMath.size]
  | next s t hq hst rest hrest ih =>
      have hs := residual_size s t q hq hst
      have hp := blockSize_pos s t q hq hst
      simp only [List.length_cons, RangeMath.size]
      omega

theorem trace_empty_only {q : Nat} {bs : List (Nat × Nat)}
    (h : Trace q .empty bs) : bs = [] := by
  cases h
  rfl

theorem trace_unique {q : Nat} {r : RangeMath.HalfOpen}
    {bs cs : List (Nat × Nat)} (hbs : Trace q r bs)
    (hcs : Trace q r cs) : bs = cs := by
  induction hbs generalizing cs with
  | empty =>
      cases hcs
      rfl
  | next s t hq hst rest hrest ih =>
      cases hcs with
      | next _ _ _ _ cs hcs =>
          simp [ih hcs]

theorem trace_exists (q : Nat) (hq : q ≤ 128)
    (r : RangeMath.HalfOpen) (hr : Valid r) :
    ∃ bs, Trace q r bs ∧ bs.length ≤ RangeMath.size r := by
  suffices ∀ n : Nat, ∀ r : RangeMath.HalfOpen,
      RangeMath.size r = n → Valid r →
      ∃ bs, Trace q r bs ∧ bs.length ≤ RangeMath.size r by
    exact this (RangeMath.size r) r rfl hr
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro r hrsize hvalid
    cases r with
    | empty => exact ⟨[], Trace.empty, by simp [RangeMath.size]⟩
    | live s t =>
        obtain ⟨hst, ht⟩ := hvalid
        have hsmaller : RangeMath.size (residual s t q hq hst) < n := by
          rw [← hrsize]
          exact residual_strictly_smaller s t q hq hst
        obtain ⟨rest, hrest, hlen⟩ :=
          ih _ hsmaller (residual s t q hq hst) rfl
            (residual_valid s t q hq hst ht)
        refine ⟨(s, bestPrefix s t q hq hst) :: rest,
          Trace.next s t hq hst rest hrest, ?_⟩
        have hs := residual_size s t q hq hst
        have hp := blockSize_pos s t q hq hst
        simp only [List.length_cons, RangeMath.size]
        omega

theorem trace_partition {q : Nat} {r : RangeMath.HalfOpen}
    {bs : List (Nat × Nat)} (h : Trace q r bs) (x : Nat) :
    RangeMath.mem r x ↔ ∃ b ∈ bs, blockMem b x := by
  induction h with
  | empty => simp [RangeMath.mem]
  | next s t hq hst rest hrest ih =>
      rw [residual_partition s t q x hq hst]
      rw [← block_membership s t q x hq hst]
      rw [ih]
      simp only [List.mem_cons]
      constructor
      · intro h
        rcases h with hb | ⟨b, hbi, hbm⟩
        · exact ⟨(s, bestPrefix s t q hq hst), Or.inl rfl, hb⟩
        · exact ⟨b, Or.inr hbi, hbm⟩
      · rintro ⟨b, hb, hbm⟩
        rcases hb with heq | htail
        · subst b
          exact Or.inl hbm
        · exact Or.inr ⟨b, htail, hbm⟩

theorem trace_canonical {q : Nat} {r : RangeMath.HalfOpen}
    {bs : List (Nat × Nat)} (h : Trace q r bs) :
    ∀ b ∈ bs, q ≤ b.2 ∧ b.2 ≤ 128 ∧
      CidrModel.lower 128 b.1 b.2 = b.1 := by
  induction h with
  | empty => simp
  | next s t hq hst rest hrest ih =>
      intro b hb
      rcases List.mem_cons.mp hb with heq | htail
      · subst b
        obtain ⟨hlo, _⟩ := block_canonical s t q hq hst
        obtain ⟨hmin, hmax⟩ := best_bounds s t q hq hst
        exact ⟨hmin, hmax, hlo⟩
      · exact ih b htail

theorem trace_output_start_in_range {q : Nat} {r : RangeMath.HalfOpen}
    {bs : List (Nat × Nat)} (h : Trace q r bs)
    (b : Nat × Nat) (hb : b ∈ bs) : RangeMath.mem r b.1 := by
  have hcanon := (trace_canonical h b hb).2.2
  have hblock : blockMem b b.1 := by
    unfold blockMem
    simpa only [hcanon] using CidrModel.lower_mem 128 b.1 b.2
  exact (trace_partition h b.1).2 ⟨b, hb, hblock⟩

/-- Earlier output CIDRs end before later stored addresses. This gives
increasing starts and pairwise disjoint sets. -/
theorem trace_ordered {q : Nat} {r : RangeMath.HalfOpen}
    {bs : List (Nat × Nat)} (h : Trace q r bs) :
    bs.Pairwise (fun a b => CidrModel.upper 128 a.1 a.2 + 1 ≤ b.1) := by
  induction h with
  | empty => exact List.Pairwise.nil
  | next s t hq hst rest hrest ih =>
      apply List.pairwise_cons.mpr
      constructor
      · intro b hb
        have hstart := trace_output_start_in_range hrest b hb
        have hbound : s + blockSize s t q hq hst ≤ b.1 := by
          by_cases hmore : s + blockSize s t q hq hst < t
          · have hh : s + blockSize s t q hq hst ≤ b.1 ∧ b.1 < t := by
              simpa [residual, hmore, RangeMath.mem] using hstart
            exact hh.1
          · simp [residual, hmore, RangeMath.mem] at hstart
        have he := (block_canonical s t q hq hst).2
        simpa [he] using hbound
      · exact ih

theorem trace_pairwise_disjoint {q : Nat} {r : RangeMath.HalfOpen}
    {bs : List (Nat × Nat)} (h : Trace q r bs) :
    bs.Pairwise (fun a b => ∀ x, ¬ (blockMem a x ∧ blockMem b x)) := by
  apply (trace_ordered h).imp_of_mem
  intro a b _ha hb horder x hab
  have hcanon := (trace_canonical h b hb).2.2
  have hleft := hab.1.2
  have hright := hab.2.1
  change CidrModel.upper 128 a.1 a.2 + 1 ≤ b.1 at horder
  change x ≤ CidrModel.upper 128 a.1 a.2 at hleft
  change CidrModel.lower 128 b.1 b.2 ≤ x at hright
  rw [hcanon] at hright
  omega

/-- The fixed-size sequence produced when a requested prefix partitions an
aligned interval exactly. -/
def fixedBlocks (s q : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 => (s, q) :: fixedBlocks (s + 2 ^ (128 - q)) q n

def fixedState (s q n : Nat) : RangeMath.HalfOpen :=
  if n = 0 then .empty else .live s (s + n * 2 ^ (128 - q))

theorem fixed_blocks_length (s q n : Nat) :
    (fixedBlocks s q n).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [fixedBlocks, ih]

theorem fixed_blocks_mem_iff (s q n : Nat) (b : Nat × Nat) :
    b ∈ fixedBlocks s q n ↔
      ∃ i, i < n ∧ b = (s + i * 2 ^ (128 - q), q) := by
  induction n generalizing s with
  | zero => simp [fixedBlocks]
  | succ n ih =>
      let k := 2 ^ (128 - q)
      simp only [fixedBlocks, List.mem_cons]
      constructor
      · intro hb
        rcases hb with hhead | htail
        · exact ⟨0, by omega, by simpa [k] using hhead⟩
        · obtain ⟨i, hi, hbi⟩ := (ih (s + k)).1 htail
          refine ⟨i + 1, by omega, ?_⟩
          rw [hbi]
          simp [k, Nat.succ_mul]
          omega
      · rintro ⟨i, hi, hbi⟩
        cases i with
        | zero => left; simpa [k] using hbi
        | succ i =>
            right
            apply (ih (s + k)).2
            refine ⟨i, by omega, ?_⟩
            rw [hbi]
            simp [k, Nat.succ_mul]
            omega

/-- The `i`th mathematical output has exactly the constructor-requested
prefix and the expected big-endian numeric start. -/
theorem fixed_blocks_get_opt (s q n i : Nat) :
    (fixedBlocks s q n)[i]? =
      if i < n then some (s + i * 2 ^ (128 - q), q) else none := by
  induction n generalizing s i with
  | zero => simp [fixedBlocks]
  | succ n ih =>
      cases i with
      | zero => simp [fixedBlocks]
      | succ i =>
          simp only [fixedBlocks, List.getElem?_cons_succ]
          rw [ih]
          by_cases hi : i < n
          · simp [hi, Nat.succ_mul]
            omega
          · have hs : ¬ i + 1 < n + 1 := by omega
            simp [hi, hs]

theorem best_eq_requested (s t q : Nat) (hq : q ≤ 128)
    (hst : s < t) (halign : s % 2 ^ (128 - q) = 0)
    (hfit : s + 2 ^ (128 - q) ≤ t) :
    bestPrefix s t q hq hst = q := by
  have he : eligible s t q q := by
    simp only [eligible]
    exact ⟨by omega, hq, halign, hfit⟩
  have hle := best_le_of_eligible s t q q hq hst he
  have hge := (best_bounds s t q hq hst).1
  omega

theorem fixed_trace (q n s : Nat) (hq : q ≤ 128)
    (halign : s % 2 ^ (128 - q) = 0) :
    Trace q (fixedState s q n) (fixedBlocks s q n) := by
  induction n generalizing s with
  | zero => exact Trace.empty
  | succ n ih =>
      let k := 2 ^ (128 - q)
      have hk : 0 < k := by dsimp [k]; positivity
      let t := s + (n + 1) * k
      have hmul : (n + 1) * k = k + n * k := by
        simp [Nat.succ_mul, Nat.add_comm]
      have htEq : t = s + k + n * k := by dsimp [t]; omega
      have hst : s < t := by omega
      have hfit : s + k ≤ t := by omega
      have hp : bestPrefix s t q hq hst = q :=
        best_eq_requested s t q hq hst halign hfit
      have hsize : blockSize s t q hq hst = k := by
        simp [blockSize, hp, k]
      have halign' : (s + k) % k = 0 := by
        simp [halign, k]
      have hrest : residual s t q hq hst = fixedState (s + k) q n := by
        by_cases hn : n = 0
        · subst n
          have hlast : t = s + k := by omega
          have hnmore : ¬ s + blockSize s t q hq hst < t := by
            rw [hsize, hlast]
            omega
          simp [residual, hnmore, fixedState]
        · have hmore : s + k < t := by
            have hnpos : 0 < n := by omega
            have hnk : 0 < n * k := Nat.mul_pos hnpos hk
            omega
          simp only [residual, hsize, hmore, ↓reduceIte]
          simp only [fixedState, hn, ↓reduceIte]
          exact congrArg (RangeMath.HalfOpen.live (s + k)) htEq
      have htrace := ih (s + k) halign'
      rw [← hrest] at htrace
      have hmain := Trace.next s t hq hst _ htrace
      simpa [fixedState, fixedBlocks, t, hp, k] using hmain

theorem network_size_factor (p q : Nat) (hpq : p ≤ q) (hq : q ≤ 128) :
    CidrModel.size 128 p = 2 ^ (q - p) * 2 ^ (128 - q) := by
  have hexp : 128 - p = (q - p) + (128 - q) := by omega
  simp [CidrModel.size, hexp, pow_add]

theorem network_lower_align_requested (a p q : Nat)
    (hpq : p ≤ q) (hq : q ≤ 128) :
    CidrModel.lower 128 a p % 2 ^ (128 - q) = 0 := by
  let k := 2 ^ (128 - q)
  let n := 2 ^ (q - p)
  have hsize : CidrModel.size 128 p = n * k :=
    network_size_factor p q hpq hq
  simp only [CidrModel.lower, hsize]
  have hmod : (a / (n * k) * (n * k)) % k = 0 := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_mod_left (a / (n * k) * n) k
  exact hmod

theorem network_origin_fixed_trace (a p q : Nat)
    (hpq : p ≤ q) (hq : q ≤ 128) :
    Trace q
      (RangeMath.HalfOpen.live (CidrModel.lower 128 a p)
        (CidrModel.upper 128 a p + 1))
      (fixedBlocks (CidrModel.lower 128 a p) q (2 ^ (q - p))) := by
  let s := CidrModel.lower 128 a p
  let n := 2 ^ (q - p)
  let k := 2 ^ (128 - q)
  have hn : 0 < n := by dsimp [n]; positivity
  have hsize : CidrModel.size 128 p = n * k :=
    network_size_factor p q hpq hq
  have hupper : CidrModel.upper 128 a p + 1 = s + n * k := by
    rw [CidrModel.upper_eq, hsize]
    dsimp [s]
    have hnk : 0 < n * k :=
      Nat.mul_pos hn (by dsimp [k]; positivity)
    omega
  have halign : s % k = 0 := network_lower_align_requested a p q hpq hq
  have htrace := fixed_trace q n s hq halign
  simpa [fixedState, hn, s, n, k, hupper] using htrace

theorem network_origin_partition (a p q x : Nat)
    (hpq : p ≤ q) (hq : q ≤ 128) :
    RangeMath.mem
        (.live (CidrModel.lower 128 a p) (CidrModel.upper 128 a p + 1)) x ↔
      ∃ b ∈ fixedBlocks (CidrModel.lower 128 a p) q (2 ^ (q - p)),
        blockMem b x :=
  trace_partition (network_origin_fixed_trace a p q hpq hq) x

theorem network_origin_count (a p q : Nat) :
    (fixedBlocks (CidrModel.lower 128 a p) q (2 ^ (q - p))).length =
      2 ^ (q - p) :=
  fixed_blocks_length _ _ _

end IPv6SubnetTraceMath
