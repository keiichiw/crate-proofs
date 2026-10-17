module
public import Proofs.IPv4SubnetBits
public import Proofs.IPv4MaskMath

public section
open Aeneas Aeneas.Std Result

namespace IPv4SubnetRangeBits

theorem leading_zeros_value (r : U32) :
    (core.num.U32.leading_zeros r).val = r.bv.clz.toNat := by
  have hc : r.bv.clz.toNat ≤ 32 := by
    simpa [BitVec.le_def] using (BitVec.clz_le (x := r.bv))
  simp only [core.num.U32.leading_zeros, IPv4SubnetBits.lz_eq_clz]
  simp [UScalar.val]

theorem leading_zeros_range_bounds (r : U32) (hr : 0 < r.val) :
    let lz := (core.num.U32.leading_zeros r).val
    let k := 32-lz
    0 < k ∧ k ≤ 32 ∧ 2^(k-1) ≤ r.val ∧ r.val < 2^k := by
  dsimp
  rw [leading_zeros_value]
  have hnz : r.bv ≠ 0#32 := by
    intro he
    have := congrArg BitVec.toNat he
    simp [UScalar.val, he] at hr
  have hc : r.bv.clz.toNat < 32 := by
    have hh := (BitVec.clz_lt_iff_ne_zero (x := r.bv)).2 hnz
    simpa [BitVec.lt_def] using hh
  have hlo := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero
    (x := r.bv) (by omega : 0 < 32) hnz
  have hhi := BitVec.toNat_lt_two_pow_sub_clz (x := r.bv)
  constructor
  · omega
  constructor
  · omega
  constructor
  · have he : 32 - 1 - r.bv.clz.toNat = 32 - r.bv.clz.toNat - 1 := by omega
    rw [he] at hlo
    exact hlo
  · exact hhi

theorem complement_mod (k r : Nat) (hk : k ≤ 32) (hr : r < 2^k) :
    (2^32 - 1 - r) % 2^k = 2^k - 1 - r := by
  have hpow : 2^32 = 2^(32-k) * 2^k := by
    rw [← pow_add]
    congr 1
    omega
  have hC : 0 < 2^(32-k) := by positivity
  have hD : 0 < 2^k := by positivity
  have hrem : 2^k - 1 - r < 2^k := by omega
  have hmul : 2^k ≤ 2^(32-k) * 2^k := by
    calc
      2^k = 1 * 2^k := by simp
      _ ≤ 2^(32-k) * 2^k := Nat.mul_le_mul_right (2^k) (by simp)
  have heq : 2^32 - 1 - r =
      (2^(32-k) - 1) * 2^k + (2^k - 1 - r) := by
    rw [hpow, Nat.sub_mul]
    omega
  rw [heq]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hrem]

theorem trailing_ones_mersenne (r : U32) (k : Nat) (hk : k ≤ 32)
    (hr : r.val < 2^k) :
    ∃ out, ipnet.core.num.U32.trailing_ones r = Result.ok out ∧
      (k ≤ out.val ↔ r.val + 1 = 2^k) := by
  let z := ~~~r
  rcases IPv4SubnetBits.trailing_zeros_mod_spec z k hk with
    ⟨out, hout, hmod⟩
  refine ⟨out, ?_, ?_⟩
  · simp [ipnet.core.num.U32.trailing_ones, hout, z, lift, bind_ok]
  · rw [hmod, IPv4MaskMath.not_val]
    rw [complement_mod k r.val hk hr]
    omega

theorem range_threshold_nat (r k t p : Nat) (hp : p ≤ 32)
    (hk0 : 0 < k) (hk : k ≤ 32)
    (hlo : 2^(k-1) ≤ r) (hhi : r < 2^k)
    (ht : t ≤ 32)
    (hmk : k ≤ t ↔ r+1 = 2^k)
    (hmk1 : k < 32 → (k+1 ≤ t ↔ r+1 = 2^(k+1))) :
    (if 32-k+t=32 then 32-k else 33-k) ≤ p ↔
      2^(32-p) ≤ r+1 := by
  have htk : t ≤ k := by
    by_cases htop : k = 32
    · omega
    · have hlt : k < 32 := by omega
      by_contra hn
      have he := (hmk1 hlt).mp (by omega : k+1 ≤ t)
      have hpow : 2^k < 2^(k+1) := by
        rw [pow_succ]
        have : 0 < 2^k := by positivity
        omega
      omega
  by_cases hm : r+1 = 2^k
  · have hteq : t = k := by
      have := hmk.mpr hm
      omega
    have hpl : (if 32-k+t=32 then 32-k else 33-k) = 32-k := by
      simp [hteq, Nat.sub_add_cancel hk]
    rw [hpl, hm]
    constructor
    · intro h
      have he : 32-p ≤ k := by omega
      exact Nat.pow_le_pow_right (by omega : 0 < 2) he
    · intro h
      by_contra hn
      have he : k < 32-p := by omega
      have hs : 2^k < 2^(32-p) := Nat.pow_lt_pow_right (by omega : 1 < 2) he
      omega
  · have htlt : t < k := by
      have : ¬k ≤ t := by exact fun h => hm (hmk.mp h)
      omega
    have hpl : (if 32-k+t=32 then 32-k else 33-k) = 33-k := by
      have hn : 32-k+t ≠ 32 := by omega
      simp [hn]
    rw [hpl]
    have hrlt : r+1 < 2^k := by omega
    constructor
    · intro h
      have he : 32-p ≤ k-1 := by omega
      have hpwr : 2^(32-p) ≤ 2^(k-1) :=
        Nat.pow_le_pow_right (by omega : 0 < 2) he
      omega
    · intro h
      by_contra hn
      have he : k ≤ 32-p := by omega
      have hpwr : 2^k ≤ 2^(32-p) :=
        Nat.pow_le_pow_right (by omega : 0 < 2) he
      omega

/-- The extracted range-prefix calculation is the exact size threshold for
    every possible IPv4 prefix. This bridges the real bit counts to the
    independent power-of-two condition. -/
theorem range_prefix_threshold (r : U32) (p : Nat) (hp : p ≤ 32) :
    ∃ ones, ipnet.core.num.U32.trailing_ones r = Result.ok ones ∧
      (let lz := (core.num.U32.leading_zeros r).val
       (if lz + ones.val = 32 then lz else lz + 1) ≤ p ↔
         2^(32-p) ≤ r.val+1) := by
  by_cases hz : r.val = 0
  · have hr : r = 0#u32 := by
      apply UScalar.eq_of_val_eq
      simpa using hz
    subst r
    rcases trailing_ones_mersenne (0#u32) 1 (by decide) (by norm_num) with
      ⟨ones,hones,hm⟩
    have hone : ones.val = 0 := by
      have hn : ¬ 1 ≤ ones.val := by
        intro h
        have he := hm.mp h
        norm_num at he
      omega
    refine ⟨ones, hones, ?_⟩
    · have hlz : (core.num.U32.leading_zeros 0#u32).val = 32 := by decide
      simp only [hlz, hone, Nat.add_zero, ↓reduceIte]
      constructor
      · intro h
        have : p = 32 := by omega
        subst p
        norm_num
      · intro h
        by_contra hn
        have he : 1 ≤ 32-p := by omega
        have hpwr : 2^1 ≤ 2^(32-p) :=
          Nat.pow_le_pow_right (by decide : 0 < 2) he
        norm_num at hpwr
        omega
  · have hr0 : 0 < r.val := by omega
    let lz := (core.num.U32.leading_zeros r).val
    let k := 32-lz
    rcases leading_zeros_range_bounds r hr0 with ⟨hk0,hk,hlo,hhi⟩
    rcases trailing_ones_mersenne r k hk hhi with ⟨ones,hones,hmk⟩
    rcases IPv4SubnetBits.trailing_zeros_le_width (~~~r) with
      ⟨z,hzres,hzbound⟩
    have honeseq : ones = z := by
      have he : ipnet.core.num.U32.trailing_ones r = Result.ok z := by
        simp [ipnet.core.num.U32.trailing_ones, hzres, lift, bind_ok]
      rw [hones] at he
      exact Result.ok_injective he
    have ht : ones.val ≤ 32 := honeseq ▸ hzbound
    have hmk1 : k < 32 → (k+1 ≤ ones.val ↔ r.val+1 = 2^(k+1)) := by
      intro hklt
      change r.val < 2^k at hhi
      have hpow : r.val < 2^(k+1) := by
        exact lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
      rcases trailing_ones_mersenne r (k+1) (by omega) hpow with
        ⟨o,ho,hm⟩
      have he : o = ones := by
        rw [hones] at ho
        exact Result.ok_injective ho.symm
      simpa [he] using hm
    refine ⟨ones, hones, ?_⟩
    have hnat := range_threshold_nat r.val k ones.val p hp hk0 hk hlo hhi ht hmk hmk1
    have hback : 32-k = lz := by
      dsimp [k]
      have hlz : lz ≤ 32 := by
        simpa [lz, leading_zeros_value, BitVec.le_def] using
          (BitVec.clz_le (x := r.bv))
      omega
    have hplus : 33-k = lz+1 := by omega
    simpa only [lz, hback, hplus] using hnat

theorem range_prefix_all (r : U32) :
    ∃ ones, ipnet.core.num.U32.trailing_ones r = Result.ok ones ∧
      ones.val ≤ 32 ∧
      (∀ p ≤ 32,
        (let lz := (core.num.U32.leading_zeros r).val
         (if lz + ones.val = 32 then lz else lz + 1) ≤ p ↔
           2^(32-p) ≤ r.val+1)) := by
  rcases IPv4SubnetBits.trailing_zeros_le_width (~~~r) with
    ⟨ones,hz,hbound⟩
  have hones : ipnet.core.num.U32.trailing_ones r = Result.ok ones := by
    simp [ipnet.core.num.U32.trailing_ones, hz, lift, bind_ok]
  refine ⟨ones,hones,hbound,?_⟩
  intro p hp
  rcases range_prefix_threshold r p hp with ⟨o,ho,hiff⟩
  have he : o = ones := Result.ok_injective (ho.symm.trans hones)
  simpa [he] using hiff

end IPv4SubnetRangeBits
