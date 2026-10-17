module
public import Proofs.Spec

@[expose] public section

open Aeneas.Std

namespace adler2

theorem run_four (s : Nat × Nat) (x0 x1 x2 x3 : U8) :
    run s [x0, x1, x2, x3] =
      ((s.1 + x0.val + x1.val + x2.val + x3.val) % modulus,
       (s.2 + 4 * s.1 + 4 * x0.val + 3 * x1.val + 2 * x2.val + x3.val) % modulus) := by
  simp [run, step, normalize, modulus]
  omega

abbrev Lanes := Fin 4 → Nat

def sum4 (a : Lanes) : Nat := a 0 + a 1 + a 2 + a 3

def weight (a : Lanes) : Nat := a 1 + 2 * a 2 + 3 * a 3

def byteWeight (x : Lanes) : Nat := 4 * x 0 + 3 * x 1 + 2 * x 2 + x 3

def laneAdd (a x : Lanes) : Lanes := fun i => a i + x i

def laneStep (st : Lanes × Lanes) (x : Lanes) : Lanes × Lanes :=
  let a := laneAdd st.1 x
  (a, laneAdd st.2 a)

theorem sum4_laneAdd (a x : Lanes) :
    sum4 (laneAdd a x) = sum4 a + sum4 x := by
  simp only [sum4, laneAdd]
  omega

theorem weight_laneAdd (a x : Lanes) :
    weight (laneAdd a x) = weight a + weight x := by
  simp only [weight, laneAdd]
  omega

theorem byteWeight_add_weight (x : Lanes) :
    byteWeight x + weight x = 4 * sum4 x := by
  simp only [byteWeight, weight, sum4]
  omega

theorem run_four_lanes (s : Nat × Nat) (x0 x1 x2 x3 : U8) :
    let x : Lanes := ![x0.val, x1.val, x2.val, x3.val]
    run s [x0, x1, x2, x3] =
      ((s.1 + sum4 x) % modulus, (s.2 + 4 * s.1 + byteWeight x) % modulus) := by
  simp [sum4, byteWeight, run_four, modulus]
  omega

def laneInv (a0 c ra rb : Nat) (a b : Lanes) : Prop :=
  Nat.ModEq modulus ra (a0 + sum4 a) ∧
  Nat.ModEq modulus (rb + weight a) (c + 4 * sum4 b)

theorem laneInv_step (a0 c ra rb : Nat) (a b x : Lanes)
    (h : laneInv a0 c ra rb a b) :
    laneInv a0 (c + 4 * a0)
      ((ra + sum4 x) % modulus)
      ((rb + 4 * ra + byteWeight x) % modulus)
      (laneAdd a x) (laneAdd b (laneAdd a x)) := by
  rcases h with ⟨ha, hb⟩
  constructor
  · have h1 := ha.add_right (sum4 x)
    have h2 : ra + sum4 x ≡ a0 + sum4 (laneAdd a x) [MOD modulus] := by
      simpa [sum4_laneAdd, Nat.add_assoc] using h1
    exact (Nat.mod_modEq _ _).trans h2
  · have hs := (hb.add (ha.mul_left 4)).add_right (4 * sum4 x)
    have hw := byteWeight_add_weight x
    have hEq :
        rb + 4 * ra + byteWeight x + (weight (laneAdd a x)) ≡
          (c + 4 * a0) + 4 * sum4 (laneAdd b (laneAdd a x))
          [MOD modulus] := by
      rw [weight_laneAdd, sum4_laneAdd, sum4_laneAdd]
      convert hs using 1 <;> omega
    exact (Nat.mod_modEq _ _).add_right _ |>.trans hEq


theorem laneInv_initial (a0 b0 : Nat) :
    laneInv a0 b0 a0 b0 (fun _ => 0) (fun _ => 0) := by
  simp only [laneInv, sum4, weight, add_zero, mul_zero]
  exact ⟨rfl, rfl⟩

theorem laneInv_initial_normalized (a0 b0 : Nat) :
    laneInv a0 b0 (a0 % modulus) (b0 % modulus)
      (fun _ => 0) (fun _ => 0) := by
  simp only [laneInv, sum4, weight, add_zero, mul_zero]
  exact ⟨Nat.mod_modEq a0 modulus, Nat.mod_modEq b0 modulus⟩

theorem laneInv_run_four (a0 c ra rb : Nat) (a b : Lanes)
    (x0 x1 x2 x3 : U8) (h : laneInv a0 c ra rb a b) :
    let x : Lanes := ![x0.val, x1.val, x2.val, x3.val]
    let r := run (ra, rb) [x0, x1, x2, x3]
    laneInv a0 (c + 4 * a0) r.1 r.2
      (laneAdd a x) (laneAdd b (laneAdd a x)) := by
  simp only [run_four_lanes]
  exact laneInv_step a0 c ra rb a b _ h

def laneMod (a : Lanes) : Lanes := fun i => a i % modulus

theorem sum4_laneMod (a : Lanes) :
    sum4 (laneMod a) ≡ sum4 a [MOD modulus] := by
  simp [Nat.ModEq, sum4, laneMod, Nat.add_mod]

theorem weight_laneMod (a : Lanes) :
    weight (laneMod a) ≡ weight a [MOD modulus] := by
  simp [Nat.ModEq, weight, laneMod, Nat.add_mod, Nat.mul_mod]

theorem laneInv_mod (a0 c ra rb : Nat) (a b : Lanes)
    (h : laneInv a0 c ra rb a b) :
    laneInv a0 (c % modulus) ra rb (laneMod a) (laneMod b) := by
  rcases h with ⟨ha, hb⟩
  constructor
  · exact ha.trans ((sum4_laneMod a).symm.add_left a0)
  · have hl := (weight_laneMod a).add_left rb
    have hc := Nat.mod_modEq c modulus
    have hr' := hc.add (sum4_laneMod b |>.mul_left 4)
    exact hl.trans hb |>.trans hr'.symm

def correction (a : Lanes) : Nat :=
  (modulus - a 1) + 2 * (modulus - a 2) + 3 * (modulus - a 3)

theorem correction_weight (a : Lanes)
    (ha : ∀ i : Fin 4, a i < modulus) :
    correction a + weight a = 6 * modulus := by
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  simp only [correction, weight]
  omega

theorem laneInv_combine (a0 c ra rb : Nat) (a b : Lanes)
    (h : laneInv a0 c ra rb a b)
    (hra : ra < modulus) (hrb : rb < modulus)
    (hA : ∀ i : Fin 4, a i < modulus) :
    (a0 + sum4 a) % modulus = ra ∧
    (c + 4 * sum4 b + correction a) % modulus = rb := by
  rcases h with ⟨ha, hb⟩
  constructor
  · change ra % modulus = (a0 + sum4 a) % modulus at ha
    rw [Nat.mod_eq_of_lt hra] at ha
    exact ha.symm
  · have hs := hb.add_right (correction a)
    have hw := correction_weight a hA
    have hleft : (rb + weight a + correction a) % modulus = rb := by
      have heq : rb + weight a + correction a = rb + 6 * modulus := by omega
      rw [heq, Nat.add_mod, Nat.mul_mod]
      simp [Nat.mod_eq_of_lt hrb]
    change (rb + weight a + correction a) % modulus =
      (c + 4 * sum4 b + correction a) % modulus at hs
    exact hs.symm.trans hleft

end adler2
