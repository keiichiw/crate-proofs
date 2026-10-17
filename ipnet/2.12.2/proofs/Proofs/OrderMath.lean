module
public import Proofs.CidrModel

public section

namespace OrderMath

/-- Big-endian value of a natural-number digit list. -/
@[expose] def digitsValue (base : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d * base ^ ds.length + digitsValue base ds

/-- Lexicographic comparison from the most significant digit. -/
@[expose] def lexCompare : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
      match compare x y with
      | .lt => .lt
      | .eq => lexCompare xs ys
      | .gt => .gt

theorem digitsValue_bound (base : Nat) (ds : List Nat)
    (hdigits : ∀ d ∈ ds, d < base) :
    digitsValue base ds < base ^ ds.length := by
  induction ds with
  | nil => simp [digitsValue]
  | cons d rest ih =>
    have hd : d < base := hdigits d (by simp)
    have hrest : ∀ x ∈ rest, x < base := by
      intro x hx
      exact hdigits x (by simp [hx])
    have htail := ih hrest
    have hm := Nat.mul_le_mul_right (base ^ rest.length) (Nat.succ_le_iff.mpr hd)
    simp only [digitsValue, List.length_cons, pow_succ]
    simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul] at hm
    have hcomm : base ^ rest.length * base = base * base ^ rest.length :=
      Nat.mul_comm _ _
    omega

private theorem value_lt_of_head_lt (base x y tx ty k : Nat)
    (hxy : x < y) (htx : tx < base ^ k) :
    x * base ^ k + tx < y * base ^ k + ty := by
  have hm := Nat.mul_le_mul_right (base ^ k) (Nat.succ_le_iff.mpr hxy)
  simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul] at hm
  omega

private theorem value_eq_of_head_eq (base x y tx ty k : Nat)
    (hxy : x = y) (htxy : tx = ty) :
    x * base ^ k + tx = y * base ^ k + ty := by
  subst x
  subst tx
  rfl

private theorem compare_add_left (c x y : Nat) :
    compare (c + x) (c + y) = compare x y := by
  cases h : compare x y with
  | lt =>
    exact Nat.compare_eq_lt.mpr (by have := Nat.compare_eq_lt.mp h; omega)
  | eq =>
    exact Nat.compare_eq_eq.mpr (by have := Nat.compare_eq_eq.mp h; omega)
  | gt =>
    exact Nat.compare_eq_gt.mpr (by have := Nat.compare_eq_gt.mp h; omega)

theorem lexCompare_eq_compare_value (base : Nat) (xs ys : List Nat)
    (hlen : xs.length = ys.length)
    (hxs : ∀ d ∈ xs, d < base)
    (hys : ∀ d ∈ ys, d < base) :
    lexCompare xs ys = compare (digitsValue base xs) (digitsValue base ys) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hlen' : xs.length = ys.length := by simpa using hlen
      have hx : x < base := hxs x (by simp)
      have hy : y < base := hys y (by simp)
      have hxs' : ∀ d ∈ xs, d < base := by
        intro d hd
        exact hxs d (by simp [hd])
      have hys' : ∀ d ∈ ys, d < base := by
        intro d hd
        exact hys d (by simp [hd])
      have htx := digitsValue_bound base xs hxs'
      have hty := digitsValue_bound base ys hys'
      by_cases hxy : x < y
      · have hval : digitsValue base (x :: xs) < digitsValue base (y :: ys) := by
          simp only [digitsValue, ← hlen']
          exact value_lt_of_head_lt base x y _ _ _ hxy htx
        simp [lexCompare, Nat.compare_eq_lt.mpr hxy, Nat.compare_eq_lt.mpr hval]
      · by_cases hyx : y < x
        · have hval : digitsValue base (y :: ys) < digitsValue base (x :: xs) := by
            simp only [digitsValue, hlen']
            exact value_lt_of_head_lt base y x _ _ _ hyx hty
          simp [lexCompare, Nat.compare_eq_gt.mpr hyx, Nat.compare_eq_gt.mpr hval]
        · have heq : x = y := by omega
          subst y
          have htail := ih ys hlen' hxs' hys'
          simp only [lexCompare, Nat.compare_eq_eq.mpr (rfl : x = x), digitsValue, hlen']
          rw [compare_add_left]
          exact htail

theorem bytesValue_eq_digitsValue (bs : List Aeneas.Std.U8) :
    CidrModel.bytesValue bs = digitsValue 256 (bs.map Aeneas.Std.UScalar.val) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [CidrModel.bytesValue, digitsValue, List.map_cons, List.length_map,
      ih]

theorem byte_lexCompare_eq_value (xs ys : List Aeneas.Std.U8)
    (hlen : xs.length = ys.length) :
    lexCompare (xs.map Aeneas.Std.UScalar.val) (ys.map Aeneas.Std.UScalar.val) =
      compare (CidrModel.bytesValue xs) (CidrModel.bytesValue ys) := by
  rw [bytesValue_eq_digitsValue, bytesValue_eq_digitsValue]
  apply lexCompare_eq_compare_value 256
  · simpa using hlen
  · intro d hd
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hd
    exact Aeneas.Std.U8.lt_succ_max b
  · intro d hd
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hd
    exact Aeneas.Std.U8.lt_succ_max b

theorem word_lexCompare_eq_value (xs ys : List Aeneas.Std.U16)
    (hlen : xs.length = ys.length) :
    lexCompare (xs.map Aeneas.Std.UScalar.val) (ys.map Aeneas.Std.UScalar.val) =
      compare (digitsValue 65536 (xs.map Aeneas.Std.UScalar.val))
        (digitsValue 65536 (ys.map Aeneas.Std.UScalar.val)) := by
  apply lexCompare_eq_compare_value 65536
  · simpa using hlen
  · intro d hd
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hd
    exact Aeneas.Std.U16.lt_succ_max b
  · intro d hd
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hd
    exact Aeneas.Std.U16.lt_succ_max b

end OrderMath
