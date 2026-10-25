import BytesRange
open Aeneas Aeneas.Std Result
namespace range_proofs
abbrev Bound := bytes_range.core.ops.range.Bound
abbrev RangeBounds := bytes_range.core.ops.range.RangeBounds

def beginNat : Bound Usize → Nat
  | .Included n => n.val
  | .Excluded n => n.val + 1
  | .Unbounded => 0

def endNat (len : Usize) : Bound Usize → Nat
  | .Included n => n.val + 1
  | .Excluded n => n.val
  | .Unbounded => len.val

def increment (n : Usize) : Result Usize := do
  let o ← lift (Usize.checked_add n 1#usize)
  core.option.Option.expect o (toStr "out of range")

def beginValue : Bound Usize → Result Usize
  | .Included n => .ok n
  | .Excluded n => increment n
  | .Unbounded => .ok 0#usize

def endValue (len : Usize) : Bound Usize → Result Usize
  | .Included n => increment n
  | .Excluded n => .ok n
  | .Unbounded => .ok len

def validate (a b len : Usize) : Result (Usize × Usize) :=
  if a ≤ b then if b ≤ len then .ok (a,b) else .fail .panic else .fail .panic

theorem range_fragments_eq {T} (R : RangeBounds T Usize) (r : T) (len : Usize)
    (a b : Bound Usize) (ha : R.start_bound r = .ok a) (hb : R.end_bound r = .ok b) :
    bytes_range.range R r len = (do
      let first ← beginValue a
      let last ← endValue len b
      validate first last len) := by
  cases a <;> cases b <;>
    simp [bytes_range.range,ha,hb,beginValue,endValue,increment,validate,
      core.fmt.rt.Argument.new_debug_without_dictionary,core.fmt.Arguments.new,core.fmt.rt.Argument,core.fmt.Arguments,bind_ok]

private theorem wp_success {α : Type _} {m : Result α} {p : α → Prop}
    (h : WP.spec m p) : ∃ out, m = .ok out ∧ p out := by
  cases m using Result.cases with
  | ret x => exact ⟨x, rfl, (WP.spec_ok x).mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

theorem increment_success (n : Usize) (hn : n.val + 1 ≤ Usize.max) :
    ∃ out, increment n = .ok out ∧ out.val = n.val + 1 := by
  have hs := Usize.checked_add_bv_spec n 1#usize
  cases h : Usize.checked_add n 1#usize with
  | none => simp [h] at hs; omega
  | some out =>
    simp only [h] at hs
    refine ⟨out, ?_, ?_⟩
    · simp [increment,h,lift,bind_ok,core.option.Option.expect,Result.ofOption]
    · simpa using hs.2.1

theorem begin_success (a : Bound Usize) (ha : beginNat a ≤ Usize.max) :
    ∃ out, beginValue a = .ok out ∧ out.val = beginNat a := by
  cases a with
  | Included n => exact ⟨n,rfl,rfl⟩
  | Excluded n => exact increment_success n ha
  | Unbounded => exact ⟨0#usize,rfl,by simp [beginNat]⟩

theorem end_success (len : Usize) (a : Bound Usize) (ha : endNat len a ≤ Usize.max) :
    ∃ out, endValue len a = .ok out ∧ out.val = endNat len a := by
  cases a with
  | Included n => exact increment_success n ha
  | Excluded n => exact ⟨n,rfl,rfl⟩
  | Unbounded => exact ⟨len,rfl,rfl⟩

def Valid (a b : Bound Usize) (len : Usize) : Prop :=
  beginNat a ≤ endNat len b ∧ endNat len b ≤ len.val

theorem range_success {T} (R : RangeBounds T Usize) (r : T) (len : Usize)
    (a b : Bound Usize) (ha : R.start_bound r = .ok a) (hb : R.end_bound r = .ok b)
    (hvalid : Valid a b len) :
    ∃ out, bytes_range.range R r len = .ok out ∧
      out.1.val = beginNat a ∧ out.2.val = endNat len b := by
  have hlen : len.val ≤ Usize.max := by scalar_tac
  obtain ⟨first,hfirst,hfirstval⟩ := begin_success a (by unfold Valid at hvalid; omega)
  obtain ⟨last,hlast,hlastval⟩ := end_success len b (by unfold Valid at hvalid; omega)
  refine ⟨(first,last),?_,hfirstval,hlastval⟩
  rw [range_fragments_eq R r len a b ha hb,hfirst,bind_ok,hlast,bind_ok]
  have h₁ : first ≤ last := by unfold Valid at hvalid; scalar_tac
  have h₂ : last ≤ len := by unfold Valid at hvalid; scalar_tac
  simp only [validate,ite_eq_left h₁,ite_eq_left h₂]

theorem increment_overflow (n : Usize) (hn : Usize.max < n.val + 1) :
    increment n = .fail .panic := by
  have hs := Usize.checked_add_bv_spec n 1#usize
  cases h : Usize.checked_add n 1#usize with
  | none => simp [increment,h,lift,bind_ok,core.option.Option.expect,Result.ofOption]
  | some out => simp [h] at hs; omega

theorem begin_overflow (a : Bound Usize) (ha : Usize.max < beginNat a) :
    beginValue a = .fail .panic := by
  cases a with
  | Included n => have hn := n.hBounds; simp only [beginNat] at ha; scalar_tac
  | Excluded n => exact increment_overflow n ha
  | Unbounded => simp [beginNat] at ha

theorem end_overflow (len : Usize) (a : Bound Usize) (ha : Usize.max < endNat len a) :
    endValue len a = .fail .panic := by
  cases a with
  | Included n => exact increment_overflow n ha
  | Excluded n => have hn := n.hBounds; simp only [endNat] at ha; scalar_tac
  | Unbounded => have hn := len.hBounds; simp only [endNat] at ha; scalar_tac

theorem range_invalid {T} (R : RangeBounds T Usize) (r : T) (len : Usize)
    (a b : Bound Usize) (ha : R.start_bound r = .ok a) (hb : R.end_bound r = .ok b)
    (hvalid : ¬ Valid a b len) :
    bytes_range.range R r len = .fail .panic := by
  rw [range_fragments_eq R r len a b ha hb]
  by_cases hfirst : beginNat a ≤ Usize.max
  · obtain ⟨first,hfirsteq,hfirstval⟩ := begin_success a hfirst
    rw [hfirsteq,bind_ok]
    by_cases hlast : endNat len b ≤ Usize.max
    · obtain ⟨last,hlasteq,hlastval⟩ := end_success len b hlast
      rw [hlasteq,bind_ok]
      unfold validate
      split_ifs with h₁ h₂
      · exfalso
        apply hvalid
        unfold Valid
        scalar_tac
      · rfl
      · rfl
    · rw [end_overflow len b (by omega)]
      simp
  · rw [begin_overflow a (by omega)]
    simp

theorem range_success_iff {T} (R : RangeBounds T Usize) (r : T) (len : Usize)
    (a b : Bound Usize) (ha : R.start_bound r = .ok a) (hb : R.end_bound r = .ok b) :
    (∃ out, bytes_range.range R r len = .ok out ∧
      out.1.val = beginNat a ∧ out.2.val = endNat len b) ↔ Valid a b len := by
  constructor
  · rintro ⟨out,ho,hfirst,hlast⟩
    by_contra h
    have hf := range_invalid R r len a b ha hb h
    simp_all
  · exact range_success R r len a b ha hb

end range_proofs
