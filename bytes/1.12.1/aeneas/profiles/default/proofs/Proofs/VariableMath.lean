import Proofs.VariableReads
open Aeneas Aeneas.Std Result
/-! Arithmetic correspondence helpers for the independent variable-width
specification. These prove positional-sum and padding equations only; they do
not establish any reader implementation or consumption contract. In particular,
the signed-disagreement lemmas compare mathematical interpretations, not an
actual checked-reader execution. -/
namespace bytes_numeric

theorem setSlice_zeros_prefix (n : Nat) (bs : List U8) (h : bs.length ≤ n) :
    (List.replicate n (0#u8)).setSlice! 0 bs =
      bs ++ List.replicate (n-bs.length) (0#u8) := by
  simp [List.setSlice!,Nat.min_eq_left h]

theorem setSlice_zeros_suffix (n : Nat) (bs : List U8) (h : bs.length ≤ n) :
    (List.replicate n (0#u8)).setSlice! (n-bs.length) bs =
      List.replicate (n-bs.length) (0#u8) ++ bs := by
  have hn : n-(n-bs.length) = bs.length := by omega
  simp [List.setSlice!,hn,show n-bs.length+bs.length=n by omega]

theorem leValue_fill_zeros (n : Nat) (bs : List U8) (h : bs.length ≤ n) :
    leValue ((List.replicate n (0#u8)).setSlice! 0 bs) = leValue bs := by
  rw [setSlice_zeros_prefix n bs h,leValue_pad]

theorem beValue_fill_zeros (n : Nat) (bs : List U8) (h : bs.length ≤ n) :
    beValue ((List.replicate n (0#u8)).setSlice! (n-bs.length) bs) = beValue bs := by
  rw [setSlice_zeros_suffix n bs h,beValue_pad]
theorem leValue_weighted_sum_aux (bs : List U8) (k : Nat) :
    (bs.mapIdx (fun i b => b.val * 256^(i+k))).sum = 256^k * leValue bs := by
  induction bs generalizing k with
  | nil => simp [leValue]
  | cons b bs ih =>
    simp only [List.mapIdx_cons,List.sum_cons,Nat.zero_add,Nat.add_assoc]
    rw [ih (1+k)]
    simp only [show 1+k=k+1 by omega,Nat.pow_succ,leValue]
    ring

theorem leValue_weighted_sum (bs : List U8) :
    leValue bs = (bs.mapIdx (fun i b => b.val * 256^i)).sum := by
  simpa using (leValue_weighted_sum_aux bs 0).symm

theorem beValue_cons (b : U8) (bs : List U8) :
    beValue (b::bs) = b.val * 256^bs.length + beValue bs := by
  unfold beValue
  rw [List.reverse_cons,leValue_append]
  simp only [List.length_reverse,leValue]
  ring

theorem beValue_weighted_sum (bs : List U8) :
    beValue bs = (bs.mapIdx (fun i b => b.val * 256^(bs.length-1-i))).sum := by
  induction bs with
  | nil => simp [beValue,leValue]
  | cons b bs ih =>
    rw [beValue_cons,List.mapIdx_cons,List.sum_cons]
    simp only [List.length_cons,Nat.add_sub_cancel,Nat.sub_zero]
    have hfun : (fun (i : Nat) (b : U8) => b.val * 256^(bs.length-(i+1))) =
        (fun i b => b.val * 256^(bs.length-1-i)) := by
      funext i b
      congr 2
      omega
    rw [hfun,← ih]

theorem signedByteValue_beValue (bs : List U8) :
    bytes.signedByteValue (beValue bs) bs.length =
      if bs.length = 0 then 0
      else if beValue bs < 2^(8*bs.length-1) then (beValue bs : Int)
      else (beValue bs : Int) - (2^(8*bs.length) : Nat) := by
  simpa [beValue] using signedByteValue_leValue bs.reverse

theorem signed64_full_leValue (bs : List U8) (hn : bs.length = 8) :
    signed64 (leValue bs) = bytes.signedByteValue (leValue bs) 8 := by
  rw [← hn,signedByteValue_leValue]
  norm_num [signed64,hn]

theorem signed64_full_beValue (bs : List U8) (hn : bs.length = 8) :
    signed64 (beValue bs) = bytes.signedByteValue (beValue bs) 8 := by
  simpa only [beValue] using signed64_full_leValue bs.reverse (by simpa using hn)

theorem signed_short_math_discrepancy :
    signed64 (leValue [255#u8]) = 255 ∧
      bytes.signedByteValue (leValue [255#u8]) 1 = -1 := by
  norm_num [signed64,leValue,bytes.signedByteValue]

theorem signed64_short_leValue_disagrees (bs : List U8)
    (hpos : 0 < bs.length) (hshort : bs.length < 8)
    (hsign : 2^(8*bs.length-1) ≤ leValue bs) :
    signed64 (leValue bs) ≠ bytes.signedByteValue (leValue bs) bs.length := by
  rw [signed64_short_leValue bs hshort,signedByteValue_leValue]
  have hzero : bs.length ≠ 0 := by omega
  simp only [ite_eq_right hzero,ite_eq_right (Nat.not_lt.mpr hsign)]
  have hpow : 0 < 2^(8*bs.length) := Nat.two_pow_pos _
  omega

theorem signed64_short_beValue_disagrees (bs : List U8)
    (hpos : 0 < bs.length) (hshort : bs.length < 8)
    (hsign : 2^(8*bs.length-1) ≤ beValue bs) :
    signed64 (beValue bs) ≠ bytes.signedByteValue (beValue bs) bs.length := by
  simpa only [beValue,List.length_reverse] using signed64_short_leValue_disagrees
    bs.reverse (by simpa using hpos) (by simpa using hshort) (by simpa [beValue] using hsign)

end bytes_numeric
