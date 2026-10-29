import CrcStage2.Funs
import CrcProofs.Util
open Aeneas Aeneas.Std Result
namespace CrcStage2

def scalarEquiv (ty : UScalarTy) : UScalar ty ≃ BitVec ty.numBits where
  toFun := UScalar.bv
  invFun := UScalar.mk
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

theorem scalar_card (ty : UScalarTy) : Nat.card (UScalar ty) = 2^ty.numBits := by
  rw [Nat.card_congr (scalarEquiv ty)]
  rw [Nat.card_congr ((BitVec.equivFin (m := ty.numBits)).toEquiv)]
  exact Nat.card_fin (2^ty.numBits)

theorem scalar_type_neq {a b : UScalarTy} (h : 2^a.numBits ≠ 2^b.numBits) :
    UScalar a ≠ UScalar b := by
  intro heq
  apply h
  have hc := congrArg Nat.card heq
  simpa only [scalar_card] using hc

 theorem bitreverse_u8 (x : U8) : core.intrinsics.bitreverse core.marker.CopyU8 x =
    .ok (UScalar.mk x.bv.reverse) := by
  simp [core.intrinsics.bitreverse]

@[simp] theorem reverse_bits_u8 (x : U8) : core.num.U8.reverse_bits x =
    .ok (UScalar.mk x.bv.reverse) := bitreverse_u8 x

 theorem bitreverse_u16 (x : U16) : core.intrinsics.bitreverse core.marker.CopyU16 x =
    .ok (UScalar.mk x.bv.reverse) := by
  have h8 : U16 ≠ U8 := scalar_type_neq (by decide)
  simp [core.intrinsics.bitreverse, h8]

@[simp] theorem reverse_bits_u16 (x : U16) : core.num.U16.reverse_bits x =
    .ok (UScalar.mk x.bv.reverse) := bitreverse_u16 x

 theorem bitreverse_u32 (x : U32) : core.intrinsics.bitreverse core.marker.CopyU32 x =
    .ok (UScalar.mk x.bv.reverse) := by
  have h8 : U32 ≠ U8 := scalar_type_neq (by decide)
  have h16 : U32 ≠ U16 := scalar_type_neq (by decide)
  simp [core.intrinsics.bitreverse, h8, h16]

@[simp] theorem reverse_bits_u32 (x : U32) : core.num.U32.reverse_bits x =
    .ok (UScalar.mk x.bv.reverse) := bitreverse_u32 x

 theorem bitreverse_u64 (x : U64) : core.intrinsics.bitreverse core.marker.CopyU64 x =
    .ok (UScalar.mk x.bv.reverse) := by
  have h8 : U64 ≠ U8 := scalar_type_neq (by decide)
  have h16 : U64 ≠ U16 := scalar_type_neq (by decide)
  have h32 : U64 ≠ U32 := scalar_type_neq (by decide)
  simp [core.intrinsics.bitreverse, h8, h16, h32]

@[simp] theorem reverse_bits_u64 (x : U64) : core.num.U64.reverse_bits x =
    .ok (UScalar.mk x.bv.reverse) := bitreverse_u64 x

 theorem bitreverse_u128 (x : U128) : core.intrinsics.bitreverse core.marker.CopyU128 x =
    .ok (UScalar.mk x.bv.reverse) := by
  have h8 : U128 ≠ U8 := scalar_type_neq (by decide)
  have h16 : U128 ≠ U16 := scalar_type_neq (by decide)
  have h32 : U128 ≠ U32 := scalar_type_neq (by decide)
  have h64 : U128 ≠ U64 := scalar_type_neq (by decide)
  simp [core.intrinsics.bitreverse, h8, h16, h32, h64]

@[simp] theorem reverse_bits_u128 (x : U128) : core.num.U128.reverse_bits x =
    .ok (UScalar.mk x.bv.reverse) := bitreverse_u128 x

def rawInit {n : Nat} (w : Nat) (refin : Bool) (v : BitVec n) : BitVec n :=
  if refin then v.reverse >>> (n-w) else v <<< (n-w)

def rawFinalize {n : Nat} (w : Nat) (refin refout : Bool) (xorout v : BitVec n) : BitVec n :=
  let v1 := if refin ^^ refout then v.reverse else v
  (if refout then v1 else v1 >>> (n-w)) ^^^ xorout

 theorem init8_spec (a : crc_catalog.Algorithm U8) (v : U8)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 8) :
    ∃ out, crc8.init a v = .ok out ∧ out.bv = rawInit a.width.val a.refin v.bv := by
  apply crc.total_result
  unfold crc8.init
  split
  · simp only [reverse_bits_u8, bind_ok]
    step
    step
    simp only [rawInit, UScalarTy.numBits]
    split
    · have hshift : i1.val = 8 - a.width.val := by omega
      simpa only [hshift] using value_post1
    · contradiction
  · step
    step
    simp only [rawInit, UScalarTy.numBits]
    split
    · contradiction
    · have hshift : i.val = 8 - a.width.val := by omega
      simpa only [hshift] using value_post1
theorem finalize8_spec (a : crc_catalog.Algorithm U8) (v : U8)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 8) :
    ∃ out, crc8.finalize a v = .ok out ∧
      out.bv = rawFinalize a.width.val a.refin a.refout a.xorout.bv v.bv := by
  apply crc.total_result
  unfold crc8.finalize
  cases hri : a.refin <;> cases hro : a.refout <;>
    simp only [hri, hro, Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, reverse_bits_u8, bind_ok, rawFinalize]
  all_goals try {simp only [WP.spec_ok]; rfl}
  all_goals step
  all_goals step
  all_goals
    rename_i sh hsh hb
    apply congrArg (fun x : BitVec 8 => x ^^^ a.xorout.bv)
    simpa only [hsh] using crc2_post1
 theorem init16_spec (a : crc_catalog.Algorithm U16) (v : U16)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 16) :
    ∃ out, crc16.init a v = .ok out ∧ out.bv = rawInit a.width.val a.refin v.bv := by
  apply crc.total_result
  unfold crc16.init
  split
  · simp only [reverse_bits_u16, bind_ok]
    step
    step
    simp only [rawInit, UScalarTy.numBits]
    split
    · have hshift : i1.val = 16 - a.width.val := by omega
      simpa only [hshift] using value_post1
    · contradiction
  · step
    step
    simp only [rawInit, UScalarTy.numBits]
    split
    · contradiction
    · have hshift : i.val = 16 - a.width.val := by omega
      simpa only [hshift] using value_post1
theorem finalize16_spec (a : crc_catalog.Algorithm U16) (v : U16)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 16) :
    ∃ out, crc16.finalize a v = .ok out ∧
      out.bv = rawFinalize a.width.val a.refin a.refout a.xorout.bv v.bv := by
  apply crc.total_result
  unfold crc16.finalize
  cases hri : a.refin <;> cases hro : a.refout <;>
    simp only [hri, hro, Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, reverse_bits_u16, bind_ok, rawFinalize]
  all_goals try {simp only [WP.spec_ok]; rfl}
  all_goals step
  all_goals step
  all_goals
    rename_i sh hsh hb
    apply congrArg (fun x : BitVec 16 => x ^^^ a.xorout.bv)
    simpa only [hsh] using crc2_post1

 theorem init32_spec (a : crc_catalog.Algorithm U32) (v : U32)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 32) :
    ∃ out, crc32.init a v = .ok out ∧ out.bv = rawInit a.width.val a.refin v.bv := by
  apply crc.total_result
  unfold crc32.init
  split
  · simp only [reverse_bits_u32, bind_ok]
    step
    step
    simp only [rawInit, UScalarTy.numBits]
    split
    · have hshift : i1.val = 32 - a.width.val := by omega
      simpa only [hshift] using value_post1
    · contradiction
  · step
    step
    simp only [rawInit, UScalarTy.numBits]
    split
    · contradiction
    · have hshift : i.val = 32 - a.width.val := by omega
      simpa only [hshift] using value_post1
theorem finalize32_spec (a : crc_catalog.Algorithm U32) (v : U32)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 32) :
    ∃ out, crc32.finalize a v = .ok out ∧
      out.bv = rawFinalize a.width.val a.refin a.refout a.xorout.bv v.bv := by
  apply crc.total_result
  unfold crc32.finalize
  cases hri : a.refin <;> cases hro : a.refout <;>
    simp only [hri, hro, Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, reverse_bits_u32, bind_ok, rawFinalize]
  all_goals try {simp only [WP.spec_ok]; rfl}
  all_goals step
  all_goals step
  all_goals
    rename_i sh hsh hb
    apply congrArg (fun x : BitVec 32 => x ^^^ a.xorout.bv)
    simpa only [hsh] using crc2_post1

 theorem init64_spec (a : crc_catalog.Algorithm U64) (v : U64)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 64) :
    ∃ out, crc64.init a v = .ok out ∧ out.bv = rawInit a.width.val a.refin v.bv := by
  apply crc.total_result
  unfold crc64.init
  split
  · simp only [reverse_bits_u64, bind_ok]
    step
    step
    simp only [rawInit, UScalarTy.numBits]
    split
    · have hshift : i1.val = 64 - a.width.val := by omega
      simpa only [hshift] using value_post1
    · contradiction
  · step
    step
    simp only [rawInit, UScalarTy.numBits]
    split
    · contradiction
    · have hshift : i.val = 64 - a.width.val := by omega
      simpa only [hshift] using value_post1
theorem finalize64_spec (a : crc_catalog.Algorithm U64) (v : U64)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 64) :
    ∃ out, crc64.finalize a v = .ok out ∧
      out.bv = rawFinalize a.width.val a.refin a.refout a.xorout.bv v.bv := by
  apply crc.total_result
  unfold crc64.finalize
  cases hri : a.refin <;> cases hro : a.refout <;>
    simp only [hri, hro, Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, reverse_bits_u64, bind_ok, rawFinalize]
  all_goals try {simp only [WP.spec_ok]; rfl}
  all_goals step
  all_goals step
  all_goals
    rename_i sh hsh hb
    apply congrArg (fun x : BitVec 64 => x ^^^ a.xorout.bv)
    simpa only [hsh] using crc2_post1

 theorem init128_spec (a : crc_catalog.Algorithm U128) (v : U128)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 128) :
    ∃ out, crc128.init a v = .ok out ∧ out.bv = rawInit a.width.val a.refin v.bv := by
  apply crc.total_result
  unfold crc128.init
  split
  · simp only [reverse_bits_u128, bind_ok]
    step
    step
    simp only [rawInit, UScalarTy.numBits]
    split
    · have hshift : i1.val = 128 - a.width.val := by omega
      simpa only [hshift] using value_post1
    · contradiction
  · step
    step
    simp only [rawInit, UScalarTy.numBits]
    split
    · contradiction
    · have hshift : i.val = 128 - a.width.val := by omega
      simpa only [hshift] using value_post1
theorem finalize128_spec (a : crc_catalog.Algorithm U128) (v : U128)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 128) :
    ∃ out, crc128.finalize a v = .ok out ∧
      out.bv = rawFinalize a.width.val a.refin a.refout a.xorout.bv v.bv := by
  apply crc.total_result
  unfold crc128.finalize
  cases hri : a.refin <;> cases hro : a.refout <;>
    simp only [hri, hro, Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, reverse_bits_u128, bind_ok, rawFinalize]
  all_goals try {simp only [WP.spec_ok]; rfl}
  all_goals step
  all_goals step
  all_goals
    rename_i sh hsh hb
    apply congrArg (fun x : BitVec 128 => x ^^^ a.xorout.bv)
    simpa only [hsh] using crc2_post1

end CrcStage2
