import IntegerCore
import VarintSpec
import RequiredSpace
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace IntegerEncodingEncode

def contByte (n : U64) : U8 := UScalar.mk ((128 : BitVec 8) ||| n.bv.setWidth 8)

theorem contByte_val (n : U64) : (contByte n).val = n.val % 128 + 128 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hn : n.val % 128 < 128 := Nat.mod_lt _ (by decide)
  change ((2^7 ||| (n.val % 2^8))).testBit i = (n.val % 2^7 + 2^7).testBit i
  by_cases hi : i < 7
  · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hi]
    have h128 : Nat.testBit (2^7) i = false := by
      rw [Nat.testBit_two_pow]
      simp only [show ¬7=i by omega,decide_false]
    have hm8 : (n.val % 2^8).testBit i = n.val.testBit i := by
      rw [Nat.testBit_mod_two_pow]; simp only [show i<8 by omega,decide_true,Bool.true_and]
    have hm7 : (n.val % 2^7).testBit i = n.val.testBit i := by
      rw [Nat.testBit_mod_two_pow]; simp only [hi,decide_true,Bool.true_and]
    rw [Nat.testBit_or,h128,hm8,hm7]
    rfl
  · by_cases he : i = 7
    · subst i
      have hz : (n.val % 128).testBit 7 = false := Nat.testBit_lt_two_pow hn
      rw [Nat.add_comm, Nat.testBit_two_pow_add_eq]
      rw [Nat.testBit_or,show Nat.testBit (2^7) 7 = true by decide]
      simp only [Bool.true_or]
      exact (congrArg Bool.not hz).symm
    · have h0 : (128 ||| (n.val % 256)) < 2^8 := by
        apply Nat.or_lt_two_pow <;> omega
      have h1 : n.val % 128 + 128 < 2^8 := by omega
      have hpow : 2^8 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le h0 hpow)).trans
        (Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 hpow)).symm

theorem body_spec (dst : Slice U8) (n : U64) (i : Usize)
    (hn : 128 ≤ n.val) (hi : i.val < dst.val.length) :
    WP.spec (integer_encoding.U64.Insts.Integer_encodingVarintVarInt.encode_var_loop.body dst n i)
      (fun out => ∃ dst' n' i', out = .cont (dst',n',i') ∧
        dst'.val = dst.val.set i.val (contByte n) ∧ n'.val = n.val / 128 ∧ i'.val = i.val+1) := by
  unfold integer_encoding.U64.Insts.Integer_encodingVarintVarInt.encode_var_loop.body
  simp only [UScalar.le_equiv,show (128#u64 : U64).val = 128 by rfl,hn,↓reduceIte]
  step
  step
  step
  step
  step
  refine ⟨s,n1,i3,rfl,?_,?_,i3_post⟩
  · have hb : i2 = contByte n := by
      apply (UScalar.eq_equiv_bv_eq _ _).mpr
      rw [i2_post1,i1_post]
      unfold integer_encoding.varint.MSB contByte UScalar.cast
      rfl
    rw [s_post,hb]
    exact Slice.set_val_eq _ _ _
  · simpa only [Nat.shiftRight_eq_div_pow] using n1_post

open IntegerEncodingSpec

theorem get_set (xs : List U8) (i j : Nat) (b : U8) (hi : i < xs.length) :
    (xs.set i b)[j]! = if i=j then b else xs[j]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i=j
  · subst j; simp [hi]
  · simp [h]

def Inv (original : Slice U8) (u k : Nat) (x : Slice U8 × U64 × Usize) : Prop :=
  x.1.val.length = original.val.length ∧
  x.2.1.val = u / 128^x.2.2.val ∧
  x.2.2.val + uLen x.2.1.val = k ∧
  (∀ j, j < x.2.2.val → x.1.val[j]!.val = (u / 128^j)%128+128) ∧
  (∀ j, x.2.2.val ≤ j → x.1.val[j]! = original.val[j]!)

theorem loop_spec (dst : Slice U8) (u : U64)
    (hcap : uLen u.val ≤ dst.val.length) :
    WP.spec (integer_encoding.U64.Insts.Integer_encodingVarintVarInt.encode_var_loop dst u 0#usize)
      (fun out => Inv dst u.val (uLen u.val) out ∧ out.2.1.val < 128) := by
  unfold integer_encoding.U64.Insts.Integer_encodingVarintVarInt.encode_var_loop
  apply loop.spec_decr_nat
    (measure := fun x : Slice U8 × U64 × Usize => x.2.1.val)
    (inv := Inv dst u.val (uLen u.val))
  · intro x hx
    rcases x with ⟨d,n,i⟩
    dsimp only [Inv] at hx
    rcases hx with ⟨hlen,hn,hcount,hpre,hsuf⟩
    by_cases hc : 128 ≤ n.val
    · have hi : i.val < d.val.length := by
        have hpos := uLen_pos n.val
        omega
      have hb := body_spec d n i hc hi
      apply WP.spec_mono hb
      rintro out ⟨d',n',i',rfl,hd,hn',hi'⟩
      refine ⟨?_, ?_⟩
      · dsimp only [Inv]
        refine ⟨?_,?_,?_,?_,?_⟩
        · rw [hd,List.length_set,hlen]
        · rw [hn',hn,hi',Nat.pow_succ,Nat.div_div_eq_div_mul]
        · rw [hi',hn']
          have hs := uLen_step hc
          omega
        · intro j hj
          rw [hd,get_set _ _ _ _ hi]
          by_cases he : i.val=j
          · simp only [he,↓reduceIte]
            rw [contByte_val,hn,he]
          · simp only [he,↓reduceIte]
            exact hpre j (by omega)
        · intro j hj
          rw [hd,get_set _ _ _ _ hi]
          have he : i.val≠j := by omega
          simp only [he,↓reduceIte]
          exact hsuf j (by omega)
      · rw [hn']
        exact Nat.div_lt_self (by omega) (by decide)
    · unfold integer_encoding.U64.Insts.Integer_encodingVarintVarInt.encode_var_loop.body
      simp only [UScalar.le_equiv,show (128#u64 : U64).val=128 by rfl,hc,↓reduceIte,WP.spec_ok]
      exact ⟨⟨hlen,hn,hcount,hpre,hsuf⟩,by omega⟩
  · refine ⟨rfl,?_,?_,?_,?_⟩ <;> simp

def Encoded (u : Nat) (original : Slice U8) (out : Usize × Slice U8) : Prop :=
  out.1.val = uLen u ∧
  out.2.val.length = original.val.length ∧
  (∀ j, j < uLen u → out.2.val[j]!.val =
    (u / 128^j)%128 + if j+1 < uLen u then 128 else 0) ∧
  (∀ j, uLen u ≤ j → out.2.val[j]! = original.val[j]!)

theorem u64_total (u : U64) (dst : Slice U8) (hcap : uLen u.val ≤ dst.val.length) :
    ∃ out, integer_encoding.U64.Insts.Integer_encodingVarintVarInt.encode_var u dst = .ok out ∧
      Encoded u.val dst out := by
  apply IntegerRequiredSpace.total_result
  unfold integer_encoding.U64.Insts.Integer_encodingVarintVarInt.encode_var
  obtain ⟨space, hspace, hspaceval⟩ := IntegerRequiredSpace.u64_required_space u
  rw [hspace]
  step
  obtain ⟨⟨d,value,i⟩, hlo, hInv, hnlt⟩ := IntegerRequiredSpace.total_result (loop_spec dst u hcap)
  rw [hlo]
  dsimp only [Inv] at hInv
  rcases hInv with ⟨hlen,hn,hcount,hpre,hsuf⟩
  have hlast : i.val+1 = uLen u.val := by rw [uLen_small hnlt] at hcount; exact hcount
  have hi : i.val < d.val.length := by omega
  step
  step
  step
  dsimp only [Encoded,Prod.fst,Prod.snd]
  refine ⟨by omega,?_,?_,?_⟩
  · rw [dst2_post,Slice.set_val_eq,List.length_set,hlen]
  · intro j hj
    rw [dst2_post,Slice.set_val_eq,get_set _ _ _ _ hi]
    by_cases he : i.val=j
    · simp only [he,↓reduceIte]
      have hv : dst1.val=value.val := by
        rw [n]
        change value.val % 256 = value.val
        exact Nat.mod_eq_of_lt (by dsimp only at hnlt; omega)
      rw [hv,hn,he]
      have hjlast : ¬j+1 < uLen u.val := by omega
      simp only [hjlast,↓reduceIte,Nat.add_zero,Nat.mod_eq_of_lt (by simpa [hn,he] using hnlt)]
    · simp only [he,↓reduceIte]
      rw [hpre j (by omega)]
      have hjlast : j+1 < uLen u.val := by omega
      simp only [hjlast,↓reduceIte]
  · intro j hj
    rw [dst2_post,Slice.set_val_eq,get_set _ _ _ _ hi]
    have he : i.val≠j := by omega
    simp only [he,↓reduceIte]
    exact hsuf j (by omega)

theorem i64_total (v : I64) (dst : Slice U8)
    (hcap : uLen (zigzag v.val) ≤ dst.val.length) :
    ∃ out, integer_encoding.I64.Insts.Integer_encodingVarintVarInt.encode_var v dst = .ok out ∧
      Encoded (zigzag v.val) dst out := by
  obtain ⟨z,hz,hzval⟩ := integer_encoding.zigzag_encode_spec v
  obtain ⟨out,ho,henc⟩ := u64_total z dst (by simpa [hzval] using hcap)
  refine ⟨out,?_,by simpa [hzval] using henc⟩
  have he : integer_encoding.I64.Insts.Integer_encodingVarintVarInt.encode_var v dst =
      integer_encoding.U64.Insts.Integer_encodingVarintVarInt.encode_var z dst := by
    simp only [integer_encoding.I64.Insts.Integer_encodingVarintVarInt.encode_var,
      integer_encoding.I64.Insts.Integer_encodingVarintVarInt.required_space,
      integer_encoding.varint.required_encoded_space_signed,hz,
      integer_encoding.U64.Insts.Integer_encodingVarintVarInt.encode_var,
      integer_encoding.U64.Insts.Integer_encodingVarintVarInt.required_space]
    simp
    rfl
  exact he.trans ho

theorem u8_total (v : U8) (dst : Slice U8)
    (hcap : uLen v.val ≤ dst.val.length) :
    ∃ out, integer_encoding.U8.Insts.Integer_encodingVarintVarInt.encode_var v dst = .ok out ∧
      Encoded v.val dst out := by
  apply IntegerRequiredSpace.total_result
  unfold integer_encoding.U8.Insts.Integer_encodingVarintVarInt.encode_var
  step
  obtain ⟨out,ho,henc⟩ := u64_total i dst (by simpa [i_post] using hcap)
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using henc

theorem u16_total (v : U16) (dst : Slice U8)
    (hcap : uLen v.val ≤ dst.val.length) :
    ∃ out, integer_encoding.U16.Insts.Integer_encodingVarintVarInt.encode_var v dst = .ok out ∧
      Encoded v.val dst out := by
  apply IntegerRequiredSpace.total_result
  unfold integer_encoding.U16.Insts.Integer_encodingVarintVarInt.encode_var
  step
  obtain ⟨out,ho,henc⟩ := u64_total i dst (by simpa [i_post] using hcap)
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using henc

theorem u32_total (v : U32) (dst : Slice U8)
    (hcap : uLen v.val ≤ dst.val.length) :
    ∃ out, integer_encoding.U32.Insts.Integer_encodingVarintVarInt.encode_var v dst = .ok out ∧
      Encoded v.val dst out := by
  apply IntegerRequiredSpace.total_result
  unfold integer_encoding.U32.Insts.Integer_encodingVarintVarInt.encode_var
  step
  obtain ⟨out,ho,henc⟩ := u64_total i dst (by simpa [i_post] using hcap)
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using henc

theorem usize_total (v : Usize) (dst : Slice U8)
    (hcap : uLen v.val ≤ dst.val.length) :
    ∃ out, integer_encoding.Usize.Insts.Integer_encodingVarintVarInt.encode_var v dst = .ok out ∧
      Encoded v.val dst out := by
  apply IntegerRequiredSpace.total_result
  unfold integer_encoding.Usize.Insts.Integer_encodingVarintVarInt.encode_var
  step
  obtain ⟨out,ho,henc⟩ := u64_total i dst (by simpa [i_post] using hcap)
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using henc

theorem i8_total (v : I8) (dst : Slice U8)
    (hcap : uLen (zigzag v.val) ≤ dst.val.length) :
    ∃ out, integer_encoding.I8.Insts.Integer_encodingVarintVarInt.encode_var v dst = .ok out ∧
      Encoded (zigzag v.val) dst out := by
  apply IntegerRequiredSpace.total_result
  unfold integer_encoding.I8.Insts.Integer_encodingVarintVarInt.encode_var
  step
  obtain ⟨out,ho,henc⟩ := i64_total i dst (by simpa [i_post] using hcap)
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using henc

theorem i16_total (v : I16) (dst : Slice U8)
    (hcap : uLen (zigzag v.val) ≤ dst.val.length) :
    ∃ out, integer_encoding.I16.Insts.Integer_encodingVarintVarInt.encode_var v dst = .ok out ∧
      Encoded (zigzag v.val) dst out := by
  apply IntegerRequiredSpace.total_result
  unfold integer_encoding.I16.Insts.Integer_encodingVarintVarInt.encode_var
  step
  obtain ⟨out,ho,henc⟩ := i64_total i dst (by simpa [i_post] using hcap)
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using henc

theorem i32_total (v : I32) (dst : Slice U8)
    (hcap : uLen (zigzag v.val) ≤ dst.val.length) :
    ∃ out, integer_encoding.I32.Insts.Integer_encodingVarintVarInt.encode_var v dst = .ok out ∧
      Encoded (zigzag v.val) dst out := by
  apply IntegerRequiredSpace.total_result
  unfold integer_encoding.I32.Insts.Integer_encodingVarintVarInt.encode_var
  step
  obtain ⟨out,ho,henc⟩ := i64_total i dst (by simpa [i_post] using hcap)
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using henc

theorem isize_total (v : Isize) (dst : Slice U8)
    (hcap : uLen (zigzag v.val) ≤ dst.val.length) :
    ∃ out, integer_encoding.Isize.Insts.Integer_encodingVarintVarInt.encode_var v dst = .ok out ∧
      Encoded (zigzag v.val) dst out := by
  apply IntegerRequiredSpace.total_result
  unfold integer_encoding.Isize.Insts.Integer_encodingVarintVarInt.encode_var
  step
  obtain ⟨out,ho,henc⟩ := i64_total i dst (by simpa [i_post] using hcap)
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using henc

end IntegerEncodingEncode
