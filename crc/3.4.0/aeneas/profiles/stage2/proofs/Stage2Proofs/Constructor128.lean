import Stage2Proofs.Update128
import Stage2Proofs.Public128
import Stage2Proofs.ByteMathWide
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace CrcConstructor128
abbrev Table128 := Array (Array U128 256#usize) 1#usize

def tableRead (t : Table128) (b : U8) : U128 :=
  t.val[0].val[b.val]'(by have h := b.hmax; scalar_tac)

def Prefix (poly : U128) (t : Table128) (n : Nat) : Prop :=
  ∀ b : U8, b.val < n → (tableRead t b).bv = CrcCanonicalWide.byteStep poly.bv 0 b.bv

theorem utility (poly value : U128) (hb : value.val < 256) :
    ∃ out, CrcBody.util.crc128 poly false value = .ok out ∧
      out.bv = CrcCanonicalWide.byteStep poly.bv 0 (value.bv.setWidth 8) := by
  obtain ⟨out,hout,hmodel⟩ := crc.crc128_polynomial_spec poly value false
  refine ⟨out,hout,?_⟩
  rw [CrcCanonicalWide.byteStep_injection (by decide), CrcCanonicalWide.encodeByte]
  have heq : (value.bv.setWidth 8).setWidth 128 = value.bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, UScalar.bv_toNat]
    change (value.val % 256) % 340282366920938463463374607431768211456 = value.val
    rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega)]
  rw [heq]
  simpa using hmodel

theorem body_spec (poly : U128) (t : Table128) (i : Usize) (hi : i.val < 256)
    (hp : Prefix poly t i.val) :
    WP.spec (CrcBody.table.crc128_table_loop0.body false poly t i)
      (fun out => ∃ t' j, out = .cont (t',j) ∧ j.val = i.val+1 ∧ Prefix poly t' j.val) := by
  unfold CrcBody.table.crc128_table_loop0.body
  simp only [UScalar.lt_equiv, show (256#usize : Usize).val = 256 by rfl, hi, ↓reduceIte,
    show (1#usize : Usize) > 0#usize by decide]
  step
  have hi1 : i1.val = i.val := by scalar_tac
  obtain ⟨v,hv,hcanon⟩ := utility poly i1 (by omega)
  rw [hv]
  simp only [bind_ok]
  step
  step
  step
  refine ⟨_, i3, rfl, i3_post, ?_⟩
  intro b hb
  simp only [Prefix] at hp
  have hzero : (0#usize : Usize).val = 0 := rfl
  simp only [tableRead, a_post, index_mut_back_post, a1_post,
    Array.set_val_eq, hzero, List.getElem_set, ↓reduceIte]
  split
  · rename_i heq
    have he : i1.bv.setWidth 8 = b.bv := by
      apply BitVec.eq_of_toNat_eq
      change i1.val % 256 = b.val
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simpa only [he] using hcanon
  · apply hp b
    omega
theorem loop_spec (poly : U128) (t : Table128) :
    WP.spec (CrcBody.table.crc128_table_loop0 false poly t 0#usize)
      (fun out => Prefix poly out 256) := by
  unfold CrcBody.table.crc128_table_loop0
  apply loop.spec_decr_nat
    (measure := fun x : Table128 × Usize => 256-x.2.val)
    (inv := fun x : Table128 × Usize => x.2.val ≤ 256 ∧ Prefix poly x.1 x.2.val)
  · intro x hx
    rcases x with ⟨t,i⟩
    dsimp only at hx
    obtain ⟨hi,hp⟩ := hx
    by_cases hlt : i.val < 256
    · apply WP.spec_mono (body_spec poly t i hlt hp)
      intro out hout
      obtain ⟨t',j,rfl,hj,hp'⟩ := hout
      dsimp only
      exact ⟨⟨by omega,hp'⟩, by omega⟩
    · unfold CrcBody.table.crc128_table_loop0.body
      simp only [UScalar.lt_equiv, show (256#usize : Usize).val = 256 by rfl, hlt,
        ↓reduceIte, WP.spec_ok]
      have heq : i.val = 256 := by omega
      simpa only [heq] using hp
  · simp only [show (0#usize : Usize).val = 0 by rfl]
    exact ⟨by omega, by intro b hb; omega⟩

theorem table_spec (poly : U128) :
    ∃ out, CrcBody.table.crc128_table 1#usize 128#u8 poly false = .ok out ∧ Prefix poly out 256 := by
  apply crc.total_result
  unfold CrcBody.table.crc128_table
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hzero : ((128#u8 - 128#u8) : Result U8) = .ok 0#u8 := by rfl
  simp only [hzero, bind_ok]
  step
  have hp : poly1 = poly := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    simpa only [show (0#u8 : U8).val = 0 by rfl, BitVec.shiftLeft_zero] using poly1_post1
  rw [hp]
  apply WP.spec_bind (loop_spec poly (Array.repeat 1#usize (Array.repeat 256#usize 0#u128)))
  intro out hout
  simp only [show ¬(1#usize : Usize) > 1#usize by decide, ↓reduceIte, WP.spec_ok]
  exact hout


theorem new128_coherent_nonref (a : CrcBody.crc_catalog.Algorithm U128)
    (ha : CrcPublic128.NonRef128 a) :
    ∃ out : CrcPublic128.Crc128, CrcBody.crc128.CrcU128Table.new 1#usize a = .ok out ∧
      out.algorithm = a ∧ CrcPublic128.Coherent128 out := by
  obtain ⟨t,ht,hp⟩ := table_spec a.poly
  obtain ⟨hw,hri⟩ := ha
  refine ⟨⟨a,t⟩, ?_, rfl, ?_⟩
  · simp only [CrcBody.crc128.CrcU128Table.new, hw, hri, ht, bind_ok]
  · intro b
    apply hp b
    have h := b.hmax
    scalar_tac

theorem new_checksum128_nonref (a : CrcBody.crc_catalog.Algorithm U128)
    (ha : CrcPublic128.NonRef128 a) (bytes : Slice U8) :
    ∃ self : CrcPublic128.Crc128, CrcBody.crc128.CrcU128Table.new 1#usize a = .ok self ∧
      ∃ out, CrcBody.crc128.CrcU128Table.checksum self bytes = .ok out ∧
      out.bv = (if a.refout then
        (CrcCanonicalWide.run a.poly.bv a.init.bv (bytes.val.map UScalar.bv)).reverse
        else CrcCanonicalWide.run a.poly.bv a.init.bv (bytes.val.map UScalar.bv)) ^^^ a.xorout.bv := by
  obtain ⟨self,hs,haeq,hcoh⟩ := new128_coherent_nonref a ha
  refine ⟨self,hs,?_⟩
  have hw : CrcPublic128.NonRef128 self.algorithm := haeq ▸ ha
  simpa only [haeq] using CrcPublic128.checksum_canonical self bytes hw hcoh

theorem new_digest_protocol128_nonref (a : CrcBody.crc_catalog.Algorithm U128)
    (ha : CrcPublic128.NonRef128 a) (initial : U128) (bytes : Slice U8) :
    ∃ self : CrcPublic128.Crc128, CrcBody.crc128.CrcU128Table.new 1#usize a = .ok self ∧
      ∃ start finish out,
      CrcBody.crc128.CrcU128Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc128.DigestAU128Table.update start bytes = .ok finish ∧
      CrcBody.crc128.DigestAU128Table.finalize finish = .ok out ∧
      out.bv = (if a.refout then
        (CrcCanonicalWide.run a.poly.bv initial.bv (bytes.val.map UScalar.bv)).reverse
        else CrcCanonicalWide.run a.poly.bv initial.bv (bytes.val.map UScalar.bv)) ^^^ a.xorout.bv := by
  obtain ⟨self,hs,haeq,hcoh⟩ := new128_coherent_nonref a ha
  refine ⟨self,hs,?_⟩
  have hw : CrcPublic128.NonRef128 self.algorithm := haeq ▸ ha
  simpa only [haeq] using CrcPublic128.digest_protocol_canonical self initial bytes hw hcoh

end CrcConstructor128
