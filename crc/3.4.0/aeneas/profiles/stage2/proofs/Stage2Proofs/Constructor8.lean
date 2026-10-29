import Stage2Proofs.Public8Base
import Stage2Proofs.Update8
import Stage2Proofs.Public8
import Stage2Proofs.Refout8
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace CrcConstructor8
abbrev Table8 := Array (Array U8 256#usize) 1#usize

def Prefix (poly : U8) (t : Table8) (n : Nat) : Prop :=
  ∀ b : U8, b.val < n → (CrcUpdate8.tableRead t b).bv = CrcCanonical8.byteStep poly.bv 0 b.bv

theorem body_spec (poly : U8) (t : Table8) (i : Usize) (hi : i.val < 256)
    (hp : Prefix poly t i.val) :
    WP.spec (CrcBody.table.crc8_table_loop0.body false poly t i)
      (fun out => ∃ t' j, out = .cont (t',j) ∧ j.val = i.val+1 ∧ Prefix poly t' j.val) := by
  unfold CrcBody.table.crc8_table_loop0.body
  simp only [UScalar.lt_equiv, show (256#usize : Usize).val = 256 by rfl, hi, ↓reduceIte,
    show (1#usize : Usize) > 0#usize by decide]
  step
  have hu : CrcBody.util.crc8 poly false i1 = crc.util.crc8 poly false i1 := rfl
  obtain ⟨v,hv,hcanon⟩ := CrcCanonical8.utility_byteStep poly i1
  rw [hu, hv]
  simp only [bind_ok]
  step
  step
  step
  refine ⟨_, i3, rfl, i3_post, ?_⟩
  intro b hb
  simp only [Prefix] at hp
  have hi1 : i1.val = i.val := by scalar_tac
  have hzero : (0#usize : Usize).val = 0 := rfl
  simp only [CrcUpdate8.tableRead, a_post, index_mut_back_post, a1_post,
    Array.set_val_eq, hzero, List.getElem_set, ↓reduceIte]
  split
  · rename_i heq
    have he : i1 = b := by apply (UScalar.eq_equiv_bv_eq _ _).mpr; apply BitVec.eq_of_toNat_eq; simp only [UScalar.bv_toNat]; omega
    simpa only [he] using hcanon
  · apply hp b
    omega

theorem loop_spec (poly : U8) (t : Table8) :
    WP.spec (CrcBody.table.crc8_table_loop0 false poly t 0#usize)
      (fun out => Prefix poly out 256) := by
  unfold CrcBody.table.crc8_table_loop0
  apply loop.spec_decr_nat
    (measure := fun x : Table8 × Usize => 256-x.2.val)
    (inv := fun x : Table8 × Usize => x.2.val ≤ 256 ∧ Prefix poly x.1 x.2.val)
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
    · unfold CrcBody.table.crc8_table_loop0.body
      simp only [UScalar.lt_equiv, show (256#usize : Usize).val = 256 by rfl, hlt,
        ↓reduceIte, WP.spec_ok]
      have heq : i.val = 256 := by omega
      simpa only [heq] using hp
  · simp only [show (0#usize : Usize).val = 0 by rfl]
    exact ⟨by omega, by intro b hb; omega⟩

theorem table_spec (poly : U8) :
    ∃ out, CrcBody.table.crc8_table 1#usize 8#u8 poly false = .ok out ∧ Prefix poly out 256 := by
  apply crc.total_result
  unfold CrcBody.table.crc8_table
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hzero : ((8#u8 - 8#u8) : Result U8) = .ok 0#u8 := by rfl
  simp only [hzero, bind_ok]
  step
  have hp : poly1 = poly := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    simpa only [show (0#u8 : U8).val = 0 by rfl, BitVec.shiftLeft_zero] using poly1_post1
  rw [hp]
  apply WP.spec_bind (loop_spec poly (Array.repeat 1#usize (Array.repeat 256#usize 0#u8)))
  intro out hout
  simp only [show ¬(1#usize : Usize) > 1#usize by decide, ↓reduceIte, WP.spec_ok]
  exact hout


theorem new8_coherent_nonref (a : CrcBody.crc_catalog.Algorithm U8)
    (ha : CrcRefout8.NonRef8 a) :
    ∃ out : CrcBody.Crc8, CrcBody.crc8.CrcU8Table.new 1#usize a = .ok out ∧
      out.algorithm = a ∧ CrcBody.Coherent8 out := by
  obtain ⟨t,ht,hp⟩ := table_spec a.poly
  obtain ⟨hw,hri⟩ := ha
  refine ⟨⟨a,t⟩, ?_, rfl, ?_⟩
  · simp only [CrcBody.crc8.CrcU8Table.new, hw, hri, ht, bind_ok]
  · intro b
    apply hp (UScalar.mk b)
    have h := (UScalar.mk b : U8).hmax
    scalar_tac

theorem new8_coherent (a : CrcBody.crc_catalog.Algorithm U8)
    (ha : CrcBody.FullWidth8 a) :
    ∃ out : CrcBody.Crc8, CrcBody.crc8.CrcU8Table.new 1#usize a = .ok out ∧
      out.algorithm = a ∧ CrcBody.Coherent8 out :=
  new8_coherent_nonref a ⟨ha.1,ha.2.1⟩

theorem new_checksum8_canonical (a : CrcBody.crc_catalog.Algorithm U8)
    (ha : CrcBody.FullWidth8 a) (bytes : Slice U8) :
    ∃ self : CrcBody.Crc8, CrcBody.crc8.CrcU8Table.new 1#usize a = .ok self ∧
      ∃ out, CrcBody.crc8.CrcU8Table.checksum self bytes = .ok out ∧
      out.bv = CrcCanonical8.run a.poly.bv a.init.bv (bytes.val.map UScalar.bv) ^^^ a.xorout.bv := by
  obtain ⟨self,hs,haeq,hcoh⟩ := new8_coherent a ha
  refine ⟨self,hs,?_⟩
  have hw : CrcBody.FullWidth8 self.algorithm := haeq ▸ ha
  simpa only [haeq] using CrcBody.checksum8_canonical self bytes hw hcoh


theorem new_checksum8_nonref (a : CrcBody.crc_catalog.Algorithm U8)
    (ha : CrcRefout8.NonRef8 a) (bytes : Slice U8) :
    ∃ self : CrcBody.Crc8, CrcBody.crc8.CrcU8Table.new 1#usize a = .ok self ∧
      ∃ out, CrcBody.crc8.CrcU8Table.checksum self bytes = .ok out ∧
      out.bv = (if a.refout then
        (CrcCanonical8.run a.poly.bv a.init.bv (bytes.val.map UScalar.bv)).reverse
        else CrcCanonical8.run a.poly.bv a.init.bv (bytes.val.map UScalar.bv)) ^^^ a.xorout.bv := by
  obtain ⟨self,hs,haeq,hcoh⟩ := new8_coherent_nonref a ha
  refine ⟨self,hs,?_⟩
  have hw : CrcRefout8.NonRef8 self.algorithm := haeq ▸ ha
  simpa only [haeq] using CrcRefout8.checksum_canonical self bytes hw hcoh

theorem new_digest_protocol8_nonref (a : CrcBody.crc_catalog.Algorithm U8)
    (ha : CrcRefout8.NonRef8 a) (initial : U8) (bytes : Slice U8) :
    ∃ self : CrcBody.Crc8, CrcBody.crc8.CrcU8Table.new 1#usize a = .ok self ∧
      ∃ start finish out,
      CrcBody.crc8.CrcU8Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc8.DigestAU8Table.update start bytes = .ok finish ∧
      CrcBody.crc8.DigestAU8Table.finalize finish = .ok out ∧
      out.bv = (if a.refout then
        (CrcCanonical8.run a.poly.bv initial.bv (bytes.val.map UScalar.bv)).reverse
        else CrcCanonical8.run a.poly.bv initial.bv (bytes.val.map UScalar.bv)) ^^^ a.xorout.bv := by
  obtain ⟨self,hs,haeq,hcoh⟩ := new8_coherent_nonref a ha
  refine ⟨self,hs,?_⟩
  have hw : CrcRefout8.NonRef8 self.algorithm := haeq ▸ ha
  simpa only [haeq] using CrcRefout8.digest_protocol_canonical self initial bytes hw hcoh

end CrcConstructor8
