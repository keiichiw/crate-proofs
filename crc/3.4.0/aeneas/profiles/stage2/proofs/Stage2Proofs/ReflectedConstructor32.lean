import Stage2Proofs.Public32Reflected
import Stage2Proofs.ReflectMathWide
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace CrcReflectedConstructor32
abbrev Table32 := Array (Array U32 256#usize) 1#usize

def tableRead (t : Table32) (b : U8) : U32 :=
  t.val[0].val[b.val]'(by have h := b.hmax; scalar_tac)

def Prefix (poly : U32) (t : Table32) (n : Nat) : Prop :=
  ∀ b : U8, b.val < n → (tableRead t b).bv = crc.polynomialRun poly.bv true 8 (b.bv.setWidth 32)

theorem utility (poly value : U32) :
    ∃ out, CrcBody.util.crc32 poly true value = .ok out ∧
      out.bv = crc.polynomialRun poly.bv true 8 value.bv := by
  obtain ⟨out,hout,hmodel⟩ := crc.crc32_polynomial_spec poly value true
  exact ⟨out,hout,hmodel⟩

theorem body_spec (poly : U32) (t : Table32) (i : Usize) (hi : i.val < 256)
    (hp : Prefix poly t i.val) :
    WP.spec (CrcBody.table.crc32_table_loop0.body true poly t i)
      (fun out => ∃ t' j, out = .cont (t',j) ∧ j.val = i.val+1 ∧ Prefix poly t' j.val) := by
  unfold CrcBody.table.crc32_table_loop0.body
  simp only [UScalar.lt_equiv, show (256#usize : Usize).val = 256 by rfl, hi, ↓reduceIte,
    show (1#usize : Usize) > 0#usize by decide]
  step
  have hi1 : i1.val = i.val := by scalar_tac
  obtain ⟨v,hv,hcanon⟩ := utility poly i1
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
    have he : i1.bv = b.bv.setWidth 32 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, UScalar.bv_toNat]
      have hb32 : b.val < 2^32 := by have h := b.hmax; scalar_tac
      rw [Nat.mod_eq_of_lt hb32]
      omega
    simpa only [he] using hcanon
  · apply hp b
    omega
theorem loop_spec (poly : U32) (t : Table32) :
    WP.spec (CrcBody.table.crc32_table_loop0 true poly t 0#usize)
      (fun out => Prefix poly out 256) := by
  unfold CrcBody.table.crc32_table_loop0
  apply loop.spec_decr_nat
    (measure := fun x : Table32 × Usize => 256-x.2.val)
    (inv := fun x : Table32 × Usize => x.2.val ≤ 256 ∧ Prefix poly x.1 x.2.val)
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
    · unfold CrcBody.table.crc32_table_loop0.body
      simp only [UScalar.lt_equiv, show (256#usize : Usize).val = 256 by rfl, hlt,
        ↓reduceIte, WP.spec_ok]
      have heq : i.val = 256 := by omega
      simpa only [heq] using hp
  · simp only [show (0#usize : Usize).val = 0 by rfl]
    exact ⟨by omega, by intro b hb; omega⟩

theorem table_spec (poly : U32) :
    ∃ out, CrcBody.table.crc32_table 1#usize 32#u8 poly true = .ok out ∧
      Prefix (CrcReflectedPublic32.reverseScalar poly) out 256 := by
  apply crc.total_result
  unfold CrcBody.table.crc32_table
  simp only [↓reduceIte, CrcReflectedPublic32.reverse32, bind_ok]
  have hzero : ((32#u8 - 32#u8) : Result U8) = .ok 0#u8 := by rfl
  simp only [hzero, bind_ok]
  step
  have hp : poly1 = CrcReflectedPublic32.reverseScalar poly := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    simpa only [show (0#u8 : U8).val = 0 by rfl, BitVec.ushiftRight_zero] using poly1_post1
  rw [hp]
  apply WP.spec_bind (loop_spec (CrcReflectedPublic32.reverseScalar poly)
    (Array.repeat 1#usize (Array.repeat 256#usize 0#u32)))
  intro out hout
  simp only [show ¬(1#usize : Usize) > 1#usize by decide, ↓reduceIte, WP.spec_ok]
  exact hout

theorem new_coherent (a : CrcBody.crc_catalog.Algorithm U32)
    (ha : CrcReflectedPublic32.Domain a) :
    ∃ out : CrcReflectedTable32.Crc32, CrcBody.crc32.CrcU32Table.new 1#usize a = .ok out ∧
      out.algorithm = a ∧ CrcReflectedTable32.Coherent out := by
  obtain ⟨t, ht, hp⟩ := table_spec a.poly
  obtain ⟨hw, hri⟩ := ha
  refine ⟨⟨a,t⟩, ?_, rfl, ?_⟩
  · simp only [CrcBody.crc32.CrcU32Table.new, hw, hri, ht, bind_ok]
  · intro b
    have hv := hp b (by have h := b.hmax; scalar_tac)
    rw [CrcReflectedWide.byteStep_injection (by decide)]
    have hz : (0 : BitVec 32).reverse = 0 := BitVec.reverse_eq_zero_iff.mpr rfl
    have hz' : (0 : BitVec 32).reverse ^^^ b.bv.setWidth 32 = b.bv.setWidth 32 :=
      (congrArg (fun x : BitVec 32 => x ^^^ b.bv.setWidth 32) hz).trans BitVec.zero_xor
    exact hv.trans (congrArg (crc.polynomialRun a.poly.bv.reverse true 8) hz'.symm)

theorem new_checksum_canonical (a : CrcBody.crc_catalog.Algorithm U32)
    (ha : CrcReflectedPublic32.Domain a) (bytes : Slice U8) :
    ∃ self : CrcReflectedTable32.Crc32, CrcBody.crc32.CrcU32Table.new 1#usize a = .ok self ∧
      ∃ out, CrcBody.crc32.CrcU32Table.checksum self bytes = .ok out ∧
      out.bv = CrcReflectedPublic32.finish a
        (CrcReflectedWide.run a.poly.bv a.init.bv (bytes.val.map UScalar.bv)) := by
  obtain ⟨self, hs, haeq, hcoh⟩ := new_coherent a ha
  refine ⟨self, hs, ?_⟩
  have hd : CrcReflectedPublic32.Domain self.algorithm := haeq ▸ ha
  simpa only [haeq] using CrcReflectedTable32.checksum_canonical self bytes hd hcoh

theorem new_digest_protocol_canonical (a : CrcBody.crc_catalog.Algorithm U32)
    (ha : CrcReflectedPublic32.Domain a) (initial : U32) (bytes : Slice U8) :
    ∃ self : CrcReflectedTable32.Crc32, CrcBody.crc32.CrcU32Table.new 1#usize a = .ok self ∧
      ∃ start stop out,
      CrcBody.crc32.CrcU32Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc32.DigestAU32Table.update start bytes = .ok stop ∧
      CrcBody.crc32.DigestAU32Table.finalize stop = .ok out ∧
      out.bv = CrcReflectedPublic32.finish a
        (CrcReflectedWide.run a.poly.bv initial.bv (bytes.val.map UScalar.bv)) := by
  obtain ⟨self, hs, haeq, hcoh⟩ := new_coherent a ha
  refine ⟨self, hs, ?_⟩
  have hd : CrcReflectedPublic32.Domain self.algorithm := haeq ▸ ha
  simpa only [haeq] using CrcReflectedTable32.digest_protocol_canonical self initial bytes hd hcoh
end CrcReflectedConstructor32
