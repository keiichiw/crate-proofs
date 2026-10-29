import Stage2Proofs.Update16
import Stage2Proofs.Public16Base
import Stage2Proofs.ByteMathWide
open Aeneas Aeneas.Std Result
namespace CrcPublic16
abbrev Crc16 := CrcBody.Crc U16 (CrcBody.Table 1#usize) CrcUpdate16.Table
abbrev Digest16 := CrcBody.Digest U16 (CrcBody.Table 1#usize) CrcUpdate16.Table

def tableRead (table : CrcUpdate16.Table) (byte : U8) : U16 :=
  table.val[0].val[byte.val]'(by have h := byte.hmax; scalar_tac)

def Coherent16 (self : Crc16) : Prop :=
  ∀ byte : U8, (tableRead self.data byte).bv =
    CrcCanonicalWide.byteStep self.algorithm.poly.bv 0 byte.bv
theorem hlo (state : BitVec 16) (byte : BitVec 8) :
    ((state ^^^ (byte.setWidth 16 <<< 8)) <<< 8) = state <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem hhi (state : BitVec 16) (byte : BitVec 8) :
    ((state ^^^ (byte.setWidth 16 <<< 8)) >>> 8) <<< 8 =
      (((state >>> 8 ^^^ byte.setWidth 16) &&& 255) <<< 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem lookup_canonical (self : Crc16) (ht : Coherent16 self) (state : U16) (byte : U8) :
    (CrcUpdate16.lookup self.data state byte).bv =
      CrcCanonicalWide.byteStep self.algorithm.poly.bv state.bv byte.bv := by
  let idx : U8 := UScalar.mk (ty := .U8) ((CrcUpdate16.indexWord state byte).bv.setWidth 8)
  have hb := CrcUpdate16.indexWord_bound state byte
  have hidx : idx.val = (CrcUpdate16.indexWord state byte).val := by
    change (CrcUpdate16.indexWord state byte).val % 256 = _
    exact Nat.mod_eq_of_lt hb
  have hcast : idx.bv.setWidth 16 = (CrcUpdate16.indexWord state byte).bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, UScalar.bv_toNat]
    change idx.val % 65536 = (CrcUpdate16.indexWord state byte).val
    rw [hidx]
    exact Nat.mod_eq_of_lt (by omega)
  have htidx := ht idx
  rw [CrcCanonicalWide.byteStep_injection (by decide)] at htidx
  have he : CrcCanonicalWide.encodeByte 16 idx.bv =
      (CrcUpdate16.indexWord state byte).bv <<< 8 := by
    exact congrArg (fun x : BitVec 16 => x <<< 8) hcast
  have htmodel : (tableRead self.data idx).bv = crc.polynomialRun self.algorithm.poly.bv false 8
      ((CrcUpdate16.indexWord state byte).bv <<< 8) := by
    rw [he] at htidx
    exact htidx.trans (congrArg (crc.polynomialRun self.algorithm.poly.bv false 8)
      (by apply BitVec.eq_of_getLsbD_eq; intro i hi; simp))
  have hl : (CrcUpdate16.lookup self.data state byte).bv =
      (tableRead self.data idx).bv ^^^ (state.bv <<< 8) := by
    simp [CrcUpdate16.lookup, UScalar.bv_xor, tableRead, hidx, CrcUpdate16.indexWord_bound]
  rw [hl, htmodel, CrcCanonicalWide.byteStep_injection (by decide), CrcCanonicalWide.encodeByte]
  rw [CrcCanonicalWide.polynomialRun_split8 (by decide) self.algorithm.poly.bv
    (state.bv ^^^ (byte.bv.setWidth 16 <<< 8))]
  change _ = ((state.bv ^^^ (byte.bv.setWidth 16 <<< 8)) <<< 8) ^^^
    crc.polynomialRun self.algorithm.poly.bv false 8
      (((state.bv ^^^ (byte.bv.setWidth 16 <<< 8)) >>> 8) <<< 8)
  rw [hlo, hhi]
  exact BitVec.xor_comm _ _


theorem run_canonical (self : Crc16) (ht : Coherent16 self) (state : U16) (bytes : List U8) :
    (CrcUpdate16.run self.data state bytes).bv =
      CrcCanonicalWide.run self.algorithm.poly.bv state.bv (bytes.map UScalar.bv) := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih =>
    change (CrcUpdate16.run self.data (CrcUpdate16.lookup self.data state byte) bytes).bv =
      CrcCanonicalWide.run self.algorithm.poly.bv
        (CrcCanonicalWide.byteStep self.algorithm.poly.bv state.bv byte.bv) (bytes.map UScalar.bv)
    rw [ih, lookup_canonical self ht]

theorem update_canonical (self : Crc16) (state : U16) (bytes : Slice U8)
    (hr : self.algorithm.refin = false) (ht : Coherent16 self) :
    ∃ out, CrcBody.crc16.CrcU16Table.update self state bytes = .ok out ∧
      out.bv = CrcCanonicalWide.run self.algorithm.poly.bv state.bv (bytes.val.map UScalar.bv) := by
  obtain ⟨out, hout, hv⟩ := CrcUpdate16.update_table_total self.algorithm self.data bytes state hr
  exact ⟨out, hout, (congrArg UScalar.bv hv).trans (run_canonical self ht state bytes.val)⟩

theorem checksum_canonical (self : Crc16) (bytes : Slice U8)
    (ha : NonRef16 self.algorithm) (ht : Coherent16 self) :
    ∃ out, CrcBody.crc16.CrcU16Table.checksum self bytes = .ok out ∧
      out.bv = (if self.algorithm.refout then
        (CrcCanonicalWide.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)).reverse else
        CrcCanonicalWide.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)) ^^^ self.algorithm.xorout.bv := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self self.algorithm.init bytes ha.2 ht
  obtain ⟨out, hout, hfin⟩ := finalize_total self.algorithm mid ha
  refine ⟨out, ?_, ?_⟩
  · simp only [CrcBody.crc16.CrcU16Table.checksum, init_identity _ _ ha, hm, hout, bind_ok]
  · simpa only [hv] using hfin

theorem digest_update_canonical (self : Digest16) (bytes : Slice U8)
    (hr : self.crc.algorithm.refin = false) (ht : Coherent16 self.crc) :
    ∃ out, CrcBody.crc16.DigestAU16Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv =
        CrcCanonicalWide.run self.crc.algorithm.poly.bv self.value.bv (bytes.val.map UScalar.bv) := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self.crc self.value bytes hr ht
  exact ⟨{ self with value := mid }, by simp [CrcBody.crc16.DigestAU16Table.update, hm], rfl, hv⟩

theorem digest_protocol_canonical (self : Crc16) (initial : U16) (bytes : Slice U8)
    (ha : NonRef16 self.algorithm) (ht : Coherent16 self) :
    ∃ start finish out,
      CrcBody.crc16.CrcU16Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc16.DigestAU16Table.update start bytes = .ok finish ∧
      CrcBody.crc16.DigestAU16Table.finalize finish = .ok out ∧
      out.bv = (if self.algorithm.refout then
        (CrcCanonicalWide.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv)).reverse
        else CrcCanonicalWide.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv))
        ^^^ self.algorithm.xorout.bv := by
  obtain ⟨finish, hu, hc, hv⟩ := digest_update_canonical (⟨self, initial⟩ : Digest16) bytes ha.2 ht
  have hfa : NonRef16 finish.crc.algorithm := by simpa only [hc] using ha
  obtain ⟨out, hout, hbv⟩ := finalize_total finish.crc.algorithm finish.value hfa
  refine ⟨⟨self, initial⟩, finish, out, ?_, hu, hout, ?_⟩
  · simp only [CrcBody.crc16.CrcU16Table.digest_with_initial, init_identity _ _ ha,
      bind_ok, CrcBody.crc16.DigestAU16Table.new]
  · simpa only [hc, hv] using hbv

theorem digest_update_nonref_canonical (self : Digest16) (bytes : Slice U8)
    (ha : NonRef16 self.crc.algorithm) (ht : Coherent16 self.crc) :
    ∃ out, CrcBody.crc16.DigestAU16Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv =
        CrcCanonicalWide.run self.crc.algorithm.poly.bv self.value.bv (bytes.val.map UScalar.bv) :=
  digest_update_canonical self bytes ha.2 ht
end CrcPublic16
