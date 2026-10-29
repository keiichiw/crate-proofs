import Stage2Proofs.Update32
import Stage2Proofs.Public32Base
import Stage2Proofs.ByteMathWide
open Aeneas Aeneas.Std Result
namespace CrcPublic32
abbrev Crc32 := CrcBody.Crc U32 (CrcBody.Table 1#usize) CrcUpdate32.Table
abbrev Digest32 := CrcBody.Digest U32 (CrcBody.Table 1#usize) CrcUpdate32.Table

def tableRead (table : CrcUpdate32.Table) (byte : U8) : U32 :=
  table.val[0].val[byte.val]'(by have h := byte.hmax; scalar_tac)

def Coherent32 (self : Crc32) : Prop :=
  ∀ byte : U8, (tableRead self.data byte).bv =
    CrcCanonicalWide.byteStep self.algorithm.poly.bv 0 byte.bv
theorem hlo (state : BitVec 32) (byte : BitVec 8) :
    ((state ^^^ (byte.setWidth 32 <<< 24)) <<< 8) = state <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem hhi (state : BitVec 32) (byte : BitVec 8) :
    ((state ^^^ (byte.setWidth 32 <<< 24)) >>> 24) <<< 24 =
      (((state >>> 24 ^^^ byte.setWidth 32) &&& 255) <<< 24) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem lookup_canonical (self : Crc32) (ht : Coherent32 self) (state : U32) (byte : U8) :
    (CrcUpdate32.lookup self.data state byte).bv =
      CrcCanonicalWide.byteStep self.algorithm.poly.bv state.bv byte.bv := by
  let idx : U8 := UScalar.mk (ty := .U8) ((CrcUpdate32.indexWord state byte).bv.setWidth 8)
  have hb := CrcUpdate32.indexWord_bound state byte
  have hidx : idx.val = (CrcUpdate32.indexWord state byte).val := by
    change (CrcUpdate32.indexWord state byte).val % 256 = _
    exact Nat.mod_eq_of_lt hb
  have hcast : idx.bv.setWidth 32 = (CrcUpdate32.indexWord state byte).bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, UScalar.bv_toNat]
    change idx.val % 4294967296 = (CrcUpdate32.indexWord state byte).val
    rw [hidx]
    exact Nat.mod_eq_of_lt (by omega)
  have htidx := ht idx
  rw [CrcCanonicalWide.byteStep_injection (by decide)] at htidx
  have he : CrcCanonicalWide.encodeByte 32 idx.bv =
      (CrcUpdate32.indexWord state byte).bv <<< 24 := by
    exact congrArg (fun x : BitVec 32 => x <<< 24) hcast
  have htmodel : (tableRead self.data idx).bv = crc.polynomialRun self.algorithm.poly.bv false 8
      ((CrcUpdate32.indexWord state byte).bv <<< 24) := by
    rw [he] at htidx
    exact htidx.trans (congrArg (crc.polynomialRun self.algorithm.poly.bv false 8)
      (by apply BitVec.eq_of_getLsbD_eq; intro i hi; simp))
  have hl : (CrcUpdate32.lookup self.data state byte).bv =
      (tableRead self.data idx).bv ^^^ (state.bv <<< 8) := by
    simp [CrcUpdate32.lookup, UScalar.bv_xor, tableRead, hidx, CrcUpdate32.indexWord_bound]
  rw [hl, htmodel, CrcCanonicalWide.byteStep_injection (by decide), CrcCanonicalWide.encodeByte]
  rw [CrcCanonicalWide.polynomialRun_split8 (by decide) self.algorithm.poly.bv
    (state.bv ^^^ (byte.bv.setWidth 32 <<< 24))]
  change _ = ((state.bv ^^^ (byte.bv.setWidth 32 <<< 24)) <<< 8) ^^^
    crc.polynomialRun self.algorithm.poly.bv false 8
      (((state.bv ^^^ (byte.bv.setWidth 32 <<< 24)) >>> 24) <<< 24)
  rw [hlo, hhi]
  exact BitVec.xor_comm _ _


theorem run_canonical (self : Crc32) (ht : Coherent32 self) (state : U32) (bytes : List U8) :
    (CrcUpdate32.run self.data state bytes).bv =
      CrcCanonicalWide.run self.algorithm.poly.bv state.bv (bytes.map UScalar.bv) := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih =>
    change (CrcUpdate32.run self.data (CrcUpdate32.lookup self.data state byte) bytes).bv =
      CrcCanonicalWide.run self.algorithm.poly.bv
        (CrcCanonicalWide.byteStep self.algorithm.poly.bv state.bv byte.bv) (bytes.map UScalar.bv)
    rw [ih, lookup_canonical self ht]

theorem update_canonical (self : Crc32) (state : U32) (bytes : Slice U8)
    (hr : self.algorithm.refin = false) (ht : Coherent32 self) :
    ∃ out, CrcBody.crc32.CrcU32Table.update self state bytes = .ok out ∧
      out.bv = CrcCanonicalWide.run self.algorithm.poly.bv state.bv (bytes.val.map UScalar.bv) := by
  obtain ⟨out, hout, hv⟩ := CrcUpdate32.update_table_total self.algorithm self.data bytes state hr
  exact ⟨out, hout, (congrArg UScalar.bv hv).trans (run_canonical self ht state bytes.val)⟩

theorem checksum_canonical (self : Crc32) (bytes : Slice U8)
    (ha : NonRef32 self.algorithm) (ht : Coherent32 self) :
    ∃ out, CrcBody.crc32.CrcU32Table.checksum self bytes = .ok out ∧
      out.bv = (if self.algorithm.refout then
        (CrcCanonicalWide.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)).reverse else
        CrcCanonicalWide.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)) ^^^ self.algorithm.xorout.bv := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self self.algorithm.init bytes ha.2 ht
  obtain ⟨out, hout, hfin⟩ := finalize_total self.algorithm mid ha
  refine ⟨out, ?_, ?_⟩
  · simp only [CrcBody.crc32.CrcU32Table.checksum, init_identity _ _ ha, hm, hout, bind_ok]
  · simpa only [hv] using hfin

theorem digest_update_canonical (self : Digest32) (bytes : Slice U8)
    (hr : self.crc.algorithm.refin = false) (ht : Coherent32 self.crc) :
    ∃ out, CrcBody.crc32.DigestAU32Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv =
        CrcCanonicalWide.run self.crc.algorithm.poly.bv self.value.bv (bytes.val.map UScalar.bv) := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self.crc self.value bytes hr ht
  exact ⟨{ self with value := mid }, by simp [CrcBody.crc32.DigestAU32Table.update, hm], rfl, hv⟩

theorem digest_protocol_canonical (self : Crc32) (initial : U32) (bytes : Slice U8)
    (ha : NonRef32 self.algorithm) (ht : Coherent32 self) :
    ∃ start finish out,
      CrcBody.crc32.CrcU32Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc32.DigestAU32Table.update start bytes = .ok finish ∧
      CrcBody.crc32.DigestAU32Table.finalize finish = .ok out ∧
      out.bv = (if self.algorithm.refout then
        (CrcCanonicalWide.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv)).reverse
        else CrcCanonicalWide.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv))
        ^^^ self.algorithm.xorout.bv := by
  obtain ⟨finish, hu, hc, hv⟩ := digest_update_canonical (⟨self, initial⟩ : Digest32) bytes ha.2 ht
  have hfa : NonRef32 finish.crc.algorithm := by simpa only [hc] using ha
  obtain ⟨out, hout, hbv⟩ := finalize_total finish.crc.algorithm finish.value hfa
  refine ⟨⟨self, initial⟩, finish, out, ?_, hu, hout, ?_⟩
  · simp only [CrcBody.crc32.CrcU32Table.digest_with_initial, init_identity _ _ ha,
      bind_ok, CrcBody.crc32.DigestAU32Table.new]
  · simpa only [hc, hv] using hbv

theorem digest_update_nonref_canonical (self : Digest32) (bytes : Slice U8)
    (ha : NonRef32 self.crc.algorithm) (ht : Coherent32 self.crc) :
    ∃ out, CrcBody.crc32.DigestAU32Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv =
        CrcCanonicalWide.run self.crc.algorithm.poly.bv self.value.bv (bytes.val.map UScalar.bv) :=
  digest_update_canonical self bytes ha.2 ht
end CrcPublic32
