import Stage2Proofs.Update64
import Stage2Proofs.Public64Base
import Stage2Proofs.ByteMathWide
open Aeneas Aeneas.Std Result
namespace CrcPublic64
abbrev Crc64 := CrcBody.Crc U64 (CrcBody.Table 1#usize) CrcUpdate64.Table
abbrev Digest64 := CrcBody.Digest U64 (CrcBody.Table 1#usize) CrcUpdate64.Table

def tableRead (table : CrcUpdate64.Table) (byte : U8) : U64 :=
  table.val[0].val[byte.val]'(by have h := byte.hmax; scalar_tac)

def Coherent64 (self : Crc64) : Prop :=
  ∀ byte : U8, (tableRead self.data byte).bv =
    CrcCanonicalWide.byteStep self.algorithm.poly.bv 0 byte.bv
theorem hlo (state : BitVec 64) (byte : BitVec 8) :
    ((state ^^^ (byte.setWidth 64 <<< 56)) <<< 8) = state <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem hhi (state : BitVec 64) (byte : BitVec 8) :
    ((state ^^^ (byte.setWidth 64 <<< 56)) >>> 56) <<< 56 =
      (((state >>> 56 ^^^ byte.setWidth 64) &&& 255) <<< 56) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem lookup_canonical (self : Crc64) (ht : Coherent64 self) (state : U64) (byte : U8) :
    (CrcUpdate64.lookup self.data state byte).bv =
      CrcCanonicalWide.byteStep self.algorithm.poly.bv state.bv byte.bv := by
  let idx : U8 := UScalar.mk (ty := .U8) ((CrcUpdate64.indexWord state byte).bv.setWidth 8)
  have hb := CrcUpdate64.indexWord_bound state byte
  have hidx : idx.val = (CrcUpdate64.indexWord state byte).val := by
    change (CrcUpdate64.indexWord state byte).val % 256 = _
    exact Nat.mod_eq_of_lt hb
  have hcast : idx.bv.setWidth 64 = (CrcUpdate64.indexWord state byte).bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, UScalar.bv_toNat]
    change idx.val % 18446744073709551616 = (CrcUpdate64.indexWord state byte).val
    rw [hidx]
    exact Nat.mod_eq_of_lt (by omega)
  have htidx := ht idx
  rw [CrcCanonicalWide.byteStep_injection (by decide)] at htidx
  have he : CrcCanonicalWide.encodeByte 64 idx.bv =
      (CrcUpdate64.indexWord state byte).bv <<< 56 := by
    exact congrArg (fun x : BitVec 64 => x <<< 56) hcast
  have htmodel : (tableRead self.data idx).bv = crc.polynomialRun self.algorithm.poly.bv false 8
      ((CrcUpdate64.indexWord state byte).bv <<< 56) := by
    rw [he] at htidx
    exact htidx.trans (congrArg (crc.polynomialRun self.algorithm.poly.bv false 8)
      (by apply BitVec.eq_of_getLsbD_eq; intro i hi; simp))
  have hl : (CrcUpdate64.lookup self.data state byte).bv =
      (tableRead self.data idx).bv ^^^ (state.bv <<< 8) := by
    simp [CrcUpdate64.lookup, UScalar.bv_xor, tableRead, hidx, CrcUpdate64.indexWord_bound]
  rw [hl, htmodel, CrcCanonicalWide.byteStep_injection (by decide), CrcCanonicalWide.encodeByte]
  rw [CrcCanonicalWide.polynomialRun_split8 (by decide) self.algorithm.poly.bv
    (state.bv ^^^ (byte.bv.setWidth 64 <<< 56))]
  change _ = ((state.bv ^^^ (byte.bv.setWidth 64 <<< 56)) <<< 8) ^^^
    crc.polynomialRun self.algorithm.poly.bv false 8
      (((state.bv ^^^ (byte.bv.setWidth 64 <<< 56)) >>> 56) <<< 56)
  rw [hlo, hhi]
  exact BitVec.xor_comm _ _


theorem run_canonical (self : Crc64) (ht : Coherent64 self) (state : U64) (bytes : List U8) :
    (CrcUpdate64.run self.data state bytes).bv =
      CrcCanonicalWide.run self.algorithm.poly.bv state.bv (bytes.map UScalar.bv) := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih =>
    change (CrcUpdate64.run self.data (CrcUpdate64.lookup self.data state byte) bytes).bv =
      CrcCanonicalWide.run self.algorithm.poly.bv
        (CrcCanonicalWide.byteStep self.algorithm.poly.bv state.bv byte.bv) (bytes.map UScalar.bv)
    rw [ih, lookup_canonical self ht]

theorem update_canonical (self : Crc64) (state : U64) (bytes : Slice U8)
    (hr : self.algorithm.refin = false) (ht : Coherent64 self) :
    ∃ out, CrcBody.crc64.CrcU64Table.update self state bytes = .ok out ∧
      out.bv = CrcCanonicalWide.run self.algorithm.poly.bv state.bv (bytes.val.map UScalar.bv) := by
  obtain ⟨out, hout, hv⟩ := CrcUpdate64.update_table_total self.algorithm self.data bytes state hr
  exact ⟨out, hout, (congrArg UScalar.bv hv).trans (run_canonical self ht state bytes.val)⟩

theorem checksum_canonical (self : Crc64) (bytes : Slice U8)
    (ha : NonRef64 self.algorithm) (ht : Coherent64 self) :
    ∃ out, CrcBody.crc64.CrcU64Table.checksum self bytes = .ok out ∧
      out.bv = (if self.algorithm.refout then
        (CrcCanonicalWide.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)).reverse else
        CrcCanonicalWide.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)) ^^^ self.algorithm.xorout.bv := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self self.algorithm.init bytes ha.2 ht
  obtain ⟨out, hout, hfin⟩ := finalize_total self.algorithm mid ha
  refine ⟨out, ?_, ?_⟩
  · simp only [CrcBody.crc64.CrcU64Table.checksum, init_identity _ _ ha, hm, hout, bind_ok]
  · simpa only [hv] using hfin

theorem digest_update_canonical (self : Digest64) (bytes : Slice U8)
    (hr : self.crc.algorithm.refin = false) (ht : Coherent64 self.crc) :
    ∃ out, CrcBody.crc64.DigestAU64Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv =
        CrcCanonicalWide.run self.crc.algorithm.poly.bv self.value.bv (bytes.val.map UScalar.bv) := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self.crc self.value bytes hr ht
  exact ⟨{ self with value := mid }, by simp [CrcBody.crc64.DigestAU64Table.update, hm], rfl, hv⟩

theorem digest_protocol_canonical (self : Crc64) (initial : U64) (bytes : Slice U8)
    (ha : NonRef64 self.algorithm) (ht : Coherent64 self) :
    ∃ start finish out,
      CrcBody.crc64.CrcU64Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc64.DigestAU64Table.update start bytes = .ok finish ∧
      CrcBody.crc64.DigestAU64Table.finalize finish = .ok out ∧
      out.bv = (if self.algorithm.refout then
        (CrcCanonicalWide.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv)).reverse
        else CrcCanonicalWide.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv))
        ^^^ self.algorithm.xorout.bv := by
  obtain ⟨finish, hu, hc, hv⟩ := digest_update_canonical (⟨self, initial⟩ : Digest64) bytes ha.2 ht
  have hfa : NonRef64 finish.crc.algorithm := by simpa only [hc] using ha
  obtain ⟨out, hout, hbv⟩ := finalize_total finish.crc.algorithm finish.value hfa
  refine ⟨⟨self, initial⟩, finish, out, ?_, hu, hout, ?_⟩
  · simp only [CrcBody.crc64.CrcU64Table.digest_with_initial, init_identity _ _ ha,
      bind_ok, CrcBody.crc64.DigestAU64Table.new]
  · simpa only [hc, hv] using hbv

theorem digest_update_nonref_canonical (self : Digest64) (bytes : Slice U8)
    (ha : NonRef64 self.crc.algorithm) (ht : Coherent64 self.crc) :
    ∃ out, CrcBody.crc64.DigestAU64Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv =
        CrcCanonicalWide.run self.crc.algorithm.poly.bv self.value.bv (bytes.val.map UScalar.bv) :=
  digest_update_canonical self bytes ha.2 ht
end CrcPublic64
