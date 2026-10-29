import Stage2Proofs.ByteIndex
import Stage2Proofs.Update128
import Stage2Proofs.Public128Base
import Stage2Proofs.ByteMathWide
open Aeneas Aeneas.Std Result
namespace CrcPublic128
abbrev Crc128 := CrcBody.Crc U128 (CrcBody.Table 1#usize) CrcUpdate128.Table
abbrev Digest128 := CrcBody.Digest U128 (CrcBody.Table 1#usize) CrcUpdate128.Table

def tableRead (table : CrcUpdate128.Table) (byte : U8) : U128 :=
  table.val[0].val[byte.val]'(by have h := byte.hmax; scalar_tac)

def Coherent128 (self : Crc128) : Prop :=
  ∀ byte : U8, (tableRead self.data byte).bv =
    CrcCanonicalWide.byteStep self.algorithm.poly.bv 0 byte.bv
theorem hlo (state : BitVec 128) (byte : BitVec 8) :
    ((state ^^^ (byte.setWidth 128 <<< 120)) <<< 8) = state <<< 8 := by
  exact CrcByteIndex.shifted_xor_encoded (by decide) _ _
theorem hhi (state : BitVec 128) (byte : BitVec 8) :
    ((state ^^^ (byte.setWidth 128 <<< 120)) >>> 120) <<< 120 =
      (((state >>> 120 ^^^ byte.setWidth 128) &&& 255) <<< 120) := by
  exact CrcByteIndex.highPart_injected (by decide) _ _

theorem lookup_canonical (self : Crc128) (ht : Coherent128 self) (state : U128) (byte : U8) :
    (CrcUpdate128.lookup self.data state byte).bv =
      CrcCanonicalWide.byteStep self.algorithm.poly.bv state.bv byte.bv := by
  let idx : U8 := UScalar.mk (ty := .U8) ((CrcUpdate128.indexWord state byte).bv.setWidth 8)
  have hb := CrcUpdate128.indexWord_bound state byte
  have hidx : idx.val = (CrcUpdate128.indexWord state byte).val := by
    change (CrcUpdate128.indexWord state byte).val % 256 = _
    exact Nat.mod_eq_of_lt hb
  have hcast : idx.bv.setWidth 128 = (CrcUpdate128.indexWord state byte).bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, UScalar.bv_toNat]
    change idx.val % 340282366920938463463374607431768211456 = (CrcUpdate128.indexWord state byte).val
    rw [hidx]
    exact Nat.mod_eq_of_lt (by omega)
  have htidx := ht idx
  rw [CrcCanonicalWide.byteStep_injection (by decide)] at htidx
  have he : CrcCanonicalWide.encodeByte 128 idx.bv =
      (CrcUpdate128.indexWord state byte).bv <<< 120 := by
    exact congrArg (fun x : BitVec 128 => x <<< 120) hcast
  have htmodel : (tableRead self.data idx).bv = crc.polynomialRun self.algorithm.poly.bv false 8
      ((CrcUpdate128.indexWord state byte).bv <<< 120) := by
    rw [he] at htidx
    exact htidx.trans (congrArg (crc.polynomialRun self.algorithm.poly.bv false 8)
      (by apply BitVec.eq_of_getLsbD_eq; intro i hi; simp))
  have hl : (CrcUpdate128.lookup self.data state byte).bv =
      (tableRead self.data idx).bv ^^^ (state.bv <<< 8) := by
    simp [CrcUpdate128.lookup, UScalar.bv_xor, tableRead, hidx, CrcUpdate128.indexWord_bound]
  rw [hl, htmodel, CrcCanonicalWide.byteStep_injection (by decide), CrcCanonicalWide.encodeByte]
  rw [CrcCanonicalWide.polynomialRun_split8 (by decide) self.algorithm.poly.bv
    (state.bv ^^^ (byte.bv.setWidth 128 <<< 120))]
  change _ = ((state.bv ^^^ (byte.bv.setWidth 128 <<< 120)) <<< 8) ^^^
    crc.polynomialRun self.algorithm.poly.bv false 8
      (((state.bv ^^^ (byte.bv.setWidth 128 <<< 120)) >>> 120) <<< 120)
  rw [hlo, hhi]
  exact BitVec.xor_comm _ _


theorem run_canonical (self : Crc128) (ht : Coherent128 self) (state : U128) (bytes : List U8) :
    (CrcUpdate128.run self.data state bytes).bv =
      CrcCanonicalWide.run self.algorithm.poly.bv state.bv (bytes.map UScalar.bv) := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih =>
    change (CrcUpdate128.run self.data (CrcUpdate128.lookup self.data state byte) bytes).bv =
      CrcCanonicalWide.run self.algorithm.poly.bv
        (CrcCanonicalWide.byteStep self.algorithm.poly.bv state.bv byte.bv) (bytes.map UScalar.bv)
    rw [ih, lookup_canonical self ht]

theorem update_canonical (self : Crc128) (state : U128) (bytes : Slice U8)
    (hr : self.algorithm.refin = false) (ht : Coherent128 self) :
    ∃ out, CrcBody.crc128.CrcU128Table.update self state bytes = .ok out ∧
      out.bv = CrcCanonicalWide.run self.algorithm.poly.bv state.bv (bytes.val.map UScalar.bv) := by
  obtain ⟨out, hout, hv⟩ := CrcUpdate128.update_table_total self.algorithm self.data bytes state hr
  exact ⟨out, hout, (congrArg UScalar.bv hv).trans (run_canonical self ht state bytes.val)⟩

theorem checksum_canonical (self : Crc128) (bytes : Slice U8)
    (ha : NonRef128 self.algorithm) (ht : Coherent128 self) :
    ∃ out, CrcBody.crc128.CrcU128Table.checksum self bytes = .ok out ∧
      out.bv = (if self.algorithm.refout then
        (CrcCanonicalWide.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)).reverse else
        CrcCanonicalWide.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)) ^^^ self.algorithm.xorout.bv := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self self.algorithm.init bytes ha.2 ht
  obtain ⟨out, hout, hfin⟩ := finalize_total self.algorithm mid ha
  refine ⟨out, ?_, ?_⟩
  · simp only [CrcBody.crc128.CrcU128Table.checksum, init_identity _ _ ha, hm, hout, bind_ok]
  · simpa only [hv] using hfin

theorem digest_update_canonical (self : Digest128) (bytes : Slice U8)
    (hr : self.crc.algorithm.refin = false) (ht : Coherent128 self.crc) :
    ∃ out, CrcBody.crc128.DigestAU128Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv =
        CrcCanonicalWide.run self.crc.algorithm.poly.bv self.value.bv (bytes.val.map UScalar.bv) := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self.crc self.value bytes hr ht
  exact ⟨{ self with value := mid }, by simp [CrcBody.crc128.DigestAU128Table.update, hm], rfl, hv⟩

theorem digest_protocol_canonical (self : Crc128) (initial : U128) (bytes : Slice U8)
    (ha : NonRef128 self.algorithm) (ht : Coherent128 self) :
    ∃ start finish out,
      CrcBody.crc128.CrcU128Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc128.DigestAU128Table.update start bytes = .ok finish ∧
      CrcBody.crc128.DigestAU128Table.finalize finish = .ok out ∧
      out.bv = (if self.algorithm.refout then
        (CrcCanonicalWide.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv)).reverse
        else CrcCanonicalWide.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv))
        ^^^ self.algorithm.xorout.bv := by
  obtain ⟨finish, hu, hc, hv⟩ := digest_update_canonical (⟨self, initial⟩ : Digest128) bytes ha.2 ht
  have hfa : NonRef128 finish.crc.algorithm := by simpa only [hc] using ha
  obtain ⟨out, hout, hbv⟩ := finalize_total finish.crc.algorithm finish.value hfa
  refine ⟨⟨self, initial⟩, finish, out, ?_, hu, hout, ?_⟩
  · simp only [CrcBody.crc128.CrcU128Table.digest_with_initial, init_identity _ _ ha,
      bind_ok, CrcBody.crc128.DigestAU128Table.new]
  · simpa only [hc, hv] using hbv

theorem digest_update_nonref_canonical (self : Digest128) (bytes : Slice U8)
    (ha : NonRef128 self.crc.algorithm) (ht : Coherent128 self.crc) :
    ∃ out, CrcBody.crc128.DigestAU128Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv =
        CrcCanonicalWide.run self.crc.algorithm.poly.bv self.value.bv (bytes.val.map UScalar.bv) :=
  digest_update_canonical self bytes ha.2 ht
end CrcPublic128
