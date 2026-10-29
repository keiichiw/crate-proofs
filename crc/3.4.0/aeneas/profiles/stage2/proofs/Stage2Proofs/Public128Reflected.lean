import Stage2Proofs.ByteIndex
import Stage2Proofs.Update128Reflected
import Stage2Proofs.Public128
import Stage2Proofs.Reflected128Base
import Stage2Proofs.ReflectMathWide
open Aeneas Aeneas.Std Result
namespace CrcReflectedTable128
open CrcReflectedPublic128
abbrev Crc128 := CrcPublic128.Crc128
abbrev Digest128 := CrcPublic128.Digest128

def Coherent (self : Crc128) : Prop :=
  ∀ byte : U8, (CrcPublic128.tableRead self.data byte).bv =
    (CrcReflectedWide.byteStep self.algorithm.poly.bv 0 byte.bv).reverse
theorem shifted_xor_byte (state : BitVec 128) (byte : BitVec 8) :
    ((state ^^^ byte.setWidth 128) >>> 8) = state >>> 8 := by
  exact CrcByteIndex.shifted_xor_byte _ _

theorem lookup_canonical (self : Crc128) (ht : Coherent self) (state : U128) (byte : U8) :
    (CrcUpdate128Reflected.lookup self.data state byte).bv =
      (CrcReflectedWide.byteStep self.algorithm.poly.bv state.bv.reverse byte.bv).reverse := by
  let idx : U8 := UScalar.mk (ty := .U8) ((CrcUpdate128Reflected.indexWord state byte).bv.setWidth 8)
  have hb := CrcUpdate128Reflected.indexWord_bound state byte
  have hidx : idx.val = (CrcUpdate128Reflected.indexWord state byte).val := by
    change (CrcUpdate128Reflected.indexWord state byte).val % 256 = _
    exact Nat.mod_eq_of_lt hb
  have hcast : idx.bv.setWidth 128 = (CrcUpdate128Reflected.indexWord state byte).bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, UScalar.bv_toNat]
    change idx.val % 340282366920938463463374607431768211456 = (CrcUpdate128Reflected.indexWord state byte).val
    rw [hidx]
    exact Nat.mod_eq_of_lt (by omega)
  have htidx := ht idx
  rw [CrcReflectedWide.byteStep_injection (by decide)] at htidx
  have htmodel : (CrcPublic128.tableRead self.data idx).bv =
      crc.polynomialRun self.algorithm.poly.bv.reverse true 8
        (CrcUpdate128Reflected.indexWord state byte).bv := by
    exact htidx.trans (congrArg (crc.polynomialRun self.algorithm.poly.bv.reverse true 8)
      (by
        calc
          (0 : BitVec 128).reverse ^^^ idx.bv.setWidth 128 = idx.bv.setWidth 128 := by
            apply BitVec.eq_of_getLsbD_eq
            intro i hi
            simp [BitVec.getLsbD_reverse]
          _ = _ := hcast))
  have hl : (CrcUpdate128Reflected.lookup self.data state byte).bv =
      (CrcPublic128.tableRead self.data idx).bv ^^^ (state.bv >>> 8) := by
    simp [CrcUpdate128Reflected.lookup, UScalar.bv_xor, CrcPublic128.tableRead, hidx,
      CrcUpdate128Reflected.indexWord_bound]
  rw [hl, htmodel, CrcReflectedWide.byteStep_injection (by decide)]
  rw [BitVec.reverse_reverse_eq, CrcReflectedWide.polynomialRun_split8 (by decide)
    self.algorithm.poly.bv.reverse (state.bv ^^^ byte.bv.setWidth 128), shifted_xor_byte]
  exact BitVec.xor_comm _ _

theorem run_canonical (self : Crc128) (ht : Coherent self) (state : U128) (bytes : List U8) :
    (CrcUpdate128Reflected.run self.data state bytes).bv =
      (CrcReflectedWide.run self.algorithm.poly.bv state.bv.reverse (bytes.map UScalar.bv)).reverse := by
  induction bytes generalizing state with
  | nil => exact (BitVec.reverse_reverse_eq (x := state.bv)).symm
  | cons byte bytes ih =>
    change (CrcUpdate128Reflected.run self.data (CrcUpdate128Reflected.lookup self.data state byte) bytes).bv =
      (CrcReflectedWide.run self.algorithm.poly.bv
        (CrcReflectedWide.byteStep self.algorithm.poly.bv state.bv.reverse byte.bv)
        (bytes.map UScalar.bv)).reverse
    rw [ih, lookup_canonical self ht, BitVec.reverse_reverse_eq]

theorem update_canonical (self : Crc128) (state : U128) (bytes : Slice U8)
    (ha : Domain self.algorithm) (ht : Coherent self) :
    ∃ out, CrcBody.crc128.CrcU128Table.update self state bytes = .ok out ∧
      out.bv.reverse = CrcReflectedWide.run self.algorithm.poly.bv state.bv.reverse
        (bytes.val.map UScalar.bv) := by
  obtain ⟨out, hout, hv⟩ := CrcUpdate128Reflected.update_table_total self.algorithm self.data bytes state ha.2
  refine ⟨out, hout, ?_⟩
  exact (congrArg BitVec.reverse ((congrArg UScalar.bv hv).trans
    (run_canonical self ht state bytes.val))).trans (BitVec.reverse_reverse_eq)

theorem checksum_canonical (self : Crc128) (bytes : Slice U8)
    (ha : Domain self.algorithm) (ht : Coherent self) :
    ∃ out, CrcBody.crc128.CrcU128Table.checksum self bytes = .ok out ∧
      out.bv = finish self.algorithm (CrcReflectedWide.run self.algorithm.poly.bv
        self.algorithm.init.bv (bytes.val.map UScalar.bv)) := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self (reverseScalar self.algorithm.init) bytes ha ht
  obtain ⟨out, hout, hfin⟩ := finalize_canonical self.algorithm mid ha
  refine ⟨out, ?_, ?_⟩
  · simp only [CrcBody.crc128.CrcU128Table.checksum, init_eq _ _ ha, hm, hout, bind_ok]
  · simpa only [hv, reverseScalar_bv, BitVec.reverse_reverse_eq] using hfin

theorem digest_update_canonical (self : Digest128) (bytes : Slice U8)
    (ha : Domain self.crc.algorithm) (ht : Coherent self.crc) :
    ∃ out, CrcBody.crc128.DigestAU128Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv.reverse =
        CrcReflectedWide.run self.crc.algorithm.poly.bv self.value.bv.reverse (bytes.val.map UScalar.bv) := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self.crc self.value bytes ha ht
  exact ⟨{ self with value := mid }, by simp [CrcBody.crc128.DigestAU128Table.update, hm], rfl, hv⟩

theorem digest_protocol_canonical (self : Crc128) (initial : U128) (bytes : Slice U8)
    (ha : Domain self.algorithm) (ht : Coherent self) :
    ∃ start final out,
      CrcBody.crc128.CrcU128Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc128.DigestAU128Table.update start bytes = .ok final ∧
      CrcBody.crc128.DigestAU128Table.finalize final = .ok out ∧
      out.bv = finish self.algorithm (CrcReflectedWide.run self.algorithm.poly.bv initial.bv
        (bytes.val.map UScalar.bv)) := by
  obtain ⟨final, hu, hc, hv⟩ := digest_update_canonical
    (⟨self, reverseScalar initial⟩ : Digest128) bytes ha ht
  have hfa : Domain final.crc.algorithm := by simpa only [hc] using ha
  obtain ⟨out, hout, hbv⟩ := finalize_canonical final.crc.algorithm final.value hfa
  refine ⟨⟨self, reverseScalar initial⟩, final, out, ?_, hu, hout, ?_⟩
  · simp only [CrcBody.crc128.CrcU128Table.digest_with_initial, init_eq _ _ ha,
      bind_ok, CrcBody.crc128.DigestAU128Table.new]
  · simpa only [hc, hv, reverseScalar_bv, BitVec.reverse_reverse_eq] using hbv
end CrcReflectedTable128
