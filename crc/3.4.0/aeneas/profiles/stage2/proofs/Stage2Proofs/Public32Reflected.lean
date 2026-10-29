import Stage2Proofs.Update32Reflected
import Stage2Proofs.Public32
import Stage2Proofs.Reflected32Base
import Stage2Proofs.ReflectMathWide
open Aeneas Aeneas.Std Result
namespace CrcReflectedTable32
open CrcReflectedPublic32
abbrev Crc32 := CrcPublic32.Crc32
abbrev Digest32 := CrcPublic32.Digest32

def Coherent (self : Crc32) : Prop :=
  ∀ byte : U8, (CrcPublic32.tableRead self.data byte).bv =
    (CrcReflectedWide.byteStep self.algorithm.poly.bv 0 byte.bv).reverse
theorem shifted_xor_byte (state : BitVec 32) (byte : BitVec 8) :
    ((state ^^^ byte.setWidth 32) >>> 8) = state >>> 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem lookup_canonical (self : Crc32) (ht : Coherent self) (state : U32) (byte : U8) :
    (CrcUpdate32Reflected.lookup self.data state byte).bv =
      (CrcReflectedWide.byteStep self.algorithm.poly.bv state.bv.reverse byte.bv).reverse := by
  let idx : U8 := UScalar.mk (ty := .U8) ((CrcUpdate32Reflected.indexWord state byte).bv.setWidth 8)
  have hb := CrcUpdate32Reflected.indexWord_bound state byte
  have hidx : idx.val = (CrcUpdate32Reflected.indexWord state byte).val := by
    change (CrcUpdate32Reflected.indexWord state byte).val % 256 = _
    exact Nat.mod_eq_of_lt hb
  have hcast : idx.bv.setWidth 32 = (CrcUpdate32Reflected.indexWord state byte).bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, UScalar.bv_toNat]
    change idx.val % 4294967296 = (CrcUpdate32Reflected.indexWord state byte).val
    rw [hidx]
    exact Nat.mod_eq_of_lt (by omega)
  have htidx := ht idx
  rw [CrcReflectedWide.byteStep_injection (by decide)] at htidx
  have htmodel : (CrcPublic32.tableRead self.data idx).bv =
      crc.polynomialRun self.algorithm.poly.bv.reverse true 8
        (CrcUpdate32Reflected.indexWord state byte).bv := by
    exact htidx.trans (congrArg (crc.polynomialRun self.algorithm.poly.bv.reverse true 8)
      (by
        calc
          (0 : BitVec 32).reverse ^^^ idx.bv.setWidth 32 = idx.bv.setWidth 32 := by
            apply BitVec.eq_of_getLsbD_eq
            intro i hi
            simp [BitVec.getLsbD_reverse]
          _ = _ := hcast))
  have hl : (CrcUpdate32Reflected.lookup self.data state byte).bv =
      (CrcPublic32.tableRead self.data idx).bv ^^^ (state.bv >>> 8) := by
    simp [CrcUpdate32Reflected.lookup, UScalar.bv_xor, CrcPublic32.tableRead, hidx,
      CrcUpdate32Reflected.indexWord_bound]
  rw [hl, htmodel, CrcReflectedWide.byteStep_injection (by decide)]
  rw [BitVec.reverse_reverse_eq, CrcReflectedWide.polynomialRun_split8 (by decide)
    self.algorithm.poly.bv.reverse (state.bv ^^^ byte.bv.setWidth 32), shifted_xor_byte]
  exact BitVec.xor_comm _ _

theorem run_canonical (self : Crc32) (ht : Coherent self) (state : U32) (bytes : List U8) :
    (CrcUpdate32Reflected.run self.data state bytes).bv =
      (CrcReflectedWide.run self.algorithm.poly.bv state.bv.reverse (bytes.map UScalar.bv)).reverse := by
  induction bytes generalizing state with
  | nil => exact (BitVec.reverse_reverse_eq (x := state.bv)).symm
  | cons byte bytes ih =>
    change (CrcUpdate32Reflected.run self.data (CrcUpdate32Reflected.lookup self.data state byte) bytes).bv =
      (CrcReflectedWide.run self.algorithm.poly.bv
        (CrcReflectedWide.byteStep self.algorithm.poly.bv state.bv.reverse byte.bv)
        (bytes.map UScalar.bv)).reverse
    rw [ih, lookup_canonical self ht, BitVec.reverse_reverse_eq]

theorem update_canonical (self : Crc32) (state : U32) (bytes : Slice U8)
    (ha : Domain self.algorithm) (ht : Coherent self) :
    ∃ out, CrcBody.crc32.CrcU32Table.update self state bytes = .ok out ∧
      out.bv.reverse = CrcReflectedWide.run self.algorithm.poly.bv state.bv.reverse
        (bytes.val.map UScalar.bv) := by
  obtain ⟨out, hout, hv⟩ := CrcUpdate32Reflected.update_table_total self.algorithm self.data bytes state ha.2
  refine ⟨out, hout, ?_⟩
  exact (congrArg BitVec.reverse ((congrArg UScalar.bv hv).trans
    (run_canonical self ht state bytes.val))).trans (BitVec.reverse_reverse_eq)

theorem checksum_canonical (self : Crc32) (bytes : Slice U8)
    (ha : Domain self.algorithm) (ht : Coherent self) :
    ∃ out, CrcBody.crc32.CrcU32Table.checksum self bytes = .ok out ∧
      out.bv = finish self.algorithm (CrcReflectedWide.run self.algorithm.poly.bv
        self.algorithm.init.bv (bytes.val.map UScalar.bv)) := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self (reverseScalar self.algorithm.init) bytes ha ht
  obtain ⟨out, hout, hfin⟩ := finalize_canonical self.algorithm mid ha
  refine ⟨out, ?_, ?_⟩
  · simp only [CrcBody.crc32.CrcU32Table.checksum, init_eq _ _ ha, hm, hout, bind_ok]
  · simpa only [hv, reverseScalar_bv, BitVec.reverse_reverse_eq] using hfin

theorem digest_update_canonical (self : Digest32) (bytes : Slice U8)
    (ha : Domain self.crc.algorithm) (ht : Coherent self.crc) :
    ∃ out, CrcBody.crc32.DigestAU32Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv.reverse =
        CrcReflectedWide.run self.crc.algorithm.poly.bv self.value.bv.reverse (bytes.val.map UScalar.bv) := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self.crc self.value bytes ha ht
  exact ⟨{ self with value := mid }, by simp [CrcBody.crc32.DigestAU32Table.update, hm], rfl, hv⟩

theorem digest_protocol_canonical (self : Crc32) (initial : U32) (bytes : Slice U8)
    (ha : Domain self.algorithm) (ht : Coherent self) :
    ∃ start final out,
      CrcBody.crc32.CrcU32Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc32.DigestAU32Table.update start bytes = .ok final ∧
      CrcBody.crc32.DigestAU32Table.finalize final = .ok out ∧
      out.bv = finish self.algorithm (CrcReflectedWide.run self.algorithm.poly.bv initial.bv
        (bytes.val.map UScalar.bv)) := by
  obtain ⟨final, hu, hc, hv⟩ := digest_update_canonical
    (⟨self, reverseScalar initial⟩ : Digest32) bytes ha ht
  have hfa : Domain final.crc.algorithm := by simpa only [hc] using ha
  obtain ⟨out, hout, hbv⟩ := finalize_canonical final.crc.algorithm final.value hfa
  refine ⟨⟨self, reverseScalar initial⟩, final, out, ?_, hu, hout, ?_⟩
  · simp only [CrcBody.crc32.CrcU32Table.digest_with_initial, init_eq _ _ ha,
      bind_ok, CrcBody.crc32.DigestAU32Table.new]
  · simpa only [hc, hv, reverseScalar_bv, BitVec.reverse_reverse_eq] using hbv
end CrcReflectedTable32
