import Stage2Proofs.Public8Base
import Stage2Proofs.Update8
open Aeneas Aeneas.Std Result
namespace CrcBody

def tableFunction (table : CrcUpdate8.Table) (byte : BitVec 8) : BitVec 8 :=
  (CrcUpdate8.tableRead table (UScalar.mk byte)).bv

def Coherent8 (self : Crc8) : Prop :=
  CrcCanonical8.TableValid self.algorithm.poly.bv (tableFunction self.data)

theorem fold8_bv (table : CrcUpdate8.Table) (state : U8) (bytes : List U8) :
    (CrcUpdate8.run table state bytes).bv =
      CrcCanonical8.lookupRun (tableFunction table) state.bv (bytes.map UScalar.bv) := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih =>
    simp only [CrcUpdate8.run, List.foldl_cons, List.map_cons,
      CrcCanonical8.lookupRun]
    exact ih (CrcUpdate8.lookup table state byte)

 theorem run8_canonical (self : Crc8) (ht : Coherent8 self) (state : U8) (bytes : List U8) :
    (CrcUpdate8.run self.data state bytes).bv =
      CrcCanonical8.run self.algorithm.poly.bv state.bv (bytes.map UScalar.bv) :=
  (fold8_bv self.data state bytes).trans
    (CrcCanonical8.lookupRun_correct _ _ ht _ _)
theorem update8_canonical (self : Crc8) (state : U8) (bytes : Slice U8)
    (ht : Coherent8 self) :
    ∃ out, crc8.CrcU8Table.update self state bytes = .ok out ∧
      out.bv = CrcCanonical8.run self.algorithm.poly.bv state.bv (bytes.val.map UScalar.bv) := by
  obtain ⟨out, hout, hv⟩ := CrcUpdate8.update_table_total self.algorithm self.data bytes state
  refine ⟨out, hout, ?_⟩
  exact (congrArg UScalar.bv hv).trans (run8_canonical self ht state bytes.val)

theorem checksum8_canonical (self : Crc8) (bytes : Slice U8)
    (ha : FullWidth8 self.algorithm) (ht : Coherent8 self) :
    ∃ out, crc8.CrcU8Table.checksum self bytes = .ok out ∧
      out.bv = CrcCanonical8.run self.algorithm.poly.bv self.algorithm.init.bv
        (bytes.val.map UScalar.bv) ^^^ self.algorithm.xorout.bv := by
  obtain ⟨mid, hm, hv⟩ := update8_canonical self self.algorithm.init bytes ht
  refine ⟨mid ^^^ self.algorithm.xorout, ?_, ?_⟩
  · simp only [crc8.CrcU8Table.checksum, init8_identity _ _ ha, hm, bind_ok,
      finalize8_xor _ _ ha]
  · exact congrArg (fun x : BitVec 8 => x ^^^ self.algorithm.xorout.bv) hv

theorem digest8_update_canonical (self : Digest8) (bytes : Slice U8)
    (_ha : FullWidth8 self.crc.algorithm) (ht : Coherent8 self.crc) :
    ∃ out, crc8.DigestAU8Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧
      out.value.bv = CrcCanonical8.run self.crc.algorithm.poly.bv self.value.bv
        (bytes.val.map UScalar.bv) := by
  obtain ⟨mid, hm, hv⟩ := update8_canonical self.crc self.value bytes ht
  exact ⟨{ self with value := mid }, by simp [crc8.DigestAU8Table.update, hm], rfl, hv⟩
theorem digest8_update_append (self : Digest8) (xs ys whole : Slice U8)
    (hwhole : whole.val = xs.val ++ ys.val) :
    ∃ mid final, crc8.DigestAU8Table.update self xs = .ok mid ∧
      crc8.DigestAU8Table.update mid ys = .ok final ∧
      crc8.DigestAU8Table.update self whole = .ok final := by
  obtain ⟨v1, hv1, hrun1⟩ := CrcUpdate8.update_table_total self.crc.algorithm self.crc.data xs self.value
  obtain ⟨v2, hv2, hrun2⟩ := CrcUpdate8.update_table_total self.crc.algorithm self.crc.data ys v1
  obtain ⟨v3, hv3, hrun3⟩ := CrcUpdate8.update_table_total self.crc.algorithm self.crc.data whole self.value
  have heq : v3 = v2 := by
    rw [hrun3, hwhole, CrcUpdate8.run, List.foldl_append]
    change CrcUpdate8.run self.crc.data (CrcUpdate8.run self.crc.data self.value xs.val) ys.val = v2
    rw [← hrun1, ← hrun2]
  refine ⟨{self with value := v1}, {self with value := v2}, ?_, ?_, ?_⟩
  · simp only [crc8.DigestAU8Table.update, crc8.CrcU8Table.update, hv1, bind_ok]
  · simp only [crc8.DigestAU8Table.update, crc8.CrcU8Table.update, hv2, bind_ok]
  · simp only [crc8.DigestAU8Table.update, crc8.CrcU8Table.update, hv3, bind_ok, heq]
theorem digest8_protocol_canonical (self : Crc8) (initial : U8) (bytes : Slice U8)
    (ha : FullWidth8 self.algorithm) (ht : Coherent8 self) :
    ∃ start finish out,
      crc8.CrcU8Table.digest_with_initial self initial = .ok start ∧
      crc8.DigestAU8Table.update start bytes = .ok finish ∧
      crc8.DigestAU8Table.finalize finish = .ok out ∧
      out.bv = CrcCanonical8.run self.algorithm.poly.bv initial.bv
        (bytes.val.map UScalar.bv) ^^^ self.algorithm.xorout.bv := by
  obtain ⟨finish, hu, hc, hv⟩ := digest8_update_canonical (⟨self, initial⟩ : Digest8) bytes ha ht
  have hfa : FullWidth8 finish.crc.algorithm := by simpa only [hc] using ha
  refine ⟨⟨self, initial⟩, finish, finish.value ^^^ finish.crc.algorithm.xorout,
    digest8_initial self initial ha, hu, digest8_finalize finish hfa, ?_⟩
  simpa only [hc, UScalar.bv_xor] using
    congrArg (fun x : BitVec 8 => x ^^^ self.algorithm.xorout.bv) hv
end CrcBody
