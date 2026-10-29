import CrcBody.Funs
import Stage2Proofs.ByteMath
open Aeneas Aeneas.Std Result
namespace CrcBody

abbrev Crc8 := Crc U8 (Table 1#usize) (Array (Array U8 256#usize) 1#usize)
abbrev Digest8 := Digest U8 (Table 1#usize) (Array (Array U8 256#usize) 1#usize)

def FullWidth8 (a : crc_catalog.Algorithm U8) : Prop :=
  a.width = 8#u8 ∧ a.refin = false ∧ a.refout = false

theorem init8_identity (a : crc_catalog.Algorithm U8) (initial : U8)
    (ha : FullWidth8 a) : crc8.init a initial = .ok initial := by
  obtain ⟨hw, hri, _⟩ := ha
  unfold crc8.init
  simp only [hw, hri, Bool.false_eq_true, ↓reduceIte]
  have h : WP.spec (do let i ← 8#u8 - 8#u8; initial <<< i)
      (fun out => out = initial) := by
    step
    step
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    have hz : i.val = 0 := by omega
    simpa only [hz, BitVec.shiftLeft_zero] using out_post1
  obtain ⟨out, hout, rfl⟩ := crc.total_result h
  exact hout

theorem finalize8_xor (a : crc_catalog.Algorithm U8) (value : U8)
    (ha : FullWidth8 a) : crc8.finalize a value = .ok (value ^^^ a.xorout) := by
  obtain ⟨hw, hri, hro⟩ := ha
  unfold crc8.finalize
  simp only [hw, hri, hro, Bool.false_xor, Bool.false_eq_true, ↓reduceIte, bind_ok]
  have h : WP.spec (do
      let i ← 8#u8 - 8#u8
      let v ← value >>> i
      .ok (v ^^^ a.xorout)) (fun out => out = value ^^^ a.xorout) := by
    step
    step
    have hz : i.val = 0 := by omega
    have heq : v = value := by
      apply (UScalar.eq_equiv_bv_eq _ _).mpr
      simpa only [hz, BitVec.ushiftRight_zero] using v_post1
    exact congrArg (fun x : U8 => x ^^^ a.xorout) heq
  obtain ⟨out, hout, rfl⟩ := crc.total_result h
  simpa only [Aeneas.Std.bind_assoc] using hout
theorem digest8_initial (self : Crc8) (initial : U8)
    (ha : FullWidth8 self.algorithm) :
    crc8.CrcU8Table.digest_with_initial self initial = .ok ⟨self, initial⟩ := by
  simp only [crc8.CrcU8Table.digest_with_initial, init8_identity _ _ ha, bind_ok,
    crc8.DigestAU8Table.new]

theorem digest8_default (self : Crc8) (ha : FullWidth8 self.algorithm) :
    crc8.CrcU8Table.digest self = .ok ⟨self, self.algorithm.init⟩ :=
  digest8_initial self self.algorithm.init ha

theorem digest8_finalize (self : Digest8) (ha : FullWidth8 self.crc.algorithm) :
    crc8.DigestAU8Table.finalize self = .ok (self.value ^^^ self.crc.algorithm.xorout) :=
  finalize8_xor self.crc.algorithm self.value ha
end CrcBody
