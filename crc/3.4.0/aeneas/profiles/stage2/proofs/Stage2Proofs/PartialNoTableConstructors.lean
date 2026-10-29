import Stage2Proofs.Partial8
import Stage2Proofs.Partial16
import Stage2Proofs.Partial32
import Stage2Proofs.Partial64
import Stage2Proofs.Partial128
import Stage2Proofs.WidthEndpoints
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace CrcPartialNoTableConstructors
abbrev NoCrc8 := CrcBody.Crc U8 (CrcBody.Table 0#usize) (Array (Array U8 256#usize) 0#usize)
abbrev Table0 := Array (Array U8 256#usize) 0#usize

theorem zero_loop8 (reflect : Bool) (poly : U8) (table : Table0) :
    WP.spec (CrcBody.table.crc8_table_loop0 reflect poly table 0#usize)
      (fun out => out = table) := by
  unfold CrcBody.table.crc8_table_loop0
  apply loop.spec_decr_nat
    (measure := fun _ : Table0 × Usize => 0)
    (inv := fun x : Table0 × Usize => x.1 = table)
  · intro x hx
    rcases x with ⟨t,i⟩
    dsimp only at hx
    unfold CrcBody.table.crc8_table_loop0.body
    simp only [show ¬(0#usize : Usize) > 0#usize by decide, ↓reduceIte]
    split <;> simpa only [WP.spec_ok] using hx
  · rfl

theorem table_total8 (a : CrcBody.crc_catalog.Algorithm U8) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 8) :
    ∃ out : Table0, CrcBody.table.crc8_table 0#usize a.width a.poly a.refin = .ok out := by
  let p : U8 := UScalar.mk (CrcWidthEndpoints.storedEncode 8 a.refin (a.poly.bv.setWidth a.width.val))
  have hp : CrcBody.crc8.init a a.poly = .ok p := CrcWidthEndpoints.init8_eq_encoded a a.poly hw
  have heq : CrcBody.table.crc8_table 0#usize a.width a.poly a.refin = (do
      let poly ← CrcBody.crc8.init a a.poly
      let t ← CrcBody.table.crc8_table_loop0 a.refin poly
        (Array.repeat 0#usize (Array.repeat 256#usize 0#u8)) 0#usize
      .ok t) := by
    unfold CrcBody.table.crc8_table CrcBody.crc8.init
    simp only [show ¬(0#usize : Usize) > 1#usize by decide, ↓reduceIte]
  obtain ⟨out,ho,_⟩ := crc.total_result (zero_loop8 a.refin p
    (Array.repeat 0#usize (Array.repeat 256#usize 0#u8)))
  exact ⟨out, by simp only [heq,hp,ho,bind_ok]⟩

theorem new_total8 (a : CrcBody.crc_catalog.Algorithm U8) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 8) :
    ∃ self : NoCrc8, CrcBody.crc8.CrcU8Table.new 0#usize a = .ok self ∧
      self.algorithm = a := by
  obtain ⟨t,ht⟩ := table_total8 a hw
  exact ⟨⟨a,t⟩, by simp only [CrcBody.crc8.CrcU8Table.new,ht,bind_ok], rfl⟩

abbrev NoCrc16 := CrcBody.Crc U16 (CrcBody.Table 0#usize) (Array (Array U16 256#usize) 0#usize)
abbrev Table0_16 := Array (Array U16 256#usize) 0#usize

theorem zero_loop16 (reflect : Bool) (poly : U16) (table : Table0_16) :
    WP.spec (CrcBody.table.crc16_table_loop0 reflect poly table 0#usize)
      (fun out => out = table) := by
  unfold CrcBody.table.crc16_table_loop0
  apply loop.spec_decr_nat
    (measure := fun _ : Table0_16 × Usize => 0)
    (inv := fun x : Table0_16 × Usize => x.1 = table)
  · intro x hx
    rcases x with ⟨t,i⟩
    dsimp only at hx
    unfold CrcBody.table.crc16_table_loop0.body
    simp only [show ¬(0#usize : Usize) > 0#usize by decide, ↓reduceIte]
    split <;> simpa only [WP.spec_ok] using hx
  · rfl

theorem table_total16 (a : CrcBody.crc_catalog.Algorithm U16) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 16) :
    ∃ out : Table0_16, CrcBody.table.crc16_table 0#usize a.width a.poly a.refin = .ok out := by
  let p : U16 := UScalar.mk (CrcWidthEndpoints.storedEncode 16 a.refin (a.poly.bv.setWidth a.width.val))
  have hp : CrcBody.crc16.init a a.poly = .ok p := CrcWidthEndpoints.init16_eq_encoded a a.poly hw
  have heq : CrcBody.table.crc16_table 0#usize a.width a.poly a.refin = (do
      let poly ← CrcBody.crc16.init a a.poly
      let t ← CrcBody.table.crc16_table_loop0 a.refin poly
        (Array.repeat 0#usize (Array.repeat 256#usize 0#u16)) 0#usize
      .ok t) := by
    unfold CrcBody.table.crc16_table CrcBody.crc16.init
    simp only [show ¬(0#usize : Usize) > 1#usize by decide, ↓reduceIte]
  obtain ⟨out,ho,_⟩ := crc.total_result (zero_loop16 a.refin p
    (Array.repeat 0#usize (Array.repeat 256#usize 0#u16)))
  exact ⟨out, by simp only [heq,hp,ho,bind_ok]⟩

theorem new_total16 (a : CrcBody.crc_catalog.Algorithm U16) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 16) :
    ∃ self : NoCrc16, CrcBody.crc16.CrcU16Table.new 0#usize a = .ok self ∧
      self.algorithm = a := by
  obtain ⟨t,ht⟩ := table_total16 a hw
  exact ⟨⟨a,t⟩, by simp only [CrcBody.crc16.CrcU16Table.new,ht,bind_ok], rfl⟩

abbrev NoCrc32 := CrcBody.Crc U32 (CrcBody.Table 0#usize) (Array (Array U32 256#usize) 0#usize)
abbrev Table0_32 := Array (Array U32 256#usize) 0#usize

theorem zero_loop32 (reflect : Bool) (poly : U32) (table : Table0_32) :
    WP.spec (CrcBody.table.crc32_table_loop0 reflect poly table 0#usize)
      (fun out => out = table) := by
  unfold CrcBody.table.crc32_table_loop0
  apply loop.spec_decr_nat
    (measure := fun _ : Table0_32 × Usize => 0)
    (inv := fun x : Table0_32 × Usize => x.1 = table)
  · intro x hx
    rcases x with ⟨t,i⟩
    dsimp only at hx
    unfold CrcBody.table.crc32_table_loop0.body
    simp only [show ¬(0#usize : Usize) > 0#usize by decide, ↓reduceIte]
    split <;> simpa only [WP.spec_ok] using hx
  · rfl

theorem table_total32 (a : CrcBody.crc_catalog.Algorithm U32) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 32) :
    ∃ out : Table0_32, CrcBody.table.crc32_table 0#usize a.width a.poly a.refin = .ok out := by
  let p : U32 := UScalar.mk (CrcWidthEndpoints.storedEncode 32 a.refin (a.poly.bv.setWidth a.width.val))
  have hp : CrcBody.crc32.init a a.poly = .ok p := CrcWidthEndpoints.init32_eq_encoded a a.poly hw
  have heq : CrcBody.table.crc32_table 0#usize a.width a.poly a.refin = (do
      let poly ← CrcBody.crc32.init a a.poly
      let t ← CrcBody.table.crc32_table_loop0 a.refin poly
        (Array.repeat 0#usize (Array.repeat 256#usize 0#u32)) 0#usize
      .ok t) := by
    unfold CrcBody.table.crc32_table CrcBody.crc32.init
    simp only [show ¬(0#usize : Usize) > 1#usize by decide, ↓reduceIte]
  obtain ⟨out,ho,_⟩ := crc.total_result (zero_loop32 a.refin p
    (Array.repeat 0#usize (Array.repeat 256#usize 0#u32)))
  exact ⟨out, by simp only [heq,hp,ho,bind_ok]⟩

theorem new_total32 (a : CrcBody.crc_catalog.Algorithm U32) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 32) :
    ∃ self : NoCrc32, CrcBody.crc32.CrcU32Table.new 0#usize a = .ok self ∧
      self.algorithm = a := by
  obtain ⟨t,ht⟩ := table_total32 a hw
  exact ⟨⟨a,t⟩, by simp only [CrcBody.crc32.CrcU32Table.new,ht,bind_ok], rfl⟩

abbrev NoCrc64 := CrcBody.Crc U64 (CrcBody.Table 0#usize) (Array (Array U64 256#usize) 0#usize)
abbrev Table0_64 := Array (Array U64 256#usize) 0#usize

theorem zero_loop64 (reflect : Bool) (poly : U64) (table : Table0_64) :
    WP.spec (CrcBody.table.crc64_table_loop0 reflect poly table 0#usize)
      (fun out => out = table) := by
  unfold CrcBody.table.crc64_table_loop0
  apply loop.spec_decr_nat
    (measure := fun _ : Table0_64 × Usize => 0)
    (inv := fun x : Table0_64 × Usize => x.1 = table)
  · intro x hx
    rcases x with ⟨t,i⟩
    dsimp only at hx
    unfold CrcBody.table.crc64_table_loop0.body
    simp only [show ¬(0#usize : Usize) > 0#usize by decide, ↓reduceIte]
    split <;> simpa only [WP.spec_ok] using hx
  · rfl

theorem table_total64 (a : CrcBody.crc_catalog.Algorithm U64) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 64) :
    ∃ out : Table0_64, CrcBody.table.crc64_table 0#usize a.width a.poly a.refin = .ok out := by
  let p : U64 := UScalar.mk (CrcWidthEndpoints.storedEncode 64 a.refin (a.poly.bv.setWidth a.width.val))
  have hp : CrcBody.crc64.init a a.poly = .ok p := CrcWidthEndpoints.init64_eq_encoded a a.poly hw
  have heq : CrcBody.table.crc64_table 0#usize a.width a.poly a.refin = (do
      let poly ← CrcBody.crc64.init a a.poly
      let t ← CrcBody.table.crc64_table_loop0 a.refin poly
        (Array.repeat 0#usize (Array.repeat 256#usize 0#u64)) 0#usize
      .ok t) := by
    unfold CrcBody.table.crc64_table CrcBody.crc64.init
    simp only [show ¬(0#usize : Usize) > 1#usize by decide, ↓reduceIte]
  obtain ⟨out,ho,_⟩ := crc.total_result (zero_loop64 a.refin p
    (Array.repeat 0#usize (Array.repeat 256#usize 0#u64)))
  exact ⟨out, by simp only [heq,hp,ho,bind_ok]⟩

theorem new_total64 (a : CrcBody.crc_catalog.Algorithm U64) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 64) :
    ∃ self : NoCrc64, CrcBody.crc64.CrcU64Table.new 0#usize a = .ok self ∧
      self.algorithm = a := by
  obtain ⟨t,ht⟩ := table_total64 a hw
  exact ⟨⟨a,t⟩, by simp only [CrcBody.crc64.CrcU64Table.new,ht,bind_ok], rfl⟩

abbrev NoCrc128 := CrcBody.Crc U128 (CrcBody.Table 0#usize) (Array (Array U128 256#usize) 0#usize)
abbrev Table0_128 := Array (Array U128 256#usize) 0#usize

theorem zero_loop128 (reflect : Bool) (poly : U128) (table : Table0_128) :
    WP.spec (CrcBody.table.crc128_table_loop0 reflect poly table 0#usize)
      (fun out => out = table) := by
  unfold CrcBody.table.crc128_table_loop0
  apply loop.spec_decr_nat
    (measure := fun _ : Table0_128 × Usize => 0)
    (inv := fun x : Table0_128 × Usize => x.1 = table)
  · intro x hx
    rcases x with ⟨t,i⟩
    dsimp only at hx
    unfold CrcBody.table.crc128_table_loop0.body
    simp only [show ¬(0#usize : Usize) > 0#usize by decide, ↓reduceIte]
    split <;> simpa only [WP.spec_ok] using hx
  · rfl

theorem table_total128 (a : CrcBody.crc_catalog.Algorithm U128) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 128) :
    ∃ out : Table0_128, CrcBody.table.crc128_table 0#usize a.width a.poly a.refin = .ok out := by
  let p : U128 := UScalar.mk (CrcWidthEndpoints.storedEncode 128 a.refin (a.poly.bv.setWidth a.width.val))
  have hp : CrcBody.crc128.init a a.poly = .ok p := CrcWidthEndpoints.init128_eq_encoded a a.poly hw
  have heq : CrcBody.table.crc128_table 0#usize a.width a.poly a.refin = (do
      let poly ← CrcBody.crc128.init a a.poly
      let t ← CrcBody.table.crc128_table_loop0 a.refin poly
        (Array.repeat 0#usize (Array.repeat 256#usize 0#u128)) 0#usize
      .ok t) := by
    unfold CrcBody.table.crc128_table CrcBody.crc128.init
    simp only [show ¬(0#usize : Usize) > 1#usize by decide, ↓reduceIte]
  obtain ⟨out,ho,_⟩ := crc.total_result (zero_loop128 a.refin p
    (Array.repeat 0#usize (Array.repeat 256#usize 0#u128)))
  exact ⟨out, by simp only [heq,hp,ho,bind_ok]⟩

theorem new_total128 (a : CrcBody.crc_catalog.Algorithm U128) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 128) :
    ∃ self : NoCrc128, CrcBody.crc128.CrcU128Table.new 0#usize a = .ok self ∧
      self.algorithm = a := by
  obtain ⟨t,ht⟩ := table_total128 a hw
  exact ⟨⟨a,t⟩, by simp only [CrcBody.crc128.CrcU128Table.new,ht,bind_ok], rfl⟩

theorem checksum8 (self : NoCrc8) (bytes : Slice U8)
    (poly xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 8)
    (hp : self.algorithm.poly.bv = poly.setWidth 8)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 8) :
    ∃ out, CrcBody.crc8.CrcU8Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout poly
        (self.algorithm.init.bv.setWidth self.algorithm.width.val) xorout
        (bytes.val.map UScalar.bv)).setWidth 8 := by
  let initial := self.algorithm.init.bv.setWidth self.algorithm.width.val
  let encoded : U8 := UScalar.mk (CrcPartialSpec.physical 8 self.algorithm.refin initial)
  have hinit : CrcBody.crc8.init self.algorithm self.algorithm.init = .ok encoded :=
    CrcWidthEndpoints.init8_eq_encoded self.algorithm self.algorithm.init hw
  obtain ⟨mid,hm,hmid⟩ := CrcPartial8.update_notable_encoded self bytes poly initial hw hp
  change CrcBody.crc8.CrcU8Table.update self encoded bytes = .ok mid at hm
  let finalState := CrcPartialSpec.run self.algorithm.refin poly initial (bytes.val.map UScalar.bv)
  have hmid' : mid.bv = CrcPartialSpec.physical 8 self.algorithm.refin finalState := hmid
  obtain ⟨out,ho,hv⟩ := CrcWidthEndpoints.finalize8_encoded self.algorithm mid xorout finalState hw hx hmid'
  exact ⟨out, by simp only [CrcBody.crc8.CrcU8Table.checksum,hinit,hm,ho,bind_ok], hv⟩

theorem new_checksum8 (a : CrcBody.crc_catalog.Algorithm U8)
    (poly xorout : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 8)
    (hp : a.poly.bv = poly.setWidth 8) (hx : a.xorout.bv = xorout.setWidth 8)
    (bytes : Slice U8) :
    ∃ self : NoCrc8, CrcBody.crc8.CrcU8Table.new 0#usize a = .ok self ∧
      ∃ out, CrcBody.crc8.CrcU8Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum a.refin a.refout poly
        (a.init.bv.setWidth a.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 8 := by
  obtain ⟨self,hs,ha⟩ := new_total8 a hw
  cases self with
  | mk algorithm data =>
    dsimp only at ha
    subst algorithm
    exact ⟨⟨a,data⟩,hs,checksum8 ⟨a,data⟩ bytes poly xorout hw hp hx⟩

theorem checksum16 (self : NoCrc16) (bytes : Slice U8)
    (poly xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 16)
    (hp : self.algorithm.poly.bv = poly.setWidth 16)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 16) :
    ∃ out, CrcBody.crc16.CrcU16Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout poly
        (self.algorithm.init.bv.setWidth self.algorithm.width.val) xorout
        (bytes.val.map UScalar.bv)).setWidth 16 := by
  let initial := self.algorithm.init.bv.setWidth self.algorithm.width.val
  let encoded : U16 := UScalar.mk (CrcPartialSpec.physical 16 self.algorithm.refin initial)
  have hinit : CrcBody.crc16.init self.algorithm self.algorithm.init = .ok encoded :=
    CrcWidthEndpoints.init16_eq_encoded self.algorithm self.algorithm.init hw
  obtain ⟨mid,hm,hmid⟩ := CrcPartial16.update_notable_encoded self bytes poly initial hw hp
  change CrcBody.crc16.CrcU16Table.update self encoded bytes = .ok mid at hm
  let finalState := CrcPartialSpec.run self.algorithm.refin poly initial (bytes.val.map UScalar.bv)
  have hmid' : mid.bv = CrcPartialSpec.physical 16 self.algorithm.refin finalState := hmid
  obtain ⟨out,ho,hv⟩ := CrcWidthEndpoints.finalize16_encoded self.algorithm mid xorout finalState hw hx hmid'
  exact ⟨out, by simp only [CrcBody.crc16.CrcU16Table.checksum,hinit,hm,ho,bind_ok], hv⟩

theorem new_checksum16 (a : CrcBody.crc_catalog.Algorithm U16)
    (poly xorout : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 16)
    (hp : a.poly.bv = poly.setWidth 16) (hx : a.xorout.bv = xorout.setWidth 16)
    (bytes : Slice U8) :
    ∃ self : NoCrc16, CrcBody.crc16.CrcU16Table.new 0#usize a = .ok self ∧
      ∃ out, CrcBody.crc16.CrcU16Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum a.refin a.refout poly
        (a.init.bv.setWidth a.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 16 := by
  obtain ⟨self,hs,ha⟩ := new_total16 a hw
  cases self with
  | mk algorithm data =>
    dsimp only at ha
    subst algorithm
    exact ⟨⟨a,data⟩,hs,checksum16 ⟨a,data⟩ bytes poly xorout hw hp hx⟩

theorem checksum32 (self : NoCrc32) (bytes : Slice U8)
    (poly xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 32)
    (hp : self.algorithm.poly.bv = poly.setWidth 32)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 32) :
    ∃ out, CrcBody.crc32.CrcU32Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout poly
        (self.algorithm.init.bv.setWidth self.algorithm.width.val) xorout
        (bytes.val.map UScalar.bv)).setWidth 32 := by
  let initial := self.algorithm.init.bv.setWidth self.algorithm.width.val
  let encoded : U32 := UScalar.mk (CrcPartialSpec.physical 32 self.algorithm.refin initial)
  have hinit : CrcBody.crc32.init self.algorithm self.algorithm.init = .ok encoded :=
    CrcWidthEndpoints.init32_eq_encoded self.algorithm self.algorithm.init hw
  obtain ⟨mid,hm,hmid⟩ := CrcPartial32.update_notable self poly initial encoded bytes hw hp rfl
  change CrcBody.crc32.CrcU32Table.update self encoded bytes = .ok mid at hm
  let finalState := CrcPartialSpec.run self.algorithm.refin poly initial (bytes.val.map UScalar.bv)
  have hmid' : mid.bv = CrcPartialSpec.physical 32 self.algorithm.refin finalState := hmid
  obtain ⟨out,ho,hv⟩ := CrcWidthEndpoints.finalize32_encoded self.algorithm mid xorout finalState hw hx hmid'
  exact ⟨out, by simp only [CrcBody.crc32.CrcU32Table.checksum,hinit,hm,ho,bind_ok], hv⟩

theorem new_checksum32 (a : CrcBody.crc_catalog.Algorithm U32)
    (poly xorout : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 32)
    (hp : a.poly.bv = poly.setWidth 32) (hx : a.xorout.bv = xorout.setWidth 32)
    (bytes : Slice U8) :
    ∃ self : NoCrc32, CrcBody.crc32.CrcU32Table.new 0#usize a = .ok self ∧
      ∃ out, CrcBody.crc32.CrcU32Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum a.refin a.refout poly
        (a.init.bv.setWidth a.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 32 := by
  obtain ⟨self,hs,ha⟩ := new_total32 a hw
  cases self with
  | mk algorithm data =>
    dsimp only at ha
    subst algorithm
    exact ⟨⟨a,data⟩,hs,checksum32 ⟨a,data⟩ bytes poly xorout hw hp hx⟩

theorem checksum64 (self : NoCrc64) (bytes : Slice U8)
    (poly xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 64)
    (hp : self.algorithm.poly.bv = poly.setWidth 64)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 64) :
    ∃ out, CrcBody.crc64.CrcU64Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout poly
        (self.algorithm.init.bv.setWidth self.algorithm.width.val) xorout
        (bytes.val.map UScalar.bv)).setWidth 64 := by
  let initial := self.algorithm.init.bv.setWidth self.algorithm.width.val
  let encoded : U64 := UScalar.mk (CrcPartialSpec.physical 64 self.algorithm.refin initial)
  have hinit : CrcBody.crc64.init self.algorithm self.algorithm.init = .ok encoded :=
    CrcWidthEndpoints.init64_eq_encoded self.algorithm self.algorithm.init hw
  obtain ⟨mid,hm,hmid⟩ := CrcPartial64.update_notable self hw poly initial hp bytes
  change CrcBody.crc64.CrcU64Table.update self encoded bytes = .ok mid at hm
  let finalState := CrcPartialSpec.run self.algorithm.refin poly initial (bytes.val.map UScalar.bv)
  have hmid' : mid.bv = CrcPartialSpec.physical 64 self.algorithm.refin finalState := hmid
  obtain ⟨out,ho,hv⟩ := CrcWidthEndpoints.finalize64_encoded self.algorithm mid xorout finalState hw hx hmid'
  exact ⟨out, by simp only [CrcBody.crc64.CrcU64Table.checksum,hinit,hm,ho,bind_ok], hv⟩

theorem new_checksum64 (a : CrcBody.crc_catalog.Algorithm U64)
    (poly xorout : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 64)
    (hp : a.poly.bv = poly.setWidth 64) (hx : a.xorout.bv = xorout.setWidth 64)
    (bytes : Slice U8) :
    ∃ self : NoCrc64, CrcBody.crc64.CrcU64Table.new 0#usize a = .ok self ∧
      ∃ out, CrcBody.crc64.CrcU64Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum a.refin a.refout poly
        (a.init.bv.setWidth a.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 64 := by
  obtain ⟨self,hs,ha⟩ := new_total64 a hw
  cases self with
  | mk algorithm data =>
    dsimp only at ha
    subst algorithm
    exact ⟨⟨a,data⟩,hs,checksum64 ⟨a,data⟩ bytes poly xorout hw hp hx⟩

theorem checksum128 (self : NoCrc128) (bytes : Slice U8)
    (poly xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 128)
    (hp : self.algorithm.poly.bv = poly.setWidth 128)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 128) :
    ∃ out, CrcBody.crc128.CrcU128Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout poly
        (self.algorithm.init.bv.setWidth self.algorithm.width.val) xorout
        (bytes.val.map UScalar.bv)).setWidth 128 := by
  let initial := self.algorithm.init.bv.setWidth self.algorithm.width.val
  let encoded : U128 := UScalar.mk (CrcPartialSpec.physical 128 self.algorithm.refin initial)
  have hinit : CrcBody.crc128.init self.algorithm self.algorithm.init = .ok encoded :=
    CrcWidthEndpoints.init128_eq_encoded self.algorithm self.algorithm.init hw
  obtain ⟨mid,hm,hmid⟩ := CrcPartial128.update_notable self poly initial encoded bytes hw hp rfl
  change CrcBody.crc128.CrcU128Table.update self encoded bytes = .ok mid at hm
  let finalState := CrcPartialSpec.run self.algorithm.refin poly initial (bytes.val.map UScalar.bv)
  have hmid' : mid.bv = CrcPartialSpec.physical 128 self.algorithm.refin finalState := hmid
  obtain ⟨out,ho,hv⟩ := CrcWidthEndpoints.finalize128_encoded self.algorithm mid xorout finalState hw hx hmid'
  exact ⟨out, by simp only [CrcBody.crc128.CrcU128Table.checksum,hinit,hm,ho,bind_ok], hv⟩

theorem new_checksum128 (a : CrcBody.crc_catalog.Algorithm U128)
    (poly xorout : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 128)
    (hp : a.poly.bv = poly.setWidth 128) (hx : a.xorout.bv = xorout.setWidth 128)
    (bytes : Slice U8) :
    ∃ self : NoCrc128, CrcBody.crc128.CrcU128Table.new 0#usize a = .ok self ∧
      ∃ out, CrcBody.crc128.CrcU128Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum a.refin a.refout poly
        (a.init.bv.setWidth a.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 128 := by
  obtain ⟨self,hs,ha⟩ := new_total128 a hw
  cases self with
  | mk algorithm data =>
    dsimp only at ha
    subst algorithm
    exact ⟨⟨a,data⟩,hs,checksum128 ⟨a,data⟩ bytes poly xorout hw hp hx⟩

end CrcPartialNoTableConstructors
