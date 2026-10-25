import Proofs.AdapterConsumption
open Aeneas Aeneas.Std Result
namespace bytes_buffers

theorem chain_remaining_spec {T U} (A : BytesBuf T) (B : BytesBuf U)
    (va : T → List U8) (vb : U → List U8) (ha : Laws A va) (hb : Laws B vb)
    (s : Chain T U) :
    chainRemaining A B s ⦃ out => out.val = Nat.min Usize.max (chainView va vb s).length ⦄ := by
  obtain ⟨a,ea,pa⟩ := wp_success (ha.remaining s.a)
  obtain ⟨b,eb,pb⟩ := wp_success (hb.remaining s.b)
  unfold chainRemaining bytes_adapters.bytes.buf.chain.Chain.Insts.BytesBufBuf_implBuf.remaining
  rw [ea,bind_ok,eb,bind_ok]
  simp only [WP.spec_ok]
  simp only [core.num.Usize.saturating_add, UScalar.saturating_add, UScalar.val, BitVec.toNat_ofNat]
  rw [UScalar.max_USize_eq]
  change Nat.min Usize.max (a.val + b.val) % 2 ^ UScalarTy.Usize.numBits =
    Nat.min Usize.max (chainView va vb s).length
  have hm : Nat.min Usize.max (a.val + b.val) < 2 ^ UScalarTy.Usize.numBits := by
    have := Nat.min_le_left Usize.max (a.val+b.val)
    simp [Usize.max, Usize.numBits] at *
  rw [Nat.mod_eq_of_lt hm]
  rw [pa,pb]
  simp only [chainView, List.length_append]
  simp only [Nat.min_def]
  split_ifs <;> omega

theorem chain_chunk_exact {T U} (A : BytesBuf T) (B : BytesBuf U)
    (va : T → List U8) (ha : Laws A va) (s : Chain T U)
    (a b : Slice U8) (ea : A.chunk s.a = .ok a) (eb : B.chunk s.b = .ok b) :
    chainChunk A B s ⦃ out => out = if va s.a = [] then b else a ⦄ := by
  obtain ⟨r,er,pr⟩ := wp_success (ha.has_remaining s.a)
  unfold chainChunk bytes_adapters.bytes.buf.chain.Chain.Insts.BytesBufBuf_implBuf.chunk
  rw [er,bind_ok,pr]
  by_cases h : va s.a = [] <;> simp [h,ea,eb,WP.spec_ok]

theorem chain_advance_spec {T U} (A : BytesBuf T) (B : BytesBuf U)
    (va : T → List U8) (vb : U → List U8) (ha : Laws A va) (hb : Laws B vb)
    (s : Chain T U) (n : Usize) (hn : n.val ≤ (chainView va vb s).length) :
    chainAdvance A B s n ⦃ out =>
      va out.a = (va s.a).drop n.val ∧
      vb out.b = (vb s.b).drop (n.val - (va s.a).length) ∧
      chainView va vb out = (chainView va vb s).drop n.val ⦄ := by
  obtain ⟨a,ea,pa⟩ := wp_success (ha.remaining s.a)
  have hnmax : n.val ≤ Usize.max := by
    have hh := n.hmax
    simp [Usize.max, Usize.numBits, UScalarTy.numBits] at *
    omega
  have pale : a.val ≤ (va s.a).length := by rw [pa]; exact Nat.min_le_right _ _
  have pamax : a.val ≤ Usize.max := by rw [pa]; exact Nat.min_le_left _ _
  have hmax : 0 < Usize.max := by
    rcases Usize.bounds_eq with h | h <;> simp [h, U32.max_eq, U64.max_eq]
  unfold chainAdvance bytes_adapters.bytes.buf.chain.Chain.Insts.BytesBufBuf_implBuf.advance
  rw [ea,bind_ok]
  by_cases hz : a = 0#usize
  · have hv : va s.a = [] := by
      have hh : a.val = 0 := by rw [hz]; rfl
      rw [pa] at hh
      have : (va s.a).length = 0 := by
        simp only [Nat.min_def] at hh
        split_ifs at hh <;> omega
      simpa using this
    have hn' : n.val ≤ (vb s.b).length := by simpa [chainView,hv] using hn
    obtain ⟨b,eb,pb⟩ := wp_success (hb.advance s.b n hn')
    simp [hz,eb,WP.spec_ok,chainView,hv,pb]
  · have haz : (a != 0#usize) = true := by simp [hz]
    simp only [haz, ↓reduceIte]
    by_cases hc : n.val ≤ a.val
    · have hscalar : a ≥ n := by scalar_tac
      have hn' : n.val ≤ (va s.a).length := by omega
      obtain ⟨v,ev,pv⟩ := wp_success (ha.advance s.a n hn')
      simp only [hscalar, ↓reduceIte, ev, bind_ok, WP.spec_ok]
      simp [pv,chainView,List.drop_append, Nat.sub_eq_zero_of_le hn']
    · have hscalar : ¬ a ≥ n := by scalar_tac
      have haexact : a.val = (va s.a).length := by
        simp only [Nat.min_def] at pa
        split_ifs at pa <;> omega
      obtain ⟨v,ev,pv⟩ := wp_success (ha.advance s.a a (by omega))
      simp only [hscalar, ↓reduceIte, ev, bind_ok]
      step as ⟨rem, hrem⟩
      have hn' : rem.val ≤ (vb s.b).length := by simp only [chainView,List.length_append] at hn; omega
      obtain ⟨w,ew,pw⟩ := wp_success (hb.advance s.b rem hn')
      rw [ew,bind_ok]
      simp only [WP.spec_ok]
      have he : va v = [] := by rw [pv,haexact]; simp
      have hd : (va s.a).drop n.val = [] := List.drop_eq_nil_of_le (by omega)
      simp [he,hd,pw,chainView,List.drop_append,haexact,hrem]

theorem chain_has_remaining_spec {T U} (A : BytesBuf T) (B : BytesBuf U)
    (va : T → List U8) (vb : U → List U8) (ha : Laws A va) (hb : Laws B vb)
    (s : Chain T U) :
    bytes_adapters.chain_has_remaining A B s ⦃ out =>
      out = decide (chainView va vb s ≠ []) ⦄ := by
  obtain ⟨r,er,pr⟩ := wp_success (chain_remaining_spec A B va vb ha hb s)
  unfold bytes_adapters.chain_has_remaining
    bytes_adapters.bytes.buf.chain.Chain.Insts.BytesBufBuf_implBuf.has_remaining
  change bytes_adapters.bytes.buf.chain.Chain.Insts.BytesBufBuf_implBuf.remaining A B s = .ok r at er
  rw [er,bind_ok,WP.spec_ok]
  have hm : 0 < Usize.max := by
    rcases Usize.bounds_eq with h | h <;> simp [h,U32.max_eq,U64.max_eq]
  have hh : (r > 0#usize) ↔ chainView va vb s ≠ [] := by
    simp only [UScalar.lt_equiv]
    rw [pr]
    simp only [Nat.min_def]
    split_ifs <;> simp_all [← List.length_pos_iff_ne_nil]
    omega
  simp only [hh]

def chainBuf {T U} (A : BytesBuf T) (B : BytesBuf U) : BytesBuf (Chain T U) where
  remaining := chainRemaining A B
  chunk := chainChunk A B
  advance := chainAdvance A B
  has_remaining := bytes_adapters.chain_has_remaining A B

theorem chain_laws {T U} (A : BytesBuf T) (B : BytesBuf U)
    (va : T → List U8) (vb : U → List U8) (ha : Laws A va) (hb : Laws B vb) :
    Laws (chainBuf A B) (chainView va vb) := by
  constructor
  · exact chain_remaining_spec A B va vb ha hb
  · intro s
    obtain ⟨a,ea,hpa,hea⟩ := wp_success (ha.chunk s.a)
    obtain ⟨b,eb,hpb,heb⟩ := wp_success (hb.chunk s.b)
    obtain ⟨r,er,pr⟩ := wp_success (chain_chunk_exact A B va ha s a b ea eb)
    change chainChunk A B s ⦃ _ ⦄
    rw [er,WP.spec_ok,pr]
    by_cases he : va s.a = []
    · simp [he,chainView,heb,hpb]
    · simp only [he,↓reduceIte]
      constructor
      · exact hpa.trans (List.prefix_append _ _)
      · simp [hea,he,chainView]
  · intro s n hn
    obtain ⟨r,er,pr⟩ := wp_success (chain_advance_spec A B va vb ha hb s n hn)
    change chainAdvance A B s n ⦃ _ ⦄
    rw [er,WP.spec_ok]
    exact pr.2.2
  · exact chain_has_remaining_spec A B va vb ha hb

theorem concrete_chain_remaining (s : Chain (Slice U8) (Slice U8)) :
    bytes_adapters.concrete_chain_remaining s ⦃ out =>
      out.val = Nat.min Usize.max (chainView (fun x => x.val) (fun x => x.val) s).length ⦄ :=
  chain_remaining_spec sliceBuf sliceBuf _ _ slice_laws slice_laws s

theorem concrete_chain_chunk (s : Chain (Slice U8) (Slice U8)) :
    bytes_adapters.concrete_chain_chunk s ⦃ out =>
      out = if s.a.val = [] then s.b else s.a ⦄ :=
  chain_chunk_exact sliceBuf sliceBuf (fun x => x.val) slice_laws s s.a s.b rfl rfl

theorem concrete_chain_advance (s : Chain (Slice U8) (Slice U8)) (n : Usize)
    (hn : n.val ≤ (chainView (fun x => x.val) (fun x => x.val) s).length) :
    bytes_adapters.concrete_chain_advance s n ⦃ out =>
      out.a.val = s.a.val.drop n.val ∧
      out.b.val = s.b.val.drop (n.val - s.a.val.length) ∧
      chainView (fun x => x.val) (fun x => x.val) out =
        (chainView (fun x => x.val) (fun x => x.val) s).drop n.val ⦄ :=
  chain_advance_spec sliceBuf sliceBuf _ _ slice_laws slice_laws s n hn

theorem concrete_chain_has_remaining (s : Chain (Slice U8) (Slice U8)) :
    bytes_adapters.chain_has_remaining sliceBuf sliceBuf s ⦃ out =>
      out = decide (chainView (fun x => x.val) (fun x => x.val) s ≠ []) ⦄ :=
  chain_has_remaining_spec sliceBuf sliceBuf _ _ slice_laws slice_laws s

theorem chain_advance_sequence {T U} (A : BytesBuf T) (B : BytesBuf U)
    (va : T → List U8) (vb : U → List U8) (ha : Laws A va) (hb : Laws B vb)
    (s : Chain T U) (n m : Usize)
    (hn : n.val + m.val ≤ (chainView va vb s).length) :
    (do let mid ← chainAdvance A B s n; chainAdvance A B mid m) ⦃ out =>
      chainView va vb out = (chainView va vb s).drop (n.val + m.val) ⦄ := by
  obtain ⟨mid,em,pm⟩ := wp_success (chain_advance_spec A B va vb ha hb s n (by omega))
  have hm : m.val ≤ (chainView va vb mid).length := by
    rw [pm.2.2,List.length_drop]
    omega
  obtain ⟨out,eo,po⟩ := wp_success (chain_advance_spec A B va vb ha hb mid m hm)
  rw [em,bind_ok,eo,WP.spec_ok,po.2.2,pm.2.2,List.drop_drop]

theorem take_chain_laws {T U} (A : BytesBuf T) (B : BytesBuf U)
    (va : T → List U8) (vb : U → List U8) (ha : Laws A va) (hb : Laws B vb) :
    Laws (takeBuf (chainBuf A B)) (takeView (chainView va vb)) :=
  take_laws _ _ (chain_laws A B va vb ha hb)


theorem chain_dictionary_exact {T U} (A : BytesBuf T) (B : BytesBuf U) :
    chainBuf A B = bytes_adapters.bytes.buf.chain.Chain.Insts.BytesBufBuf_implBuf A B := rfl

theorem nested_take_chain_dispatch_exact
    (s : Take (Chain (Slice U8) (Slice U8))) (n : Usize) :
    bytes_adapters.concrete_take_chain_advance s n =
      takeAdvance (chainBuf sliceBuf sliceBuf) s n := rfl
end bytes_buffers

