import Proofs.CidrModel

/-! Mathematical capacity obligations for the corrected heapless candidate.
The text equalities initially refer only to the supplied external text functions;
`StandardDisplayBridge` separately assumes their correspondence with standard
address Display. Abstract writes may be split into arbitrary chunks, but no theorem
here connects them to an actual `fmt::Write` callback sequence. The `Except`
serializer observation models a terminating pure success/error result; external
panic, divergence, effects, and allocations are not represented. These statements
do not assert that the extracted application satisfies any external hypothesis. -/

namespace HeaplessCandidateMath

open Aeneas.Std

theorem decimal_prefix4_length (p : U8) (hp : p.val ≤ 32) :
    (Nat.repr p.val).length ≤ 2 := by
  apply (Nat.length_repr_le_iff (by decide : 0 < 2)).2
  omega

theorem decimal_prefix6_length (p : U8) (hp : p.val ≤ 128) :
    (Nat.repr p.val).length ≤ 3 := by
  apply (Nat.length_repr_le_iff (by decide : 0 < 3)).2
  omega

theorem decimal_octet_length (b : U8) :
    (Nat.repr b.val).length ≤ 3 := by
  apply (Nat.length_repr_le_iff (by decide : 0 < 3)).2
  have hb := U8.le_max b
  omega

theorem hex_segment_length (n : Nat) (hn : n < 2 ^ 16) :
    (Nat.toDigits 16 n).length ≤ 4 := by
  apply (Nat.length_toDigits_le_iff (by decide : 1 < 16)
    (by decide : 0 < 4)).2
  norm_num at hn ⊢
  exact hn

/-- Each of four decimal octets needs at most three bytes; the dotted form
adds exactly three ASCII separators. -/
theorem dotted_quad_bound (octets : List U8) (hlen : octets.length = 4) :
    (octets.map (fun b => (Nat.repr b.val).length)).sum + 3 ≤ 15 := by
  have hsum : ∀ xs : List U8,
      (xs.map (fun b => (Nat.repr b.val).length)).sum ≤ 3 * xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hx := decimal_octet_length x
      omega
  have := hsum octets
  omega

/-- Eight hexadecimal groups plus seven separators give the uncompressed
IPv6 upper bound. Compression only removes groups and cannot exceed this
bound when its inserted separators total at most seven. -/
theorem ipv6_group_bound (groups separators : Nat)
    (hgroups : groups ≤ 8) (hseparators : separators ≤ 7) :
    4 * groups + separators ≤ 39 := by omega

/-- The standard IPv4-mapped spelling has `::ffff:` followed by one dotted
quad; this is well below the 39-byte IPv6 ceiling. -/
theorem mapped_ipv4_bound (v4bytes : Nat) (hv4 : v4bytes ≤ 15) :
    7 + v4bytes ≤ 39 := by omega

theorem compressed_ipv6_bound (groups separators : Nat)
    (hgroups : groups ≤ 6) (hseparators : separators ≤ 7) :
    4 * groups + separators ≤ 39 := by omega

/-- External text laws are explicit premises, not application-body facts.
The byte-length equalities distinguish ASCII decimal bytes from Unicode
character counts. -/
structure ExternalTextLaws where
  ipv4Address : ipnet.core.net.ip_addr.Ipv4Addr → String
  ipv6Address : ipnet.core.net.ip_addr.Ipv6Addr → String
  prefixText : U8 → String
  ipv4AddressBytes : ∀ a, (ipv4Address a).utf8ByteSize ≤ 15
  ipv6AddressBytes : ∀ a, (ipv6Address a).utf8ByteSize ≤ 39
  prefixExact : ∀ p, prefixText p = Nat.repr p.val
  prefixAsciiBytes : ∀ p, (prefixText p).utf8ByteSize = (Nat.repr p.val).length

/-- A separate correspondence with the pinned core/std default Display
functions. The correspondence is an external hypothesis; the names alone do
not establish it. -/
structure StandardDisplayBridge (laws : ExternalTextLaws) where
  standardIpv4 : ipnet.core.net.ip_addr.Ipv4Addr → String
  standardIpv6 : ipnet.core.net.ip_addr.Ipv6Addr → String
  ipv4Exact : ∀ a, laws.ipv4Address a = standardIpv4 a
  ipv6Exact : ∀ a, laws.ipv6Address a = standardIpv6 a

def text4 (laws : ExternalTextLaws) (n : ipnet.ipnet.Ipv4Net) : String :=
  laws.ipv4Address n.addr ++ "/" ++ laws.prefixText n.prefix_len

def text6 (laws : ExternalTextLaws) (n : ipnet.ipnet.Ipv6Net) : String :=
  laws.ipv6Address n.addr ++ "/" ++ laws.prefixText n.prefix_len

theorem text4_exact (laws : ExternalTextLaws) (n : ipnet.ipnet.Ipv4Net) :
    text4 laws n = laws.ipv4Address n.addr ++ "/" ++
      Nat.repr n.prefix_len.val := by
  simp [text4, laws.prefixExact]

theorem text6_exact (laws : ExternalTextLaws) (n : ipnet.ipnet.Ipv6Net) :
    text6 laws n = laws.ipv6Address n.addr ++ "/" ++
      Nat.repr n.prefix_len.val := by
  simp [text6, laws.prefixExact]

theorem text4_matches_standard (laws : ExternalTextLaws)
    (bridge : StandardDisplayBridge laws) (n : ipnet.ipnet.Ipv4Net) :
    text4 laws n = bridge.standardIpv4 n.addr ++ "/" ++
      Nat.repr n.prefix_len.val := by
  simp [text4, laws.prefixExact, bridge.ipv4Exact]

theorem text6_matches_standard (laws : ExternalTextLaws)
    (bridge : StandardDisplayBridge laws) (n : ipnet.ipnet.Ipv6Net) :
    text6 laws n = bridge.standardIpv6 n.addr ++ "/" ++
      Nat.repr n.prefix_len.val := by
  simp [text6, laws.prefixExact, bridge.ipv6Exact]

theorem text4_capacity (laws : ExternalTextLaws) (n : ipnet.ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    (text4 laws n).utf8ByteSize ≤ 18 := by
  have ha := laws.ipv4AddressBytes n.addr
  have hpref := laws.prefixAsciiBytes n.prefix_len
  have hd := decimal_prefix4_length n.prefix_len hp
  have hslash : "/".utf8ByteSize = 1 := by decide
  simp only [text4, String.utf8ByteSize_append] at *
  omega

theorem text6_capacity (laws : ExternalTextLaws) (n : ipnet.ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    (text6 laws n).utf8ByteSize ≤ 43 := by
  have ha := laws.ipv6AddressBytes n.addr
  have hpref := laws.prefixAsciiBytes n.prefix_len
  have hd := decimal_prefix6_length n.prefix_len hp
  have hslash : "/".utf8ByteSize = 1 := by decide
  simp only [text6, String.utf8ByteSize_append] at *
  omega

/-- A pure byte-capacity transition. Matching this model to heapless's
`fmt::Write` implementation remains a separate external obligation. -/
def appendWithin (capacity : Nat) (before piece : String) : Option String :=
  if before.utf8ByteSize + piece.utf8ByteSize ≤ capacity then
    some (before ++ piece)
  else none

theorem appendWithin_exact (capacity : Nat) (before piece : String)
    (hfit : before.utf8ByteSize + piece.utf8ByteSize ≤ capacity) :
    appendWithin capacity before piece = some (before ++ piece) := by
  simp [appendWithin, hfit]

theorem appendWithin_length (capacity : Nat) (before piece : String)
    (hfit : before.utf8ByteSize + piece.utf8ByteSize ≤ capacity) :
    (before ++ piece).utf8ByteSize ≤ capacity := by
  simpa [String.utf8ByteSize_append] using hfit

/-- The abstract write callback records allocations charged to the candidate's
temporary formatting path. An actual heapless/fmt bridge must establish
`hwrite`; it is deliberately a theorem premise rather than an axiom. -/
def renderThree
    (write : String → String → Option (String × Nat))
    (address decimal : String) : Option (String × Nat) := do
  let (b₁, n₁) ← write "" address
  let (b₂, n₂) ← write b₁ "/"
  let (b₃, n₃) ← write b₂ decimal
  some (b₃, n₁ + n₂ + n₃)

theorem renderThree_exact
    (capacity : Nat) (write : String → String → Option (String × Nat))
    (address decimal : String)
    (hcapacity : address.utf8ByteSize + 1 + decimal.utf8ByteSize ≤ capacity)
    (hwrite : ∀ before piece,
      before.utf8ByteSize + piece.utf8ByteSize ≤ capacity →
      write before piece = some (before ++ piece, 0)) :
    renderThree write address decimal =
      some (address ++ "/" ++ decimal, 0) := by
  have hslash : "/".utf8ByteSize = 1 := by decide
  have h₁ : write "" address = some (address, 0) := by
    simpa using hwrite "" address (by simpa using
      (show address.utf8ByteSize ≤ capacity by omega))
  have h₂ : write address "/" = some (address ++ "/", 0) := by
    apply hwrite
    simpa [hslash] using
      (show address.utf8ByteSize + 1 ≤ capacity by omega)
  have h₃ : write (address ++ "/") decimal =
      some (address ++ "/" ++ decimal, 0) := by
    apply hwrite
    simpa [String.utf8ByteSize_append, hslash] using hcapacity
  simp [renderThree, h₁, h₂, h₃]

/-- Arbitrarily fragmented formatter output is supported by the same
per-append contract. This is the form required to bridge real `fmt::Write`
callback sequences, whose chunks need not be the three logical components. -/
def concatChunks : List String → String
  | [] => ""
  | x :: xs => x ++ concatChunks xs

def chunksBytes (xs : List String) : Nat :=
  (xs.map String.utf8ByteSize).sum

def writeChunks (write : String → String → Option (String × Nat))
    (before : String) : List String → Option (String × Nat)
  | [] => some (before, 0)
  | piece :: rest => do
      let (after, n) ← write before piece
      let (final, m) ← writeChunks write after rest
      some (final, n + m)

theorem concatChunks_bytes (xs : List String) :
    (concatChunks xs).utf8ByteSize = chunksBytes xs := by
  induction xs with
  | nil => simp [concatChunks, chunksBytes]
  | cons x xs ih =>
      simp [concatChunks, chunksBytes, String.utf8ByteSize_append, ih]

theorem writeChunks_exact (capacity : Nat)
    (write : String → String → Option (String × Nat))
    (before : String) (chunks : List String)
    (hfit : before.utf8ByteSize + chunksBytes chunks ≤ capacity)
    (hwrite : ∀ current piece,
      current.utf8ByteSize + piece.utf8ByteSize ≤ capacity →
      write current piece = some (current ++ piece, 0)) :
    writeChunks write before chunks =
      some (before ++ concatChunks chunks, 0) := by
  induction chunks generalizing before with
  | nil => simp [writeChunks, concatChunks]
  | cons piece rest ih =>
      have hhead : before.utf8ByteSize + piece.utf8ByteSize ≤ capacity := by
        simp only [chunksBytes, List.map_cons, List.sum_cons] at hfit
        omega
      have hrest : (before ++ piece).utf8ByteSize +
          chunksBytes rest ≤ capacity := by
        change before.utf8ByteSize +
          (piece.utf8ByteSize + chunksBytes rest) ≤ capacity at hfit
        simp only [String.utf8ByteSize_append]
        omega
      simp [writeChunks, hwrite before piece hhead,
        ih (before ++ piece) hrest, concatChunks, String.append_assoc]

/-- A terminating, pure success/error observation of an external serializer
is passed through exactly. External panic, divergence, state effects, and
allocations are outside this `Except` model and require separate laws. -/
def renderThenSerialize {ε α : Type}
    (write : String → String → Option (String × Nat))
    (serializeStr : String → Except ε α)
    (address decimal : String) : Option (Except ε α × Nat) := do
  let (rendered, internalAllocations) ← renderThree write address decimal
  some (serializeStr rendered, internalAllocations)

theorem renderThenSerialize_exact {ε α : Type}
    (capacity : Nat) (write : String → String → Option (String × Nat))
    (serializeStr : String → Except ε α) (address decimal : String)
    (hcapacity : address.utf8ByteSize + 1 + decimal.utf8ByteSize ≤ capacity)
    (hwrite : ∀ before piece,
      before.utf8ByteSize + piece.utf8ByteSize ≤ capacity →
      write before piece = some (before ++ piece, 0)) :
    renderThenSerialize write serializeStr address decimal =
      some (serializeStr (address ++ "/" ++ decimal), 0) := by
  simp [renderThenSerialize,
    renderThree_exact capacity write address decimal hcapacity hwrite]

theorem render_ipv4_exact (laws : ExternalTextLaws)
    (n : ipnet.ipnet.Ipv4Net) (hp : n.prefix_len.val ≤ 32)
    (write : String → String → Option (String × Nat))
    (hwrite : ∀ before piece,
      before.utf8ByteSize + piece.utf8ByteSize ≤ 18 →
      write before piece = some (before ++ piece, 0)) :
    renderThree write (laws.ipv4Address n.addr)
      (laws.prefixText n.prefix_len) = some (text4 laws n, 0) := by
  have hcapacity := text4_capacity laws n hp
  have hslash : "/".utf8ByteSize = 1 := by decide
  have hsum : (laws.ipv4Address n.addr).utf8ByteSize + 1 +
      (laws.prefixText n.prefix_len).utf8ByteSize ≤ 18 := by
    simpa [text4, String.utf8ByteSize_append, hslash] using hcapacity
  simpa [text4] using renderThree_exact 18 write
    (laws.ipv4Address n.addr) (laws.prefixText n.prefix_len) hsum hwrite

theorem render_ipv6_exact (laws : ExternalTextLaws)
    (n : ipnet.ipnet.Ipv6Net) (hp : n.prefix_len.val ≤ 128)
    (write : String → String → Option (String × Nat))
    (hwrite : ∀ before piece,
      before.utf8ByteSize + piece.utf8ByteSize ≤ 43 →
      write before piece = some (before ++ piece, 0)) :
    renderThree write (laws.ipv6Address n.addr)
      (laws.prefixText n.prefix_len) = some (text6 laws n, 0) := by
  have hcapacity := text6_capacity laws n hp
  have hslash : "/".utf8ByteSize = 1 := by decide
  have hsum : (laws.ipv6Address n.addr).utf8ByteSize + 1 +
      (laws.prefixText n.prefix_len).utf8ByteSize ≤ 43 := by
    simpa [text6, String.utf8ByteSize_append, hslash] using hcapacity
  simpa [text6] using renderThree_exact 43 write
    (laws.ipv6Address n.addr) (laws.prefixText n.prefix_len) hsum hwrite

end HeaplessCandidateMath
