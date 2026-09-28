import SszX86.SerializeCore
import SszX86.BitVectorLoad

namespace SszX86.Serialize.Publish
open SszNative UintCodec BoolCodec

/-- The complete 72-byte temporary, including the unconstrained trailing word. -/
structure Image where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64
  tag : BitVec 32
  padding : BitVec 32

structure ImageAt (m : DataMem) (p : BitVec 64) (v : Image) : Prop where
  w0 : Mem.loadInt m (p + 0#64) 8 = some (v.w0.toNat : Int)
  w1 : Mem.loadInt m (p + 8#64) 8 = some (v.w1.toNat : Int)
  w2 : Mem.loadInt m (p + 16#64) 8 = some (v.w2.toNat : Int)
  w3 : Mem.loadInt m (p + 24#64) 8 = some (v.w3.toNat : Int)
  w4 : Mem.loadInt m (p + 32#64) 8 = some (v.w4.toNat : Int)
  w5 : Mem.loadInt m (p + 40#64) 8 = some (v.w5.toNat : Int)
  w6 : Mem.loadInt m (p + 48#64) 8 = some (v.w6.toNat : Int)
  w7 : Mem.loadInt m (p + 56#64) 8 = some (v.w7.toNat : Int)
  tag : Mem.loadInt m (p + 64#64) 4 = some (v.tag.toNat : Int)
  padding : Mem.loadInt m (p + 68#64) 4 = some (v.padding.toNat : Int)

/-- No semantic value, including padding, is invented from a mapping. -/
theorem mapped_image (m : DataMem) (p : BitVec 64) (hm : Large.Mapped m p 72) :
    ∃ v, ImageAt m p v := by
  have load64 (n : Nat) (hn : n + 8 ≤ 72) :
      ∃ v : BitVec 64, Mem.loadInt m (p + BitVec.ofNat 64 n) 8 = some (v.toNat : Int) :=
    BitVector.mapped_word m _ 8 (Large.mapped_load m p 72 n 8 hm hn)
  have load32 (n : Nat) (hn : n + 4 ≤ 72) :
      ∃ v : BitVec 32, Mem.loadInt m (p + BitVec.ofNat 64 n) 4 = some (v.toNat : Int) :=
    BitVector.mapped_word m _ 4 (Large.mapped_load m p 72 n 4 hm hn)
  obtain ⟨w0, h0⟩ := load64 0 (by decide)
  obtain ⟨w1, h1⟩ := load64 8 (by decide)
  obtain ⟨w2, h2⟩ := load64 16 (by decide)
  obtain ⟨w3, h3⟩ := load64 24 (by decide)
  obtain ⟨w4, h4⟩ := load64 32 (by decide)
  obtain ⟨w5, h5⟩ := load64 40 (by decide)
  obtain ⟨w6, h6⟩ := load64 48 (by decide)
  obtain ⟨w7, h7⟩ := load64 56 (by decide)
  obtain ⟨tag, ht⟩ := load32 64 (by decide)
  obtain ⟨padding, hp⟩ := load32 68 (by decide)
  exact ⟨⟨w0, w1, w2, w3, w4, w5, w6, w7, tag, padding⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, ht, hp⟩

def spillMem (m : DataMem) (sp : BitVec 64) (v : Image) : DataMem :=
  let m := Mem.storeInt m (sp + 8#64) 8 v.w0.toInt
  Mem.storeInt m (sp + 16#64) 8 v.w1.toInt

def preparedMem (m : DataMem) (sp : BitVec 64) (v : Image) : DataMem :=
  let m := Mem.storeInt m (sp + 24#64) 8 v.w0.toInt
  let m := Mem.storeInt m (sp + 32#64) 8 v.w1.toInt
  let m := Mem.storeInt m (sp + 40#64) 8 v.w2.toInt
  let m := Mem.storeInt m (sp + 48#64) 8 v.w3.toInt
  Mem.storeInt m (sp + 56#64) 8 v.w4.toInt

/-- Actual PC95..153 store order, with the full arbitrary +68 padding word. -/
def copyMem (m : DataMem) (out : BitVec 64) (v : Image) : DataMem :=
  let m := Mem.storeInt m (out + 56#64) 8 v.w7.toInt
  let m := Mem.storeInt m (out + 48#64) 8 v.w6.toInt
  let m := Mem.storeInt m (out + 40#64) 8 v.w5.toInt
  let m := Mem.storeInt m (out + 8#64) 8 v.w1.toInt
  let m := Mem.storeInt m (out + 0#64) 8 v.w0.toInt
  let m := Mem.storeInt m (out + 16#64) 8 v.w2.toInt
  let m := Mem.storeInt m (out + 24#64) 8 v.w3.toInt
  let m := Mem.storeInt m (out + 32#64) 8 v.w4.toInt
  let m := Mem.storeInt m (out + 64#64) 4 v.tag.toInt
  Mem.storeInt m (out + 68#64) 4 v.padding.toInt

/-- PC313 writes low-to-high, unlike the host-size failure at PC235. -/
def capacityMem (m : DataMem) (out : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + 0#64) 8 1
  let m := Mem.storeInt m (out + 8#64) 8 0
  let m := Mem.storeInt m (out + 16#64) 8 0
  let m := Mem.storeInt m (out + 24#64) 8 0
  let m := Mem.storeInt m (out + 32#64) 8 0
  let m := Mem.storeInt m (out + 40#64) 8 0
  let m := Mem.storeInt m (out + 48#64) 8 0
  let m := Mem.storeInt m (out + 56#64) 8 0
  Mem.storeInt m (out + 64#64) 4 32769

def hostMem (m : DataMem) (out : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + 56#64) 8 0
  let m := Mem.storeInt m (out + 48#64) 8 0
  let m := Mem.storeInt m (out + 40#64) 8 0
  let m := Mem.storeInt m (out + 32#64) 8 0
  let m := Mem.storeInt m (out + 24#64) 8 0
  let m := Mem.storeInt m (out + 16#64) 8 0
  let m := Mem.storeInt m (out + 8#64) 8 0
  let m := Mem.storeInt m (out + 0#64) 8 1
  Mem.storeInt m (out + 64#64) 4 32769

theorem load_store_word {n : Nat} (m : DataMem) (p : BitVec 64)
    (v : BitVec (8 * n)) (hn : n ≤ 2^64) :
    Mem.loadInt (Mem.storeInt m p n v.toInt) p n = some (v.toNat : Int) := by
  rw [BoolCodec.load_store_same _ _ _ _ hn]
  congr 1
  have h := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := v))
  simp only [BitVec.toNat_ofInt, Int.natCast_pow, show ((2 : Nat) : Int) = 2 by rfl] at h
  simp only [Int.take]
  have positive : 0 < (2 : Int) ^ (8*n) := Int.pow_pos (by decide)
  have nonnegative := Int.emod_nonneg v.toInt (by omega : (2 : Int) ^ (8*n) ≠ 0)
  omega

/-- Disjoint offsets within an arbitrary bounded activation (not an 80-byte Plan). -/
theorem local_read (m : DataMem) (sp : BitVec 64) (extent a n b k : Nat) (value : Int)
    (bound : sp.toNat + extent ≤ 2^64) (ha : a+n ≤ extent) (hb : b+k ≤ extent)
    (apart : a+n ≤ b ∨ b+k ≤ a) :
    Mem.loadInt (Mem.storeInt m (sp + BitVec.ofNat 64 b) k value)
      (sp + BitVec.ofNat 64 a) n = Mem.loadInt m (sp + BitVec.ofNat 64 a) n := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj
  bv_omega

theorem remote_read (m : DataMem) (src dst : BitVec 64)
    (srcCount dstCount a n b k : Nat) (value : Int)
    (apart : Large.Disjoint src dst srcCount dstCount)
    (ha : a+n ≤ srcCount) (hb : b+k ≤ dstCount) :
    Mem.loadInt (Mem.storeInt m (dst + BitVec.ofNat 64 b) k value)
      (src + BitVec.ofNat 64 a) n = Mem.loadInt m (src + BitVec.ofNat 64 a) n := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj
  simp only [memmove_addr_add]
  exact apart (a+i) (by omega) (b+j) (by omega)

theorem spill_reads (m : DataMem) (sp : BitVec 64) (v : Image)
    (bound : sp.toNat + 96 ≤ 2^64) :
    Mem.loadInt (spillMem m sp v) (sp + 8#64) 8 = some (v.w0.toNat : Int) ∧
    Mem.loadInt (spillMem m sp v) (sp + 16#64) 8 = some (v.w1.toNat : Int) := by
  constructor <;> simp (disch := first | assumption | omega | decide) only
    [spillMem, local_read (extent := 96), load_store_word]

theorem spill_plan (m : DataMem) (sp : BitVec 64) (v : Image)
    (bound : sp.toNat + 96 ≤ 2^64) (image : ImageAt m (sp + 24#64) v) :
    ImageAt (spillMem m sp v) (sp + 24#64) v := by
  rcases image with ⟨h0,h1,h2,h3,h4,h5,h6,h7,ht,hp⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h0 h1 h2 h3 h4 h5 h6 h7 ht hp
  constructor <;>
    simp (disch := first | assumption | omega | decide) only
      [spillMem, BitVec.add_assoc, BitVec.reduceAdd, local_read (extent := 96)]
  all_goals assumption

/-- Every copied field, including the otherwise semantically invisible padding. -/
theorem copy_image (m : DataMem) (out : BitVec 64) (v : Image)
    (bound : out.toNat + 80 ≤ 2^64) : ImageAt (copyMem m out v) out v := by
  constructor <;> simp (disch := first | assumption | omega | decide) only
    [copyMem, BoolCodec.load_store_offset_disjoint, load_store_word]


theorem spill_frame (m : DataMem) (sp : BitVec 64) (v : Image) :
    MemoryFrame m (spillMem m sp v) (fun a => InSpan a (sp + 8#64) 16) := by
  unfold spillMem
  have address : sp + 16#64 = sp + 8#64 + BitVec.ofNat 64 8 := by simp [BitVec.add_assoc]
  rw [address]
  intro a outside
  have avoid : ∀ i < 16, a ≠ sp + 8#64 + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside ⟨i, hi, equal⟩
  have first := BoolCodec.store_frame m (sp + 8#64) a 16 0 8 v.w0.toInt (by decide) avoid
  simp only [BitVec.add_zero] at first
  rw [BoolCodec.store_frame _ _ _ 16 8 8 _ (by decide) avoid, first]

theorem prepared_frame (m : DataMem) (sp : BitVec 64) (v : Image) :
    MemoryFrame m (preparedMem m sp v) (fun a => InSpan a (sp + 24#64) 40) := by
  intro a outside
  have avoid : ∀ i < 64, 24 ≤ i → a ≠ sp + BitVec.ofNat 64 i := by
    intro i hi low equal
    apply outside
    refine ⟨i-24, by omega, ?_⟩
    rw [memmove_addr_add]
    simpa only [Nat.add_sub_of_le low] using equal
  unfold preparedMem
  repeat' rw [Mem.storeInt, memmove_store_lookup_outside]
  all_goals
    intro i hi
    simp only [Int.toBytes_length] at hi
    rw [memmove_addr_add]
    apply avoid <;> omega

theorem copy_frame (m : DataMem) (out : BitVec 64) (v : Image) :
    MemoryFrame m (copyMem m out v) (fun a => InSpan a out 72) := by
  intro a outside
  have avoid : ∀ i < 72, a ≠ out + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside ⟨i, hi, equal⟩
  simp (disch := first | assumption | omega | decide) only
    [copyMem, BoolCodec.store_frame (limit := 72)]

theorem capacity_frame (m : DataMem) (out : BitVec 64) :
    MemoryFrame m (capacityMem m out) (fun a => InSpan a out 68) := by
  intro a outside
  have avoid : ∀ i < 68, a ≠ out + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside ⟨i, hi, equal⟩
  simp (disch := first | assumption | omega | decide) only
    [capacityMem, BoolCodec.store_frame (limit := 68)]

theorem host_frame (m : DataMem) (out : BitVec 64) :
    MemoryFrame m (hostMem m out) (fun a => InSpan a out 68) := by
  intro a outside
  have avoid : ∀ i < 68, a ≠ out + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside ⟨i, hi, equal⟩
  simp (disch := first | assumption | omega | decide) only
    [hostMem, BoolCodec.store_frame (limit := 68)]

macro "publish_mapping" : tactic => `(tactic|
  (intro p n hm
   repeat' first | exact hm | apply Large.mapped_store))

theorem spill_mapping (m : DataMem) (sp : BitVec 64) (v : Image) :
    BitVector.Mapping.Extends m (spillMem m sp v) := by
  unfold spillMem
  publish_mapping

theorem prepared_mapping (m : DataMem) (sp : BitVec 64) (v : Image) :
    BitVector.Mapping.Extends m (preparedMem m sp v) := by
  unfold preparedMem
  publish_mapping

theorem copy_mapping (m : DataMem) (out : BitVec 64) (v : Image) :
    BitVector.Mapping.Extends m (copyMem m out v) := by
  unfold copyMem
  publish_mapping

theorem capacity_mapping (m : DataMem) (out : BitVec 64) :
    BitVector.Mapping.Extends m (capacityMem m out) := by
  unfold capacityMem
  publish_mapping

theorem host_mapping (m : DataMem) (out : BitVec 64) :
    BitVector.Mapping.Extends m (hostMem m out) := by
  unfold hostMem
  publish_mapping

/-- Both independent error paths have this exact common 68-byte payload. -/
structure TooSmallAt (m : DataMem) (out : BitVec 64) : Prop where
  first : Mem.loadInt m (out + 0#64) 8 = some 1
  zero1 : Mem.loadInt m (out + 8#64) 8 = some 0
  zero2 : Mem.loadInt m (out + 16#64) 8 = some 0
  zero3 : Mem.loadInt m (out + 24#64) 8 = some 0
  zero4 : Mem.loadInt m (out + 32#64) 8 = some 0
  zero5 : Mem.loadInt m (out + 40#64) 8 = some 0
  zero6 : Mem.loadInt m (out + 48#64) 8 = some 0
  zero7 : Mem.loadInt m (out + 56#64) 8 = some 0
  tag : Mem.loadInt m (out + 64#64) 4 = some 32769

theorem capacity_fields (m : DataMem) (out : BitVec 64)
    (bound : out.toNat + 80 ≤ 2^64) : TooSmallAt (capacityMem m out) out := by
  constructor <;> simp (disch := first | assumption | omega | decide) only
    [capacityMem, BoolCodec.load_store_offset_disjoint, BoolCodec.load_store_same,
     Nat.reduceMul]
  all_goals decide

theorem host_fields (m : DataMem) (out : BitVec 64)
    (bound : out.toNat + 80 ≤ 2^64) : TooSmallAt (hostMem m out) out := by
  constructor <;> simp (disch := first | assumption | omega | decide) only
    [hostMem, BoolCodec.load_store_offset_disjoint, BoolCodec.load_store_same,
     Nat.reduceMul]
  all_goals decide

theorem TooSmallAt.observed {m : DataMem} {out : BitVec 64} (h : TooSmallAt m out) :
    Measure.ErrorAt (widthLoad m) out.toNat .outputTooSmall := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,ht⟩
  have observe (n k : Nat) (v : Int)
      (loaded : Mem.loadInt m (out + BitVec.ofNat 64 n) k = some v) :
      widthLoad m (out.toNat+n) k = some v.toNat := by
    simp only [widthLoad, width_address, loaded, Option.map_some]
  change Measure.SemanticErrorAt _ _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using observe 0 8 1 h0
  · exact observe 8 8 0 h1
  · refine ⟨?_, ?_, trivial⟩
    · simpa [SszNative.NatOperand.pointer] using observe 16 8 0 h2
    · simpa [SszNative.NatOperand.payload, Nat.add_assoc] using observe 24 8 0 h3
  · refine ⟨?_, ?_, trivial⟩
    · simpa [SszNative.NatOperand.pointer] using observe 32 8 0 h4
    · simpa [SszNative.NatOperand.payload, Nat.add_assoc] using observe 40 8 0 h5
  · exact observe 48 8 0 h6
  · exact observe 56 8 0 h7
  · exact observe 64 4 32769 ht

theorem error_padding (m : DataMem) (out : BitVec 64)
    (bound : out.toNat + 80 ≤ 2^64) (i : Nat) (low : 68 ≤ i) (high : i < 80) :
    (hostMem m out).get? (out + BitVec.ofNat 64 i) = m.get? (out + BitVec.ofNat 64 i) ∧
    (capacityMem m out).get? (out + BitVec.ofNat 64 i) = m.get? (out + BitVec.ofNat 64 i) := by
  have outside : ¬ InSpan (out + BitVec.ofNat 64 i) out 68 := by
    rintro ⟨j, hj, equal⟩
    have same := memmove_addr_injective out 80 i j bound high (by omega) equal
    omega
  exact ⟨host_frame m out _ outside, capacity_frame m out _ outside⟩

private theorem allSome_values {α : Type} (items : List (Option α)) (values : List α)
    (loaded : items.allSome = some values) : items = values.map some := by
  induction items generalizing values with
  | nil =>
    change (some [] : Option (List α)) = some values at loaded
    cases loaded
    rfl
  | cons first rest ih =>
    cases first with
    | none => simp [List.allSome] at loaded
    | some value =>
      cases remainder : rest.allSome with
      | none =>
        change rest.mapM id = none at remainder
        simp [List.allSome, remainder] at loaded
      | some remaining =>
        change rest.mapM id = some remaining at remainder
        simp only [List.allSome, List.mapM_cons, id_eq, remainder] at loaded
        change some (value :: remaining) = some values at loaded
        cases loaded
        simp only [List.map_cons, ih remaining remainder]

/-- Equal unsigned loads of a fixed width have equal individual bytes, even at
different addresses. This is inversion of the actual byte loader. -/
theorem equal_load_bytes (before after : DataMem) (src dst : BitVec 64)
    (n : Nat) (value : Int)
    (source : Mem.loadInt before src n = some value)
    (destination : Mem.loadInt after dst n = some value) (i : Nat) (hi : i < n) :
    after.get? (dst + BitVec.ofNat 64 i) = before.get? (src + BitVec.ofNat 64 i) := by
  cases leftRead : Mem.loadBytes before src n with
  | none => simp only [Mem.loadInt, leftRead, Option.map_none] at source; cases source
  | some leftBytes =>
    cases rightRead : Mem.loadBytes after dst n with
    | none => simp only [Mem.loadInt, rightRead, Option.map_none] at destination; cases destination
    | some rightBytes =>
      have leftMap := allSome_values
        ((List.range n).map (fun j => before.get? (src + BitVec.ofNat 64 j))) leftBytes leftRead
      have rightMap := allSome_values
        ((List.range n).map (fun j => after.get? (dst + BitVec.ofNat 64 j))) rightBytes rightRead
      have leftLength : leftBytes.length = n := by
        have h := congrArg List.length leftMap
        simpa only [List.length_map, List.length_range] using h.symm
      have rightLength : rightBytes.length = n := by
        have h := congrArg List.length rightMap
        simpa only [List.length_map, List.length_range] using h.symm
      have leftValue : Int.ofBytes leftBytes = value := by
        simpa only [Mem.loadInt, leftRead, Option.map_some, Option.some.injEq] using source
      have rightValue : Int.ofBytes rightBytes = value := by
        simpa only [Mem.loadInt, rightRead, Option.map_some, Option.some.injEq] using destination
      have sameBytes : leftBytes = rightBytes := by
        have leftEncode : Int.toBytes n (Int.ofBytes leftBytes) = leftBytes := by
          simpa only [leftLength] using Int.toBytes_ofBytes_all leftBytes
        have rightEncode : Int.toBytes n (Int.ofBytes rightBytes) = rightBytes := by
          simpa only [rightLength] using Int.toBytes_ofBytes_all rightBytes
        have equality := congrArg (Int.toBytes n) (leftValue.trans rightValue.symm)
        simpa only [leftEncode, rightEncode] using equality
      rw [sameBytes] at leftMap
      have index := congrArg (fun xs => xs[i]?) (rightMap.trans leftMap.symm)
      simpa only [List.getElem?_map, List.getElem?_range, hi, ↓reduceIte,
        Option.map_some, Option.some.injEq] using index

theorem ImageAt.byte_eq {before after : DataMem} {src dst : BitVec 64} {v : Image}
    (source : ImageAt before src v) (destination : ImageAt after dst v)
    (i : Nat) (hi : i < 72) :
    after.get? (dst + BitVec.ofNat 64 i) = before.get? (src + BitVec.ofNat 64 i) := by
  have block (a n : Nat) (value : Int)
      (hs : Mem.loadInt before (src + BitVec.ofNat 64 a) n = some value)
      (hd : Mem.loadInt after (dst + BitVec.ofNat 64 a) n = some value)
      (low : a ≤ i) (high : i < a+n) :
      after.get? (dst + BitVec.ofNat 64 i) = before.get? (src + BitVec.ofNat 64 i) := by
    have same := equal_load_bytes before after _ _ n value hs hd (i-a) (by omega)
    simpa only [memmove_addr_add, Nat.add_sub_of_le low] using same
  by_cases b0 : i < 8
  · exact block 0 8 _ source.w0 destination.w0 (by omega) b0
  by_cases b1 : i < 16
  · exact block 8 8 _ source.w1 destination.w1 (by omega) b1
  by_cases b2 : i < 24
  · exact block 16 8 _ source.w2 destination.w2 (by omega) b2
  by_cases b3 : i < 32
  · exact block 24 8 _ source.w3 destination.w3 (by omega) b3
  by_cases b4 : i < 40
  · exact block 32 8 _ source.w4 destination.w4 (by omega) b4
  by_cases b5 : i < 48
  · exact block 40 8 _ source.w5 destination.w5 (by omega) b5
  by_cases b6 : i < 56
  · exact block 48 8 _ source.w6 destination.w6 (by omega) b6
  by_cases b7 : i < 64
  · exact block 56 8 _ source.w7 destination.w7 (by omega) b7
  by_cases tagBytes : i < 68
  · exact block 64 4 _ source.tag destination.tag (by omega) tagBytes
  exact block 68 4 _ source.padding destination.padding (by omega) hi

theorem copy_bytes (before work : DataMem) (src dst : BitVec 64) (v : Image)
    (source : ImageAt before src v) (bound : dst.toNat + 80 ≤ 2^64) :
    ∀ i < 72, (copyMem work dst v).get? (dst + BitVec.ofNat 64 i) =
      before.get? (src + BitVec.ofNat 64 i) :=
  source.byte_eq (copy_image work dst v bound)

/-- The two differently ordered store sequences agree byte-for-byte, not just
on the semantic status field. Outside the payload they both retain the input. -/
theorem host_capacity_memory (m : DataMem) (out : BitVec 64)
    (bound : out.toNat + 80 ≤ 2^64) : hostMem m out = capacityMem m out := by
  have source := capacity_fields m out bound
  have destination := host_fields m out bound
  apply Std.ExtHashMap.ext_getElem?
  intro a
  change (hostMem m out).get? a = (capacityMem m out).get? a
  by_cases inside : InSpan a out 68
  · obtain ⟨i, hi, rfl⟩ := inside
    have block (b n : Nat) (value : Int)
        (hs : Mem.loadInt (capacityMem m out) (out + BitVec.ofNat 64 b) n = some value)
        (hd : Mem.loadInt (hostMem m out) (out + BitVec.ofNat 64 b) n = some value)
        (low : b ≤ i) (high : i < b+n) :
        (hostMem m out).get? (out + BitVec.ofNat 64 i) =
          (capacityMem m out).get? (out + BitVec.ofNat 64 i) := by
      have same := equal_load_bytes _ _ _ _ n value hs hd (i-b) (by omega)
      simpa only [memmove_addr_add, Nat.add_sub_of_le low] using same
    by_cases b0 : i < 8
    · exact block 0 8 1 source.first destination.first (by omega) b0
    by_cases b1 : i < 16
    · exact block 8 8 0 source.zero1 destination.zero1 (by omega) b1
    by_cases b2 : i < 24
    · exact block 16 8 0 source.zero2 destination.zero2 (by omega) b2
    by_cases b3 : i < 32
    · exact block 24 8 0 source.zero3 destination.zero3 (by omega) b3
    by_cases b4 : i < 40
    · exact block 32 8 0 source.zero4 destination.zero4 (by omega) b4
    by_cases b5 : i < 48
    · exact block 40 8 0 source.zero5 destination.zero5 (by omega) b5
    by_cases b6 : i < 56
    · exact block 48 8 0 source.zero6 destination.zero6 (by omega) b6
    by_cases b7 : i < 64
    · exact block 56 8 0 source.zero7 destination.zero7 (by omega) b7
    exact block 64 4 32769 source.tag destination.tag (by omega) hi
  · exact (host_frame m out a inside).trans (capacity_frame m out a inside).symm

end SszX86.Serialize.Publish
