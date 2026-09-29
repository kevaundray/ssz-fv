import SszX86.CodecDeserializeCopy
import SszX86.SerializePublishMemory

set_option autoImplicit false

namespace SszX86.CodecDeserialize
open SszNative UintCodec

/-- Six physical observations of a Value copy. Word contents remain arbitrary;
this is not a claim that all words are meaningful fields of the decoded node. -/
structure ValueWords where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64

structure ValueWords.At (words : ValueWords) (m : DataMem) (p : BitVec 64) : Prop where
  w0 : Mem.loadInt m (p + 0) 8 = some (words.w0.toNat : Int)
  w1 : Mem.loadInt m (p + 8) 8 = some (words.w1.toNat : Int)
  w2 : Mem.loadInt m (p + 16) 8 = some (words.w2.toNat : Int)
  w3 : Mem.loadInt m (p + 24) 8 = some (words.w3.toNat : Int)
  w4 : Mem.loadInt m (p + 32) 8 = some (words.w4.toNat : Int)
  w5 : Mem.loadInt m (p + 40) 8 = some (words.w5.toNat : Int)

/-- The stores executed by fixed, offset, and structure child-fill loops. -/
def copyWords (m : DataMem) (p : BitVec 64) (words : ValueWords) : DataMem :=
  let m := Mem.storeInt m p 8 words.w0.toInt
  let m := Mem.storeInt m (p + 8) 8 words.w1.toInt
  let m := Mem.storeInt m (p + 16) 8 words.w2.toInt
  let m := Mem.storeInt m (p + 24) 8 words.w3.toInt
  let m := Mem.storeInt m (p + 32) 8 words.w4.toInt
  Mem.storeInt m (p + 40) 8 words.w5.toInt

private theorem offset_keep (m : DataMem) (p : BitVec 64) (a b : Nat) (value : Int)
    (ha : a + 8 ≤ 48) (hb : b + 8 ≤ 48) (apart : a + 8 ≤ b ∨ b + 8 ≤ a) :
    Mem.loadInt (Mem.storeInt m (p + BitVec.ofNat 64 b) 8 value)
      (p + BitVec.ofNat 64 a) 8 = Mem.loadInt m (p + BitVec.ofNat 64 a) 8 := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj
  bv_omega

/-- Each of the six opaque words is copied verbatim. -/
theorem copyWords_at (m : DataMem) (p : BitVec 64) (words : ValueWords) :
    words.At (copyWords m p words) p := by
  have keep0 (memory : DataMem) (b : Nat) (value : Int) (lo : 8 ≤ b) (hi : b + 8 ≤ 48) :
      Mem.loadInt (Mem.storeInt memory (p + BitVec.ofNat 64 b) 8 value) p 8 =
        Mem.loadInt memory p 8 := by
    simpa only [BitVec.ofNat_zero, BitVec.add_zero] using
      offset_keep memory p 0 b value (by decide) hi (Or.inl lo)
  constructor <;>
    simp (disch := first | omega | decide) only
      [copyWords, BitVec.add_zero, keep0, offset_keep, Serialize.Publish.load_store_word]

theorem copyWords_frame (m : DataMem) (p : BitVec 64) (words : ValueWords) :
    Codec.MemoryFrame m (copyWords m p words) (fun a => Codec.InSpan a p 48) := by
  intro a outside
  have separate : ∀ i < 48, a ≠ p + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside ⟨i, hi, equal⟩
  have zero : p = p + BitVec.ofNat 64 0 := by simp
  simp only [copyWords]
  rw [zero]
  simp (disch := first | assumption | omega | decide) only [BoolCodec.store_frame (limit := 48)]

theorem ValueWords.At.byte_eq {m n : DataMem} {p q : BitVec 64} {words : ValueWords}
    (source : words.At m p) (destination : words.At n q) (i : Nat) (hi : i < 48) :
    n.get? (q + BitVec.ofNat 64 i) = m.get? (p + BitVec.ofNat 64 i) := by
  have block (a : Nat) (value : Int)
      (hs : Mem.loadInt m (p + BitVec.ofNat 64 a) 8 = some value)
      (hd : Mem.loadInt n (q + BitVec.ofNat 64 a) 8 = some value)
      (low : a ≤ i) (high : i < a + 8) :
      n.get? (q + BitVec.ofNat 64 i) = m.get? (p + BitVec.ofNat 64 i) := by
    have same := Serialize.Publish.equal_load_bytes m n _ _ 8 value hs hd (i-a) (by omega)
    simpa only [memmove_addr_add, Nat.add_sub_of_le low] using same
  by_cases b0 : i < 8
  · exact block 0 _ source.w0 destination.w0 (by omega) b0
  by_cases b1 : i < 16
  · exact block 8 _ source.w1 destination.w1 (by omega) b1
  by_cases b2 : i < 24
  · exact block 16 _ source.w2 destination.w2 (by omega) b2
  by_cases b3 : i < 32
  · exact block 24 _ source.w3 destination.w3 (by omega) b3
  by_cases b4 : i < 40
  · exact block 32 _ source.w4 destination.w4 (by omega) b4
  exact block 40 _ source.w5 destination.w5 (by omega) hi

/-- Converting equal physical word snapshots to every active field observation
handles sub-word tags without treating the surrounding padding as semantic data. -/
theorem ValueWords.At.rootCopied {m n : DataMem} {p q : BitVec 64} {words : ValueWords}
    (source : words.At m p) (destination : words.At n q) : RootCopied m n p q := by
  constructor
  intro offset bytes bound
  apply congrArg (fun bs : Option (List UInt8) => bs.map Int.ofBytes)
  unfold Mem.loadBytes
  apply congrArg List.allSome
  apply List.map_congr_left
  intro i hi
  have within := List.mem_range.mp hi
  simpa only [memmove_addr_add] using source.byte_eq destination (offset + i) (by omega)

/-- Installation of an addressed decoded child by the native six-word copy. -/
theorem copyWords_node {m : DataMem} {r : Codec.Footprint} {source p q : BitVec 64}
    {node : CodecDecode.Node} (h : Codec.NodeAt m r source p node)
    (words : ValueWords) (snapshot : words.At m p) (span : Codec.Span r q 48 16)
    (safe : ∀ a, nodeBorrowed source node a → ¬ Codec.InSpan a q 48) :
    Codec.NodeAt (copyWords m q words) r source q node :=
  nodeAt_relocate h (snapshot.rootCopied (copyWords_at m q words)) span
    (copyWords_frame m q words) safe

end SszX86.CodecDeserialize
