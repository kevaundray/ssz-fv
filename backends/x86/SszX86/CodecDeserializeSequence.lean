import SszX86.CodecDeserializeMemory

set_option autoImplicit false

namespace SszX86.CodecDeserialize
open SszNative

/-- The empty native sequence has a recursive addressed Node observation. The
footprint protects the physical Value object while observing only active fields. -/
theorem empty_node (m : DataMem) (out source : BitVec 64)
    (bound : out.toNat + 80 ≤ 2 ^ 64) (aligned : out.toNat % 16 = 0) :
    Codec.NodeAt (sequenceMem m out 16 0)
      (fun a => Codec.InSpan a (out + 16) 48) source (out + 16) (.seq none []) := by
  have loaded := sequence_loads m out 16 0 bound
  have valueSpan : Codec.Span (fun a => Codec.InSpan a (out + 16) 48) (out + 16) 48 16 := by
    refine ⟨?_, ?_, ?_, fun _ h => h⟩ <;> bv_omega
  have active (off bytes : Nat) (fits : off + bytes ≤ 48) :
      ∀ a, Codec.InSpan a (out + 16 + BitVec.ofNat 64 off) bytes →
        Codec.InSpan a (out + 16) 48 :=
    fun _ h => Emit.span_shift (out + 16) off bytes 48 fits h
  apply Codec.DecodedStored.seq
  · refine ⟨valueSpan, ?_⟩
    refine ⟨loaded.2.1, ?_⟩
    simpa only [BitVec.ofNat_zero, BitVec.add_zero] using active 0 1 (by decide)
  · decide
  · intro _
    rfl
  · refine {
      pointer := ⟨?_, active 8 8 (by decide)⟩
      length := ⟨?_, active 16 8 (by decide)⟩
      countBound := by decide
      byteBound := by decide
      span := ?_ }
    · simpa only [BitVec.add_assoc, BitVec.reduceAdd, Codec.decodedChildrenPointer] using loaded.2.2.1
    · simpa only [BitVec.add_assoc, BitVec.reduceAdd, List.length_nil] using loaded.2.2.2
    · refine ⟨by decide, by decide, by decide, ?_⟩
      rintro a ⟨i, hi, equal⟩
      cases hi
  · exact .nil

end SszX86.CodecDeserialize
