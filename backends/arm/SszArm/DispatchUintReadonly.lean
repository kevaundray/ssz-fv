import SszArm.DispatchUintPost

namespace SszArm.Dispatch.Unsigned

def CapBytes (s t : ArmState) : Prop :=
  Scalar.pointer s ≠ 0#64 → ∀ a : BitVec 64,
    (Scalar.pointer s).toNat ≤ a.toNat →
    a.toNat < (Scalar.pointer s).toNat + 8 * (Scalar.payload s).toNat → t.mem a = s.mem a

theorem capBytes {s t : ArmState} {width : Nat} {data : Ssz.Bytes}
    (owned : Owned s width data) (post : NativePost s t width data) : CapBytes s t := by
  intro pointerNonzero a low high
  have payloadNonzero : Scalar.payload s ≠ 0#64 := by
    intro zero
    simp only [zero, BitVec.toNat_ofNat] at high
    omega
  apply post.frame a
  · have separate := owned.scalar.limbsOutput pointerNonzero payloadNonzero; omega
  · have separate := owned.scalar.limbsStack pointerNonzero payloadNonzero; omega
  · have separate := owned.scalar.limbsStack pointerNonzero payloadNonzero; omega
  · cases allocated : reservation s width data with
    | none => simp only [ExtraOutside, allocated]
    | some q =>
      obtain ⟨freshLow, freshHigh, notFull⟩ := owned.geometry q allocated
      simp only [ExtraOutside, allocated]
      constructor
      · have separate := owned.limbsHeader pointerNonzero payloadNonzero; omega
      · have separate := owned.limbsStorage pointerNonzero payloadNonzero; omega

theorem descriptorPair {s t : ArmState} {width : Nat} {data : Ssz.Bytes}
    (owned : Owned s width data) (post : NativePost s t width data) :
    SszNative.NatMemory.Pair (UintCodec.widthLoad t) (Scalar.pointer s) (Scalar.payload s) width := by
  rcases owned.scalar.pair with small | ⟨words, positive, aligned, bound, count, memory, value⟩
  · exact Or.inl small
  · refine Or.inr ⟨words, positive, aligned, bound, count, ?_, value⟩
    intro i
    have within := i.isLt
    have nonzero : Scalar.pointer s ≠ 0#64 := by
      intro zero
      simp only [zero, BitVec.toNat_ofNat] at positive
      omega
    have same : read_mem_bytes 8 (BitVec.ofNat 64 ((Scalar.pointer s).toNat + 8 * i.val)) t =
        read_mem_bytes 8 (BitVec.ofNat 64 ((Scalar.pointer s).toNat + 8 * i.val)) s := by
      apply BoolCodec.read_bytes_congr
      intro j inside
      apply capBytes owned post nonzero <;> bv_omega
    simpa only [UintCodec.widthLoad, same] using memory i

theorem descriptorNat {s t : ArmState} {width : Nat} {data : Ssz.Bytes}
    (owned : Owned s width data) (post : NativePost s t width data) :
    SszNative.NatMemory.At (UintCodec.widthLoad t) ((r (.GPR 1#5) s).toNat + 8) width := by
  have header (offset : Nat) (within : offset + 8 ≤ 24) :
      read_mem_bytes 8 (r (.GPR 1#5) s + BitVec.ofNat 64 offset) t =
        read_mem_bytes 8 (r (.GPR 1#5) s + BitVec.ofNat 64 offset) s := by
    apply BoolCodec.read_bytes_congr
    intro i inside
    have bound := owned.scalar.descriptorBound
    apply post.descriptorBytes <;> bv_omega
  apply (descriptorPair owned post).at
  · simp only [UintCodec.widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Scalar.pointer, header 8 (by decide)]
  · simpa only [UintCodec.widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Scalar.payload, BitVec.add_assoc, show 8#64 + 8#64 = 16#64 by decide] using
      congrArg (fun word : BitVec 64 => some word.toNat) (header 16 (by decide))

/-- All original borrowed width words remain unchanged in addition to the
complete success/error/resource/ABI frame from the actual entry theorem. -/
structure Post (s t : ArmState) (width : Nat) (data : Ssz.Bytes) : Prop extends NativePost s t width data where
  capBytes : CapBytes s t
  descriptorNat : SszNative.NatMemory.At (UintCodec.widthLoad t) ((r (.GPR 1#5) s).toNat + 8) width

theorem post_of_body {s t : ArmState} {width : Nat} {data : Ssz.Bytes}
    (owned : Owned s width data) (body : UintCodec.Body.Result (entered s .uint) t width data) :
    Post s t width data := by
  have post := native_post_of_body owned body
  exact ⟨post, capBytes owned post, descriptorNat owned post⟩

end SszArm.Dispatch.Unsigned
