import SszArm.BitVectorFrame

namespace SszArm.BitVector

/-- All native error copies have a fixed positive extent. The public output
separation protects the entire activation, not merely the currently used slot. -/
theorem output_copy_space {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (destinationOffset sourceOffset bytes : Nat)
    (positive : 0 < bytes) (destinationWithin : destinationOffset + bytes ≤ 80)
    (sourceWithin : sourceOffset + bytes ≤ 272) :
    (r (.GPR 0#5) s + BitVec.ofNat 64 destinationOffset).toNat + bytes ≤ 2^64 ∧
    (r (.GPR 31#5) s + BitVec.ofNat 64 sourceOffset).toNat + bytes ≤ 2^64 ∧
    Memcpy.Disjoint (r (.GPR 0#5) s + BitVec.ofNat 64 destinationOffset)
      (r (.GPR 31#5) s + BitVec.ofNat 64 sourceOffset) bytes := by
  have outputBound := owned.outputBound
  have stackBound := owned.stackHigh
  have stackLow := owned.stackLow
  have destination : (r (.GPR 0#5) s + BitVec.ofNat 64 destinationOffset).toNat =
      (r (.GPR 0#5) s).toNat + destinationOffset := by bv_omega
  have source : (r (.GPR 31#5) s + BitVec.ofNat 64 sourceOffset).toNat =
      (r (.GPR 31#5) s).toNat + sourceOffset := by bv_omega
  refine ⟨by rw [destination]; omega, by rw [source]; omega, ?_⟩
  rcases owned.outputStack with empty | separate
  · omega
  · have disjoint := separate ((r (.GPR 31#5) s).toNat - 80, 448) (by simp)
    simp only [Memcpy.Disjoint, destination, source]
    omega

theorem stack_copy_space {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (destinationOffset sourceOffset bytes : Nat)
    (destinationWithin : destinationOffset + bytes ≤ 272)
    (sourceWithin : sourceOffset + bytes ≤ 272)
    (ordered : destinationOffset + bytes ≤ sourceOffset) :
    (r (.GPR 31#5) s + BitVec.ofNat 64 destinationOffset).toNat + bytes ≤ 2^64 ∧
    (r (.GPR 31#5) s + BitVec.ofNat 64 sourceOffset).toNat + bytes ≤ 2^64 ∧
    Memcpy.Disjoint (r (.GPR 31#5) s + BitVec.ofNat 64 destinationOffset)
      (r (.GPR 31#5) s + BitVec.ofNat 64 sourceOffset) bytes := by
  have stackBound := owned.stackHigh
  have destination : (r (.GPR 31#5) s + BitVec.ofNat 64 destinationOffset).toNat =
      (r (.GPR 31#5) s).toNat + destinationOffset := by bv_omega
  have source : (r (.GPR 31#5) s + BitVec.ofNat 64 sourceOffset).toNat =
      (r (.GPR 31#5) s).toNat + sourceOffset := by bv_omega
  refine ⟨by rw [destination]; omega, by rw [source]; omega, ?_⟩
  simp only [Memcpy.Disjoint, destination, source]
  exact Or.inl (by omega)

theorem output_copy_covered {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (offset bytes : Nat) (positive : 0 < bytes)
    (within : offset + bytes ≤ 80) :
    Covers (localWrites s) [((r (.GPR 0#5) s + BitVec.ofNat 64 offset).toNat, bytes)] := by
  have bound := owned.outputBound
  have address : (r (.GPR 0#5) s + BitVec.ofNat 64 offset).toNat =
      (r (.GPR 0#5) s).toNat + offset := by bv_omega
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  exact ⟨((r (.GPR 0#5) s).toNat, 80), by simp [localWrites],
    by rw [address]; omega, by rw [address]; omega⟩

theorem stack_copy_covered {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (offset bytes : Nat) (within : offset + bytes ≤ 272) :
    Covers (localWrites s) [((r (.GPR 31#5) s + BitVec.ofNat 64 offset).toNat, bytes)] := by
  have low := owned.stackLow
  have high := owned.stackHigh
  have address : (r (.GPR 31#5) s + BitVec.ofNat 64 offset).toNat =
      (r (.GPR 31#5) s).toNat + offset := by bv_omega
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  exact ⟨((r (.GPR 31#5) s).toNat - 80, 352), by simp [localWrites],
    by rw [address]; omega, by rw [address]; omega⟩

theorem output_store_frame {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (offset bytes : Nat) (positive : 0 < bytes)
    (within : offset + bytes ≤ 80) (value : BitVec (bytes * 8)) :
    Delimited.MemoryFrame (localWrites s) c
      (write_mem_bytes bytes (r (.GPR 0#5) s + BitVec.ofNat 64 offset) value c) := by
  have bound := owned.outputBound
  have physical : (r (.GPR 0#5) s + BitVec.ofNat 64 offset).toNat + bytes ≤ 2^64 := by bv_omega
  exact (output_copy_covered owned offset bytes positive within).frame
    (Delimited.store_frame c _ bytes value physical)

end SszArm.BitVector
