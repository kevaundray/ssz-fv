import SszX86.NatMulMemoryOutput
import SszNatOperandNormalization

namespace SszX86.NatMul
open SszNative
open UintCodec

/-- The complete committed buffer is a physical Large before normalization. -/
theorem allocated_at (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (m : DataMem) (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = some r)
    (written : NatMemory.wordsAt (widthLoad m) r.pointer
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written) :
    (NatOperand.large (BitVec.ofNat 64 r.pointer)
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written).At (widthLoad m) := by
  have bounds := allocation_bounds s left right address capacity used ra owned r allocated
  have pointer := allocated_pointer_nat s left right address capacity used ra owned r allocated
  simp only [NatOperand.At, pointer]
  exact ⟨bounds.1, bounds.2.1, bounds.2.2.2.2.2, written⟩

/-- The model fixes the exact normalized pointer and payload, while its retained
allocation still observes every word originally written by the row loops. -/
theorem allocated_result_at (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (m : DataMem) (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = some r)
    (written : NatMemory.wordsAt (widthLoad m) r.pointer
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written)
    (result : NatOperand)
    (success : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result = .ok result) :
    result.At (widthLoad m) := by
  have expected := allocation_result left right address capacity used r allocated
  have same := Except.ok.inj (success.symm.trans expected)
  rw [same]
  exact NatOperand.fromWords_at _ _ _
    (allocated_at s left right address capacity used ra owned m r allocated written)

theorem success_observed (m : DataMem) (out : BitVec 64) (result : NatOperand)
    (stored : result.At (widthLoad (successMem m out result.pointer result.payload))) :
    NatArithmetic.AddResultAt (widthLoad (successMem m out result.pointer result.payload))
      out.toNat (.ok result) := by
  obtain ⟨pointer, payload, status⟩ := success_reads m out result.pointer result.payload
  exact ⟨⟨pointer, payload, stored⟩, status⟩

/-- Publication does not require a post-state operand hypothesis: its exact
result observation follows from the loop's written-buffer observation. -/
theorem allocated_publish_observed (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (m : DataMem) (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = some r)
    (written : NatMemory.wordsAt (widthLoad m) r.pointer
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written)
    (result : NatOperand)
    (success : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result = .ok result) :
    NatArithmetic.AddResultAt
      (widthLoad (successMem m s.regs.rdi.toBitVec result.pointer result.payload))
      s.regs.rdi.toNat (.ok result) := by
  apply success_observed
  have publish := success_publish_frame s m result.pointer result.payload result owned.output_bound
  exact allocated_result_at s left right address capacity used ra owned _ r allocated
    (publish.written owned r allocated written) result success

end SszX86.NatMul
