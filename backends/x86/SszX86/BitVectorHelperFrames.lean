import SszX86.BitVectorFrame

namespace SszX86.BitVector
open SszNative UintCodec

theorem RegionsFrame.cover {before after : DataMem} {small large : List (Nat × Nat)}
    (frame : RegionsFrame before after small)
    (covered : ∀ span ∈ small, ∃ outer ∈ large,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2) :
    RegionsFrame before after large := by
  intro a outside
  apply frame a
  intro span member
  obtain ⟨outer, contains, start, finish⟩ := covered span member
  have separated := outside outer contains
  unfold Body.Outside at *
  omega

theorem division_regions (s : MachineData) (m : DataMem)
    (outcome : NatArithmetic.Outcome (NatOperand × BitVec 64))
    (frame : NatDivision.Frame s m outcome) :
    RegionsFrame s.dmem m
      ([(s.regs.rdi.toNat, 68), (s.regs.rsp.toNat - 64, 64), (s.regs.r8.toNat + 16, 8)] ++
        SszNative.BitVector.allocationWrites outcome) := by
  intro a outside
  apply frame a
  · exact outside (s.regs.rdi.toNat, 68) (by simp)
  · exact outside (s.regs.rsp.toNat - 64, 64) (by simp)
  · intro reservation allocated
    refine ⟨outside (s.regs.r8.toNat + 16, 8) (by simp), ?_⟩
    apply outside (reservation.pointer, 8 * outcome.written.length)
    simp only [SszNative.BitVector.allocationWrites, allocated, List.mem_append, List.mem_cons]
    simp

theorem add_regions (s : MachineData) (m : DataMem) (outcome : NatArithmetic.Outcome NatOperand)
    (frame : NatAdd.Frame s m outcome) :
    RegionsFrame s.dmem m
      ([(s.regs.rdi.toNat, 68), (s.regs.rsp.toNat - 48, 48), (s.regs.r9.toNat + 16, 8)] ++
        SszNative.BitVector.allocationWrites outcome) := by
  intro a outside
  apply frame a
  · exact outside (s.regs.rdi.toNat, 68) (by simp)
  · exact outside (s.regs.rsp.toNat - 48, 48) (by simp)
  · intro reservation allocated
    refine ⟨outside (s.regs.r9.toNat + 16, 8) (by simp), ?_⟩
    apply outside (reservation.pointer, 8 * outcome.written.length)
    simp only [SszNative.BitVector.allocationWrites, allocated, List.mem_append, List.mem_cons]
    simp

theorem exact_regions (s : MachineData) (m : DataMem) (success : Bool)
    (frame : NatExact.Frame s m success) :
    RegionsFrame s.dmem m [(s.regs.rdi.toNat, 68)] := by
  intro a outside
  have separated := outside (s.regs.rdi.toNat, 68) (by simp)
  unfold NatExact.Frame at frame
  split at frame
  · apply frame a
    unfold Body.Outside at *
    omega
  · exact frame a separated

theorem to_u128_regions (s : MachineData) (m : DataMem) (result : Option (BitVec 128))
    (frame : NatToU128.Frame s m result) :
    RegionsFrame s.dmem m [(s.regs.rdi.toNat, 32)] := by
  intro a outside
  have separated := outside (s.regs.rdi.toNat, 32) (by simp)
  apply frame a
  cases result <;> simp only [NatToU128.writtenBytes] <;> unfold Body.Outside at * <;> omega

end SszX86.BitVector
