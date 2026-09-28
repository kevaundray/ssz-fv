import SszX86.BitVectorStackPair
import SszX86.BitVectorWorldAdd

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem allocation_spans_protected {α : Type} (s : MachineData)
    (address capacity used : BitVec 64) (outcome : NatArithmetic.Outcome α)
    (regions : ∀ reservation, outcome.allocation = some reservation →
      Protected s address capacity used reservation.pointer (8 * outcome.written.length)) :
    ∀ span ∈ SszNative.BitVector.allocationWrites outcome,
      Protected s address capacity used span.1 span.2 := by
  intro span member
  cases allocated : outcome.allocation with
  | none => simp only [SszNative.BitVector.allocationWrites, allocated, List.not_mem_nil] at member
  | some reservation =>
    simp only [SszNative.BitVector.allocationWrites, allocated, List.mem_singleton] at member
    subst span
    exact regions reservation allocated

theorem division_spans_protected (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used ra : BitVec 64)
    (owned : Owned s saved length data address capacity used) :
    ∀ span ∈ SszNative.BitVector.allocationWrites
        (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat),
      Protected s address capacity
        (outcomeCursor (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat))
        span.1 span.2 := by
  apply allocation_spans_protected
  exact (entry_world s saved length data address capacity used ra owned).division_written_protected
    (division_owned s saved length data address capacity used ra owned)

theorem work_frame_allocation {α : Type} {s : MachineData} {before after : DataMem}
    {address capacity used : BitVec 64} (frame : RegionsFrame before after [(workStart s, workSize)])
    (outcome : NatArithmetic.Outcome α)
    (stored : SszNative.BitVector.allocationAt (widthLoad before) outcome)
    (protectedSpans : ∀ span ∈ SszNative.BitVector.allocationWrites outcome,
      Protected s address capacity used span.1 span.2) :
    SszNative.BitVector.allocationAt (widthLoad after) outcome := by
  have stable : StableFrame {s with dmem := before} address capacity used after := by
    apply frame.weaken
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    simp [workStart]
  intro reservation allocated
  have hp := protectedSpans (reservation.pointer, 8 * outcome.written.length)
    (by simp only [SszNative.BitVector.allocationWrites, allocated, List.mem_singleton])
  exact stable.words reservation.pointer outcome.written (stored reservation allocated) (hp.with_memory before)

theorem call_work_frame (s u : MachineData) (ra : BitVec 64)
    (stack : u.regs.rsp = s.regs.rsp)
    (low : 72 ≤ s.regs.rsp.toNat) (high : s.regs.rsp.toNat + 368 ≤ 2^64) :
    RegionsFrame u.dmem (callState u ra).dmem [(workStart s, workSize)] := by
  have lowBV : 72 ≤ s.regs.rsp.toBitVec.toNat := low
  have highBV : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 := high
  intro a outside
  apply NatDivision.call_frame u ra a
  intro i hi
  have apart := outside (workStart s, workSize) (by simp)
  change Body.Outside a.toNat (s.regs.rsp.toBitVec.toNat - 72) 296 at apart
  rw [stack]
  unfold Body.Outside at apart
  bv_omega

theorem add_keeps_allocation {α : Type} (s u : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64)
    (owned : NatAdd.Owned u left right address capacity used ra)
    (low : 72 ≤ s.regs.rsp.toNat)
    (output : u.regs.rdi.toNat = s.regs.rsp.toNat + 16)
    (stack : u.regs.rsp.toNat = s.regs.rsp.toNat - 8)
    (arena : u.regs.r9 = s.regs.rbx)
    (t : MachineState) (post : NatAdd.Post u left right address capacity used ra t)
    (earlier : NatArithmetic.Outcome α)
    (protectedSpans : ∀ span ∈ SszNative.BitVector.allocationWrites earlier,
      Protected s address capacity used span.1 span.2)
    (stored : SszNative.BitVector.allocationAt (widthLoad u.dmem) earlier) :
    SszNative.BitVector.allocationAt (widthLoad t.1.dmem) earlier := by
  intro reservation allocated
  have hp := protectedSpans (reservation.pointer, 8 * earlier.written.length)
    (by simp only [SszNative.BitVector.allocationWrites, allocated, List.mem_singleton])
  exact add_keeps_words s u left right address capacity used ra owned low output stack arena
    t post reservation.pointer earlier.written hp (stored reservation allocated)

end SszX86.BitVector
