import SszX86.MeasureBitsCountPrefix
import SszX86.MeasureBitsPublication

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

def listCalls (bits : Packed) (address capacity used : BitVec 64) :=
  [countCall bits address capacity used, encodedCall bits address capacity used]

theorem encoded_call_eq (bits : Packed) (address capacity used : BitVec 64) :
    NatArithmetic.fromWide address.toNat capacity.toNat (countUsed bits address capacity used).toNat
      (encodedWide bits.count) = encodedCall bits address capacity used := by
  rw [count_used_nat]
  rfl

theorem two_call_geometry (bits : Packed) (address capacity used : BitVec 64)
    (call : NatArithmetic.Outcome NatOperand) (member : call ∈ listCalls bits address capacity used)
    (r : Arena.Reservation) (allocated : call.allocation = some r) :
    address.toNat + used.toNat ≤ r.pointer ∧
      r.pointer + 8 * call.written.length ≤ address.toNat + capacity.toNat := by
  simp only [listCalls, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · subst call
    have geometry := wide_allocation_geometry address.toNat capacity.toNat used.toNat bits.count r allocated
    rw [show (countCall bits address capacity used).written = _ from geometry.2.1]
    exact ⟨geometry.2.2.1, by simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using geometry.2.2.2.1⟩
  · subst call
    have geometry := wide_allocation_geometry address.toNat capacity.toNat
      (countCall bits address capacity used).used (encodedWide bits.count) r allocated
    have monotone := (count_call_used_range bits address capacity used).1
    rw [show (encodedCall bits address capacity used).written = _ from geometry.2.1]
    refine ⟨by omega, ?_⟩
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using geometry.2.2.2.1

theorem prefix_writes_mono (s : MachineData) (left right : List (NatArithmetic.Outcome NatOperand))
    (included : ∀ call ∈ left, call ∈ right) (a : BitVec 64) :
    PrefixWrites s left a → PrefixWrites s right a := by
  rintro (⟨call, member, r, allocated, payload⟩ | ⟨⟨call, member, r, allocated⟩, cursor⟩ | work)
  · exact Or.inl ⟨call, included call member, r, allocated, payload⟩
  · exact Or.inr (Or.inl ⟨⟨call, included call member, r, allocated⟩, cursor⟩)
  · exact Or.inr (Or.inr work)

structure ConstructorResources (s : MachineData) (bits : Packed)
    (address capacity used : BitVec 64) (t : MachineData) : Prop where
  frame : MemoryFrame s.dmem t.dmem (PrefixWrites s (listCalls bits address capacity used))
  mapping : MappedExtension s.dmem t.dmem
  observed : NatArithmetic.AddResultAt (widthLoad t.dmem) (s.regs.rsp.toNat + 24)
    (encodedCall bits address capacity used).result
  header : widthLoad t.dmem s.regs.rcx.toNat 8 = some address.toNat ∧
    widthLoad t.dmem (s.regs.rcx.toNat + 8) 8 = some capacity.toNat
  cursor : widthLoad t.dmem (s.regs.rcx.toNat + 16) 8 = some (encodedCall bits address capacity used).used
  calls : CallsAt (widthLoad t.dmem) (listCalls bits address capacity used)
  stack : t.regs.rsp = s.regs.rsp
  output : t.regs.rbx = s.regs.rbx
  vectors : t.zmms = s.zmms

theorem constructor_resources (s before : MachineData) (after : MachineState)
    (desc : Desc) (bits : Packed) (buffer address capacity used ra : BitVec 64)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (previous : CountPrefix s bits address capacity used before)
    (headerReg : before.regs.rcx = s.regs.rcx)
    (outReg : before.regs.rdi.toBitVec = s.regs.rsp.toBitVec + 24)
    (helperOwned : NatFromU128.Owned (callState before ra) (encodedWide bits.count)
      address capacity (countUsed bits address capacity used) ra)
    (post : NatFromU128.Post (callState before ra) (encodedWide bits.count)
      address capacity (countUsed bits address capacity used) ra after) :
    ConstructorResources s bits address capacity used after.1 := by
  have callFrame : MemoryFrame before.dmem (callState before ra).dmem
      (fun a => InSpan a (s.regs.rsp.toBitVec - 16) 232) := by
    simpa only [previous.stack] using call_frame before ra
  have previousCalls := calls_frame _ _ _ _ callFrame
    (first_allocation_stack_safe s desc bits buffer address capacity used owned) previous.calls
  have preserved := constructor_preserves_first_call s before after desc bits buffer address capacity used
    (countUsed bits address capacity used) ra (encodedWide bits.count) owned
    (count_used_nat bits address capacity used) helperOwned headerReg outReg previousCalls post
  have outNat : before.regs.rdi.toNat = s.regs.rsp.toNat + 24 := by
    have bound := owned.stackBound
    rw [← UInt64.toNat_toBitVec, outReg, ← UInt64.toNat_toBitVec] at *
    bv_omega
  have secondFrame := constructor_frame s before after address capacity
    (countUsed bits address capacity used) ra (encodedWide bits.count) helperOwned
    previous.stack headerReg outReg post
  rw [encoded_call_eq] at secondFrame
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a safe
    apply (secondFrame a (fun writes => safe (prefix_writes_mono s _ _
      (by intro call member; simp only [listCalls, List.mem_cons, List.not_mem_nil, or_false] at member ⊢; exact Or.inr member)
      a writes))).trans
    exact previous.frame a (fun writes => safe (prefix_writes_mono s _ _
      (by intro call member; simp only [listCalls, List.mem_cons, List.not_mem_nil, or_false] at member ⊢; exact Or.inl member)
      a writes))
  · rw [post.memory]
    exact mapped_extension_trans _ _ _ previous.mapping
      (mapped_extension_trans _ _ _ (mapped_extension_store _ _ _ _)
        (constructor_result_mapped (callState before ra) address capacity
          (countUsed bits address capacity used) (encodedWide bits.count)))
  · simpa only [callState, outNat, encoded_call_eq] using post.observed
  · simpa only [callState, headerReg] using post.header
  · simpa only [callState, headerReg, encoded_call_eq] using post.cursor
  · intro call member r allocated
    simp only [listCalls, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · subst call
      exact preserved _ (by simp only [List.mem_singleton]) r allocated
    · subst call
      have allocated' : (NatFromU128.outcome address capacity (countUsed bits address capacity used)
          (encodedWide bits.count)).allocation = some r := by simpa only [encoded_call_eq] using allocated
      have geometry := wide_allocation_geometry address.toNat capacity.toNat
        (countUsed bits address capacity used).toNat (encodedWide bits.count) r allocated'
      have reserveGeometry := NatFromU128.reserve_geometry (callState before ra) (encodedWide bits.count)
        address capacity (countUsed bits address capacity used) ra helperOwned r geometry.1
      have pointerNat : (BitVec.ofNat 64 r.pointer).toNat = r.pointer := Nat.mod_eq_of_lt (by omega)
      have words := (post.written r allocated').2.2.2
      simpa only [pointerNat, encoded_call_eq] using words
  · apply UInt64.eq_of_toBitVec_eq
    have returned := post.returned.sp
    simpa only [callState, UInt64.toBitVec_ofBitVec, previous.stack, BitVec.sub_add_cancel] using returned
  · exact post.returned.rbx.trans previous.output
  · exact post.returned.simd.trans previous.vectors

end SszX86.Measure.Bits
