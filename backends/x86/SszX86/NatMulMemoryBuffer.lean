import SszX86.NatMulMemory
import SszX86.NatAddCarryMath

namespace SszX86.NatMul
open SszNative
open UintCodec

/-- An intermediate buffer update owns exactly its physical destination. -/
def BufferFrame (before after : DataMem) (pointer count : Nat) : Prop :=
  ∀ a : BitVec 64, Body.Outside a.toNat pointer count → after.get? a = before.get? a

theorem BufferFrame.trans {first middle last : DataMem} {pointer count : Nat}
    (front : BufferFrame first middle pointer count) (back : BufferFrame middle last pointer count) :
    BufferFrame first last pointer count := by
  intro a outside
  exact (back a outside).trans (front a outside)

theorem fill_buffer_frame (m : DataMem) (dst : BitVec 64) (index capacity : Nat)
    (words : List (BitVec 64)) (bound : dst.toNat + capacity ≤ 2^64)
    (inside : 8 * (index + words.length) ≤ capacity) :
    BufferFrame m (Large.fillMem m dst index words) dst.toNat capacity := by
  intro a outside
  apply Large.fill_frame
  intro j _ high
  exact Body.outside_byte dst a capacity j bound outside (by omega)

theorem BufferFrame.load {before after : DataMem} {pointer count : Nat}
    (frame : BufferFrame before after pointer count) (p : BitVec 64) (n : Nat)
    (bound : p.toNat+n ≤ 2^64) (apart : Body.Apart p.toNat n pointer count) :
    Mem.loadInt after p n = Mem.loadInt before p n := by
  apply memmove_loadInt_congr
  intro i hi
  apply frame
  have natural : (p + BitVec.ofNat 64 i).toNat = p.toNat+i := by bv_omega
  rw [natural]
  unfold Body.Outside Body.Apart at *
  omega

theorem BufferFrame.mapped {before after : DataMem} {pointer count : Nat}
    (frame : BufferFrame before after pointer count) (p : BitVec 64) (n : Nat)
    (hm : Large.Mapped before p n) (bound : p.toNat+n ≤ 2^64)
    (apart : Body.Apart p.toNat n pointer count) : Large.Mapped after p n := by
  intro i hi
  obtain ⟨byte, old⟩ := hm i hi
  refine ⟨byte, ?_⟩
  rw [frame]
  · exact old
  · have natural : (p + BitVec.ofNat 64 i).toNat = p.toNat+i := by bv_omega
    rw [natural]
    unfold Body.Outside Body.Apart at *
    omega

theorem allocated_operand_apart (s : MachineData) (left right operand : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (stored : operand.At (widthLoad s.dmem)) (protection : OperandProtected s address capacity used operand)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = some r) :
    NatAdd.Carry.Apart operand (BitVec.ofNat 64 r.pointer)
      (8*(SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length) := by
  cases operand with
  | small limb => trivial
  | large pointer words =>
    have bounds := allocation_bounds s left right address capacity used ra owned r allocated
    have pointerNat := allocated_pointer_nat s left right address capacity used ra owned r allocated
    apply Body.apart_bytes
    · exact stored.2.2.1
    · rw [pointerNat]
      exact bounds.2.2.2.2.2
    · rw [pointerNat]
      have apart := protection.arena
      have usedBound := owned.used_bound
      unfold Body.Apart at *
      omega

/-- Use the existing sequential-store theorem, preserving all original limbs. -/
theorem fill_operand_preserved (s : MachineData) (left right operand : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (initial : operand.At (widthLoad s.dmem)) (protection : OperandProtected s address capacity used operand)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = some r)
    (m : DataMem) (current : operand.At (widthLoad m)) (index : Nat) (words : List (BitVec 64))
    (inside : index + words.length ≤
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length) :
    operand.At (widthLoad (Large.fillMem m (BitVec.ofNat 64 r.pointer) index words)) := by
  apply NatAdd.Carry.fill_preserves m operand (BitVec.ofNat 64 r.pointer) index
    (8*(SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length)
    words current
  · exact allocated_operand_apart s left right operand address capacity used ra owned initial protection r allocated
  · omega

/-- Buffer updates preserve any local or saved stack load. -/
theorem BufferFrame.stack_load {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = some r)
    {before after : DataMem} (frame : BufferFrame before after r.pointer
      (8*(SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length))
    (off count : Nat) (inside : off+count ≤ 96) :
    Mem.loadInt after ((s.regs.rsp.toBitVec-96) + BitVec.ofNat 64 off) count =
      Mem.loadInt before ((s.regs.rsp.toBitVec-96) + BitVec.ofNat 64 off) count := by
  have low := owned.stack_low
  have natural : ((s.regs.rsp.toBitVec-96) + BitVec.ofNat 64 off).toNat = s.regs.rsp.toNat-96+off := by
    change 96 ≤ s.regs.rsp.toBitVec.toNat at low
    change ((s.regs.rsp.toBitVec-96) + BitVec.ofNat 64 off).toNat = s.regs.rsp.toBitVec.toNat-96+off
    bv_omega
  apply frame.load
  · rw [natural]
    have bound := s.regs.rsp.toBitVec.isLt
    change s.regs.rsp.toNat < 2^64 at bound
    omega
  · rw [natural]
    have bounds := allocation_bounds s left right address capacity used ra owned r allocated
    have apart := owned.arena_stack
    have usedBound := owned.used_bound
    unfold Body.Apart at *
    omega

/-- In a partially updated list, overwriting its head cannot affect its tail. -/
theorem words_tail_store (m : DataMem) (dst : BitVec 64) (head value : BitVec 64)
    (rest : List (BitVec 64)) (stored : NatMemory.wordsAt (widthLoad m) dst.toNat (head :: rest))
    (bound : dst.toNat + 8*(head :: rest).length ≤ 2^64) :
    NatMemory.wordsAt (widthLoad (Mem.storeInt m dst 8 value.toInt)) (dst.toNat+8) rest := by
  intro i
  have old := stored ⟨i.val+1, by have := i.isLt; simp only [List.length_cons]; omega⟩
  change widthLoad m (dst.toNat+8*(i.val+1)) 8 =
    some ((head :: rest)[i.val+1]'(by have := i.isLt; simp only [List.length_cons]; omega)).toNat at old
  have same : widthLoad (Mem.storeInt m dst 8 value.toInt) (dst.toNat+8+8*i.val) 8 =
      widthLoad m (dst.toNat+8*(i.val+1)) 8 := by
    have offset : dst.toNat+8+8*i.val = dst.toNat+8*(i.val+1) := by omega
    rw [offset]
    unfold widthLoad
    congr 1
    rw [width_address]
    apply BoolCodec.load_store_disjoint
    intro a ha b hb
    have ix := i.isLt
    simp only [List.length_cons] at bound
    bv_omega
  rw [same]
  change widthLoad m (dst.toNat+8*(i.val+1)) 8 = some rest[i.val].toNat at old ⊢
  exact old

end SszX86.NatMul
