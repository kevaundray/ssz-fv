import SszX86.MeasureBitsConstructorCalls

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

def countUsed (bits : Packed) (address capacity used : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (countCall bits address capacity used).used

theorem count_used_nat (bits : Packed) (address capacity used : BitVec 64) :
    (countUsed bits address capacity used).toNat = (countCall bits address capacity used).used :=
  Nat.mod_eq_of_lt (count_call_used_bound bits address capacity used)

/-- Verified resources after the first count exists; the semantics is the shared
native call itself, not a second list model. Local stores/comparison may follow. -/
structure CountPrefix (s : MachineData) (bits : Packed)
    (address capacity used : BitVec 64) (t : MachineData) : Prop where
  frame : MemoryFrame s.dmem t.dmem (PrefixWrites s [countCall bits address capacity used])
  mapping : MappedExtension s.dmem t.dmem
  arena : ArenaAt t.dmem s.regs.rcx.toBitVec address capacity (countUsed bits address capacity used)
  calls : CallsAt (widthLoad t.dmem) [countCall bits address capacity used]
  stack : t.regs.rsp = s.regs.rsp
  output : t.regs.rbx = s.regs.rbx
  vectors : t.zmms = s.zmms

theorem calls_frame (before after : DataMem)
    (calls : List (NatArithmetic.Outcome NatOperand)) (writable : BitVec 64 → Prop)
    (frame : MemoryFrame before after writable)
    (safe : ∀ a, AllocationWrites calls a → ¬ writable a)
    (stored : CallsAt (widthLoad before) calls) : CallsAt (widthLoad after) calls := by
  intro call member r allocated i
  have same := frame_load_window before after writable frame (BitVec.ofNat 64 r.pointer)
    (8 * i.val) 8 (8 * call.written.length) (by have hi := i.isLt; omega) (by
      intro a inside
      exact safe a ⟨call, member, r, allocated, inside⟩)
  unfold widthLoad
  rw [BitVec.ofNat_add, same]
  simpa only [widthLoad, BitVec.ofNat_add] using stored call member r allocated i

theorem first_allocation_stack_safe (s : MachineData) (desc : Desc) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (a : BitVec 64) (allocated : AllocationWrites [countCall bits address capacity used] a) :
    ¬ InSpan a (s.regs.rsp.toBitVec - 16) 232 := by
  obtain ⟨call, member, r, hasAllocation, ⟨i, hi, rfl⟩⟩ := allocated
  have same : call = countCall bits address capacity used := by simpa only [List.mem_singleton] using member
  subst call
  have geometry := wide_allocation_geometry address.toNat capacity.toNat used.toNat bits.count r hasAllocation
  have reserveGeometry := reserve_geometry s desc (.bits bits) buffer address capacity used owned r geometry.1
  have pointerNat : (BitVec.ofNat 64 r.pointer).toNat = r.pointer := Nat.mod_eq_of_lt (by omega)
  have payloadBound : i < 16 := by
    simpa only [countCall, geometry.2.1, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using hi
  have stackNat : (s.regs.rsp.toBitVec - 16).toNat = s.regs.rsp.toNat - 16 := by
    have low := owned.stackLow
    rw [← UInt64.toNat_toBitVec] at low ⊢
    bv_omega
  have apart : Large.Disjoint (BitVec.ofNat 64 r.pointer) (s.regs.rsp.toBitVec - 16) 16 232 := by
    apply Body.apart_bytes
    · rw [pointerNat]
      exact reserveGeometry.2.2.2.2.2.1
    · rw [stackNat]
      have bound := owned.stackBound
      omega
    · rw [pointerNat, stackNat]
      have separated := owned.freeStack
      unfold Body.Apart at separated ⊢
      omega
  rintro ⟨j, hj, equal⟩
  exact apart i payloadBound j hj equal

theorem local_header_keep (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used)
    (before after : DataMem)
    (frame : MemoryFrame before after (fun a => InSpan a (s.regs.rsp.toBitVec - 16) 232))
    (off : Nat) (within : off + 8 ≤ 24) :
    widthLoad after (s.regs.rcx.toNat + off) 8 = widthLoad before (s.regs.rcx.toNat + off) 8 := by
  unfold widthLoad
  rw [← UInt64.toNat_toBitVec, width_address]
  congr 1
  apply frame_load_window before after _ frame s.regs.rcx.toBitVec off 8 24 within
  rintro a ⟨i, hi, rfl⟩ ⟨j, hj, equal⟩
  exact owned.headerStack i hi j (by omega) equal

theorem CountPrefix.stack_extension {s before after : MachineData} {desc : Desc} {bits : Packed}
    {buffer address capacity used : BitVec 64}
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (previous : CountPrefix s bits address capacity used before)
    (memory : MemoryFrame before.dmem after.dmem (fun a => InSpan a (s.regs.rsp.toBitVec - 16) 232))
    (mapping : MappedExtension before.dmem after.dmem)
    (sp : after.regs.rsp = before.regs.rsp)
    (outReg : after.regs.rbx = before.regs.rbx)
    (vectors : after.zmms = before.zmms) : CountPrefix s bits address capacity used after := by
  refine ⟨?_, mapped_extension_trans _ _ _ previous.mapping mapping, ?_, ?_,
    sp.trans previous.stack, outReg.trans previous.output, vectors.trans previous.vectors⟩
  · intro a safe
    exact (memory a (fun inside => safe (Or.inr (Or.inr inside)))).trans (previous.frame a safe)
  · refine ⟨?_, ?_, ?_⟩
    · simpa only [UInt64.toNat_toBitVec, Nat.add_zero] using
        (local_header_keep s desc (.bits bits) buffer address capacity used owned _ _ memory 0 (by decide)).trans previous.arena.1
    · simpa only [UInt64.toNat_toBitVec] using
        (local_header_keep s desc (.bits bits) buffer address capacity used owned _ _ memory 8 (by decide)).trans previous.arena.2.1
    · simpa only [UInt64.toNat_toBitVec] using
        (local_header_keep s desc (.bits bits) buffer address capacity used owned _ _ memory 16 (by decide)).trans previous.arena.2.2
  · exact calls_frame _ _ _ _ memory
      (first_allocation_stack_safe s desc bits buffer address capacity used owned) previous.calls

theorem count_prefix_small (s t : MachineData) (desc : Desc) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (small : bits.count.toNat < 2^64)
    (memory : t.dmem = s.dmem) (sp : t.regs.rsp = s.regs.rsp)
    (outReg : t.regs.rbx = s.regs.rbx) (vectors : t.zmms = s.zmms) :
    CountPrefix s bits address capacity used t := by
  have model := NatFromU128.result_model_small address capacity used bits.count small
  refine ⟨?_, ?_, ?_, ?_, sp, outReg, vectors⟩
  · intro a safe
    rw [memory]
  · rw [memory]
    exact mapped_extension_refl _
  · simpa only [memory, countUsed, countCall, model, NatArithmetic.unchanged,
      BitVec.ofNat_toNat, BitVec.setWidth_eq] using owned.arena
  · intro call member r allocated
    have same : call = countCall bits address capacity used := by simpa only [List.mem_singleton] using member
    subst call
    simp only [countCall, model, NatArithmetic.unchanged] at allocated
    cases allocated

end SszX86.Measure.Bits
