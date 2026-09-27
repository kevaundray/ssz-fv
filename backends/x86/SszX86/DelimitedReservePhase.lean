import SszX86.DelimitedCountPhase
import SszX86.DelimitedReservation
import SszX86.DelimitedWorkMemory
import SszX86.DelimitedFinish

namespace SszX86.Delimited
open UintCodec

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private theorem counted_region (s t : MachineData) (data : Ssz.Bytes)
    (state : Counted s t data) (p n : Nat)
    (bound : p + n ≤ 2^64)
    (output : Body.Apart p n s.regs.rdi.toNat 76)
    (stack : Body.Apart p n (s.regs.rsp.toNat - 104) (activationBytes data)) :
    ∀ i < n, t.dmem.get? (BitVec.ofNat 64 (p+i)) =
      s.dmem.get? (BitVec.ofNat 64 (p+i)) := by
  intro i hi
  have physical : p+i < 2^64 := by omega
  apply state.frame
  · unfold Body.Outside Body.Apart at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical]
    omega
  · unfold Body.Outside Body.Apart at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical]
    omega
  · intro r impossible
    cases impossible

private theorem counted_header (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (state : Counted s t data) : Reservation.Header t address capacity used := by
  have same (loadOffset : Nat) (within : loadOffset + 8 ≤ 24) :
      Mem.loadInt t.dmem (s.regs.r8.toBitVec + BitVec.ofNat 64 loadOffset) 8 =
        Mem.loadInt s.dmem (s.regs.r8.toBitVec + BitVec.ofNat 64 loadOffset) 8 := by
    apply memmove_loadInt_congr
    intro i hi
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      ← UInt64.toNat_toBitVec, BitVec.add_assoc] using
      counted_region s t data state s.regs.r8.toNat 24 h.header_bound
        h.header_output h.header_stack (loadOffset+i) (by omega)
  constructor
  · rw [state.arenaAddress]
    have initial := same 0 (by decide)
    simp only [BitVec.add_zero] at initial
    exact initial.trans h.address_load
  · rw [state.arenaAddress]
    exact (same 8 (by decide)).trans h.capacity_load
  · rw [state.arenaAddress]
    exact (same 16 (by decide)).trans h.used_load

/-- Mapping recovery permits the old arena prefix to overlap output or stack:
those regions remain mapped even when their bytes need not remain unchanged. -/
private theorem counted_mapped (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (active : UsesActivation data) (state : Counted s t data)
    (base : BitVec 64) (count : Nat) (regionMapped : Large.Mapped s.dmem base count) :
    Large.Mapped t.dmem base count := by
  intro i hi
  let a := base + BitVec.ofNat 64 i
  by_cases output : Body.Outside a.toNat s.regs.rdi.toNat 76
  · by_cases stack : Body.Outside a.toNat (s.regs.rsp.toNat - 104) (activationBytes data)
    · change ∃ byte, t.dmem.get? a = some byte
      rw [state.frame a output stack (by intro r impossible; cases impossible)]
      exact regionMapped i hi
    · have low := h.stack_low active
      have inside : s.regs.rsp.toNat - 104 ≤ a.toNat ∧ a.toNat < s.regs.rsp.toNat := by
        simp only [Body.Outside, activationBytes, ite_eq_left active] at stack
        omega
      have index : a.toNat - (s.regs.rsp.toNat - 104) < 104 := by omega
      have eq : (s.regs.rsp.toBitVec - 104) +
          BitVec.ofNat 64 (a.toNat - (s.regs.rsp.toNat - 104)) = a := by
        simp only [← UInt64.toNat_toBitVec] at low inside ⊢
        bv_omega
      simpa only [eq] using state.active.stack _ index
  · have inside : s.regs.rdi.toNat ≤ a.toNat ∧ a.toNat < s.regs.rdi.toNat + 76 := by
      unfold Body.Outside at output
      omega
    have index : a.toNat - s.regs.rdi.toNat < 76 := by omega
    have eq : t.regs.rdi.toBitVec + BitVec.ofNat 64 (a.toNat - s.regs.rdi.toNat) = a := by
      rw [state.active.out]
      simp only [← UInt64.toNat_toBitVec] at inside ⊢
      bv_omega
    simpa only [eq] using state.active.output _ index

private def reserveMem (m : DataMem) (cursor pointer finish : Nat)
    (low high : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (BitVec.ofNat 64 cursor) 8 (BitVec.ofNat 64 finish).toInt
  let m := Mem.storeInt m (BitVec.ofNat 64 pointer) 8 low.toInt
  Mem.storeInt m (BitVec.ofNat 64 (pointer+8)) 8 high.toInt

private theorem reserve_mapped (m : DataMem) (cursor pointer finish : Nat)
    (low high base : BitVec 64) (count : Nat) (regionMapped : Large.Mapped m base count) :
    Large.Mapped (reserveMem m cursor pointer finish low high) base count := by
  unfold reserveMem
  repeat' first | exact regionMapped | apply Large.mapped_store

private theorem store_word_frame (m : DataMem) (p : Nat) (value : Int) (a : BitVec 64)
    (bound : p+8 ≤ 2^64) (outside : Body.Outside a.toNat p 8) :
    (Mem.storeInt m (BitVec.ofNat 64 p) 8 value).get? a = m.get? a := by
  have physical : p < 2^64 := by omega
  apply memmove_store_lookup_outside
  intro i hi
  apply Body.outside_byte (BitVec.ofNat 64 p) a 8 i
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical] using bound
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical] using outside
  · simpa only [Int.toBytes_length] using hi

private theorem reserve_frame (m : DataMem) (cursor pointer finish : Nat)
    (low high a : BitVec 64) (header : cursor+8 ≤ 2^64) (room : pointer+16 ≤ 2^64)
    (hc : Body.Outside a.toNat cursor 8) (hp : Body.Outside a.toNat pointer 16) :
    (reserveMem m cursor pointer finish low high).get? a = m.get? a := by
  have lo : Body.Outside a.toNat pointer 8 := by unfold Body.Outside at *; omega
  have hi : Body.Outside a.toNat (pointer+8) 8 := by unfold Body.Outside at *; omega
  unfold reserveMem
  rw [store_word_frame _ (pointer+8) _ a (by omega) hi,
    store_word_frame _ pointer _ a (by omega) lo,
    store_word_frame _ cursor _ a header hc]

private theorem load_word_apart (m : DataMem) (p q : Nat) (value : Int)
    (hp : p+8 ≤ 2^64) (hq : q+8 ≤ 2^64) (apart : Body.Apart p 8 q 8) :
    Mem.loadInt (Mem.storeInt m (BitVec.ofNat 64 q) 8 value) (BitVec.ofNat 64 p) 8 =
      Mem.loadInt m (BitVec.ofNat 64 p) 8 := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj
  unfold Body.Apart at apart
  bv_omega

private theorem reserve_fields (m : DataMem) (cursor pointer finish : Nat)
    (low high : BitVec 64) (header : cursor+8 ≤ 2^64) (room : pointer+16 ≤ 2^64)
    (endBound : finish < 2^64) (apart : Body.Apart cursor 8 pointer 16) :
    widthLoad (reserveMem m cursor pointer finish low high) pointer 8 = some low.toNat ∧
    widthLoad (reserveMem m cursor pointer finish low high) (pointer+8) 8 = some high.toNat ∧
    widthLoad (reserveMem m cursor pointer finish low high) cursor 8 = some finish := by
  have lowHigh : Body.Apart pointer 8 (pointer+8) 8 := by unfold Body.Apart; omega
  have cursorLow : Body.Apart cursor 8 pointer 8 := by unfold Body.Apart at *; omega
  have cursorHigh : Body.Apart cursor 8 (pointer+8) 8 := by unfold Body.Apart at *; omega
  simp only [widthLoad, reserveMem]
  rw [load_word_apart _ pointer (pointer+8) _ (by omega) (by omega) lowHigh]
  rw [load_word_apart _ cursor (pointer+8) _ header (by omega) cursorHigh,
    load_word_apart _ cursor pointer _ header (by omega) cursorLow]
  simp only [stored_word_load, Option.map_some, Int.toNat_natCast,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt endBound]
  exact ⟨True.intro, True.intro, True.intro⟩

private theorem reserve_active (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (activation : UsesActivation data) (state : Counted s t data)
    (r : SszNative.Arena.Reservation)
    (reserved : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r)
    (flags : StatusFlags) : Active s (Reservation.reservedState t address used flags) data := by
  have bounds := SszNative.Delimited.reservation_bounds _ _ _ h.arena_bound h.arena_nonzero r reserved
  obtain ⟨checks, rfl⟩ :=
    (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
  have memory : (Reservation.reservedState t address used flags).dmem =
      reserveMem t.dmem (s.regs.r8.toNat+16)
        (address.toNat + SszNative.Arena.start address.toNat used.toNat)
        (SszNative.Arena.start address.toNat used.toNat+16)
        t.regs.r14.toBitVec t.regs.rbp.toBitVec := by
    simp only [Reservation.reservedState, reserveMem, state.arenaAddress,
      BitVec.ofNat_add, ← UInt64.toNat_toBitVec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨state.active.sp, state.active.out, state.active.source, state.active.length,
    state.active.preceding, state.active.highest, ?_, state.active.simd, ?_, ?_⟩
  · change SavedAt (Reservation.reservedState t address used flags).dmem t.regs.rsp.toBitVec s
    rw [memory]
    apply savedAt_congr t.dmem _ t.regs.rsp.toBitVec s _ state.active.saved
    intro i hi
    apply reserve_frame
    · have bound := h.header_bound; omega
    · exact bounds.2.2.2.2.2
    · have apart := h.header_stack
      have low := h.stack_low activation
      rw [state.active.sp]
      simp only [activationBytes, ite_eq_left activation, Body.Apart,
        Body.Outside, ← UInt64.toNat_toBitVec] at apart low ⊢
      bv_omega
    · have apart := h.arena_stack
      have low := h.stack_low activation
      have usedBound := h.used_bound
      rw [state.active.sp]
      simp only [activationBytes, ite_eq_left activation, Body.Apart,
        Body.Outside, ← UInt64.toNat_toBitVec] at apart low usedBound bounds ⊢
      bv_omega
  · change Large.Mapped (Reservation.reservedState t address used flags).dmem t.regs.rdi.toBitVec 76
    rw [memory]
    exact reserve_mapped _ _ _ _ _ _ _ _ state.active.output
  · rw [memory]
    exact reserve_mapped _ _ _ _ _ _ _ _ state.active.stack

private theorem reserved_ready (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (activation : UsesActivation data) (state : Counted s t data)
    (large : (SszNative.Delimited.countWords data.size
      (Ssz.highestBit data[data.size-1]!)).high ≠ 0#64)
    (r : SszNative.Arena.Reservation)
    (reserved : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r)
    (flags : StatusFlags) :
    Ready s (Reservation.reservedState t address used flags) limit data address capacity used
      ⟨SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size-1]!),
        r.used, some r⟩ := by
  have prepared : SszNative.Delimited.prepare ⟨address.toNat, capacity.toNat, used.toNat⟩
      (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size-1]!)) =
      some ⟨SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size-1]!),
        r.used, some r⟩ := by
    simp only [SszNative.Delimited.prepare, large, ↓reduceIte, reserved]
  have physical : data.size < 2^64 := by rw [h.length]; exact s.regs.rcx.toBitVec.isLt
  have model := SszNative.Delimited.run_valid limit data
    ⟨address.toNat, capacity.toNat, used.toNat⟩ activation.1 activation.2
  rw [prepared] at model
  have allocation : SszNative.Delimited.allocation data
      ⟨address.toNat, capacity.toNat, used.toNat⟩ = some r := by
    have resources := (SszNative.Delimited.run_resources limit data
      ⟨address.toNat, capacity.toNat, used.toNat⟩ physical).1
    rw [model] at resources
    exact resources.symm
  have active := reserve_active s t limit data address capacity used ra h activation state r reserved flags
  have bounds := SszNative.Delimited.reservation_bounds _ _ _ h.arena_bound h.arena_nonzero r reserved
  obtain ⟨checks, rfl⟩ :=
    (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
  have memory : (Reservation.reservedState t address used flags).dmem =
      reserveMem t.dmem (s.regs.r8.toNat+16)
        (address.toNat + SszNative.Arena.start address.toNat used.toNat)
        (SszNative.Arena.start address.toNat used.toNat+16)
        t.regs.r14.toBitVec t.regs.rbp.toBitVec := by
    simp only [Reservation.reservedState, reserveMem, state.arenaAddress,
      BitVec.ofNat_add, ← UInt64.toNat_toBitVec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have fields := reserve_fields t.dmem (s.regs.r8.toNat+16)
    (address.toNat + SszNative.Arena.start address.toNat used.toNat)
    (SszNative.Arena.start address.toNat used.toNat+16)
    t.regs.r14.toBitVec t.regs.rbp.toBitVec
    (by have bound := h.header_bound; omega) bounds.2.2.2.2.2
    (by exact checks.2.2.2.2.1) (by
      have apart := h.arena_header
      have usedBound := h.used_bound
      unfold Body.Apart at *
      dsimp only at bounds
      omega)
  refine ⟨active, prepared, allocation, state.low, state.high, rfl, ?_, ?_, ?_⟩
  · change widthLoad _ _ 8 = _ ∧ widthLoad _ _ 8 = _
    rw [memory]
    exact ⟨fields.1.trans (congrArg some (congrArg BitVec.toNat state.low)),
      fields.2.1.trans (congrArg some (congrArg BitVec.toNat state.high))⟩
  · rw [memory]
    exact fields.2.2
  · intro a output stack outside
    obtain ⟨cursor, pointer⟩ := outside _ rfl
    rw [memory, reserve_frame _ _ _ _ _ _ a
      (by have bound := h.header_bound; omega) bounds.2.2.2.2.2 cursor pointer]
    exact state.frame a output stack (by intro r impossible; cases impossible)

private theorem reservation_active_same (s t u : MachineData) (data : Ssz.Bytes)
    (active : Active s t data) (frame : Reservation.Frame t u) (memory : u.dmem = t.dmem) :
    Active s u data := by
  have sp : u.regs.rsp = t.regs.rsp := UInt64.toBitVec_inj.1
    (frame.2 .rsp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have out : u.regs.rdi = t.regs.rdi := UInt64.toBitVec_inj.1
    (frame.2 .rdi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have source : u.regs.rdx = t.regs.rdx := UInt64.toBitVec_inj.1
    (frame.2 .rdx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have length : u.regs.rcx = t.regs.rcx := UInt64.toBitVec_inj.1
    (frame.2 .rcx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have preceding : u.regs.r13 = t.regs.r13 := UInt64.toBitVec_inj.1
    (frame.2 .r13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have highest : u.regs.rbx = t.regs.rbx := UInt64.toBitVec_inj.1
    (frame.2 .rbx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨?_, out.trans active.out, source.trans active.source, length.trans active.length,
    preceding.trans active.preceding, highest.trans active.highest, ?_,
    frame.1.trans active.simd, ?_, ?_⟩
  · rw [sp]; exact active.sp
  · rw [memory, sp]; exact active.saved
  · change Large.Mapped u.dmem u.regs.rdi.toBitVec 76
    rw [memory, out]; exact active.output
  · rw [memory]; exact active.stack

/-- Every concrete reservation guard is discharged by the checked allocator.
Success includes the committed cursor and both stored words before the Option
load. Failure reaches the real scratch continuation without any memory writes. -/
theorem reserve_phase_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (nonempty : 0 < data.size) (delimiter : data[data.size-1]! ≠ 0)
    (state : Counted s t data)
    (large : (SszNative.Delimited.countWords data.size
      (Ssz.highestBit data[data.size-1]!)).high ≠ 0#64)
    (P : MachineState → Prop)
    (success : ∀ u ready, Ready s u limit data address capacity used ready →
      u.regs.rsi = s.regs.rsi → u.regs.r8.toBitVec = BitVec.ofNat 64 ready.pointer →
      Eventually (step e) P (u, base+365))
    (failure : ∀ u, Active s u data → Frame s u.dmem data none →
      widthLoad u.dmem (s.regs.r8.toNat+16) 8 = some used.toNat →
      SszNative.Delimited.prepare ⟨address.toNat, capacity.toNat, used.toNat⟩
        (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size-1]!)) = none →
      SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩ =
        ⟨.error .scratchExhausted, used.toNat, none⟩ →
      Eventually (step e) P (u, base+736)) :
    Eventually (step e) P (t, base+269) := by
  have activation : UsesActivation data := ⟨nonempty, delimiter⟩
  have header := counted_header s t limit data address capacity used ra h state
  apply eventually_trans (step e) (Reservation.Post t base address capacity used) P _
    (Reservation.runs e base hc t address capacity used header
      (counted_mapped s t limit data address capacity used ra h activation state
        address capacity.toNat h.arena_mapped))
  rintro ⟨u, pc⟩ ⟨frame, outcome⟩
  rcases outcome with ⟨failed, rfl, memory⟩ | ⟨r, reserved, rfl, flags, rfl⟩
  · have prepared := (SszNative.Delimited.prepare_none_iff
      ⟨address.toNat, capacity.toNat, used.toNat⟩
      (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size-1]!))).2
      ⟨large, failed⟩
    apply failure u (reservation_active_same s t u data state.active frame memory)
    · rw [memory]; exact state.frame
    · rw [memory]
      simp only [widthLoad, ← UInt64.toNat_toBitVec, width_address,
        ← state.arenaAddress, header.used_load, Option.map_some, Int.toNat_natCast]
    · exact prepared
    · rw [SszNative.Delimited.run_valid limit data _ nonempty delimiter, prepared]
  · apply success _ _
      (reserved_ready s t limit data address capacity used ra h activation state large r reserved flags)
    · exact state.optionAddress
    · obtain ⟨checks, rfl⟩ :=
        (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
      rfl

/-- The reservation failure branch is composed through its real error stores,
callee-save restoration, and RET; only successful preparation continues. -/
theorem reserve_return_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (nonempty : 0 < data.size) (delimiter : data[data.size-1]! ≠ 0)
    (state : Counted s t data)
    (large : (SszNative.Delimited.countWords data.size
      (Ssz.highestBit data[data.size-1]!)).high ≠ 0#64)
    (P : MachineState → Prop)
    (success : ∀ u ready, Ready s u limit data address capacity used ready →
      u.regs.rsi = s.regs.rsi → u.regs.r8.toBitVec = BitVec.ofNat 64 ready.pointer →
      Eventually (step e) P (u, base+365))
    (hp : ∀ u, Post s limit data address capacity used ra u → P u) :
    Eventually (step e) P (t, base+269) := by
  apply reserve_phase_cps e base hc s t limit data address capacity used ra h
    nonempty delimiter state large P success
  intro u active frame cursor _ model
  exact scratch_phase_cps e base hc s u limit data address capacity used ra h
    nonempty delimiter active frame cursor model P hp

end SszX86.Delimited
