import SszX86.NatMulMemoryInitializedGeometry
import SszX86.NatMulMemoryActivation
import SszX86.NatMulMemoryCompose
import SszX86.NatMulMemoryZero
import SszX86.NatMulReserveCursor
import SszX86.NatMulReserveGeometry

namespace SszX86.NatMul
open SszNative
open UintCodec

structure Initialized (original current : MachineData) (left right : NatOperand)
    (address capacity used : BitVec 64) (r : Arena.Reservation) (t : MachineState) : Prop where
  stack : t.1.regs.rsp = current.regs.rsp
  destination : t.1.regs.rbx.toBitVec = BitVec.ofNat 64 r.pointer
  work : WorkFrame original t.1.dmem
    (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat)
  left_at : left.At (widthLoad t.1.dmem)
  right_at : right.At (widthLoad t.1.dmem)
  output_mapped : Large.Mapped t.1.dmem original.regs.rdi.toBitVec 72
  cursor : widthLoad t.1.dmem (original.regs.r9.toNat+16) 8 =
    some (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).used
  zero_words : NatMemory.wordsAt (widthLoad t.1.dmem) r.pointer
    (List.replicate (Reservation.total current) 0)
  destination_mapped : Large.Mapped t.1.dmem (BitVec.ofNat 64 r.pointer) (8*Reservation.total current)
  locals_mapped : Large.Mapped t.1.dmem current.regs.rsp.toBitVec 40
  slot0 : Mem.loadInt t.1.dmem current.regs.rsp.toBitVec 8 = some (current.regs.rax.toNat : Int)
  slot16 : Mem.loadInt t.1.dmem (current.regs.rsp.toBitVec+16#64) 8 = some (current.regs.rsi.toNat : Int)
  slot24 : Mem.loadInt t.1.dmem (current.regs.rsp.toBitVec+24#64) 8 = some (current.regs.rdi.toNat : Int)
  slot32 : Mem.loadInt t.1.dmem (current.regs.rsp.toBitVec+32#64) 8 = some (current.regs.rcx.toNat : Int)

private theorem helper_mapped (s : MachineData) (ra : BitVec 64) (n : Nat) (t : MachineState)
    (post : MemsetCall.Post s ra n t) (p : BitVec 64) (count : Nat)
    (hm : Large.Mapped s.dmem p count)
    (buffer : Large.Disjoint p s.regs.rdi.toBitVec count n)
    (slot : Large.Disjoint p (s.regs.rsp.toBitVec-8#64) count 8) :
    Large.Mapped t.1.dmem p count := by
  intro i hi
  obtain ⟨byte, old⟩ := hm i hi
  refine ⟨byte, ?_⟩
  rw [post.frame]
  · exact old
  · rintro (⟨j, hj, equal⟩ | ⟨j, hj, equal⟩)
    · exact buffer i hi j hj equal
    · exact slot i hi j hj equal

private theorem outside_local_span (original current : MachineData)
    (low : 96 ≤ original.regs.rsp.toNat)
    (stack : current.regs.rsp.toBitVec = original.regs.rsp.toBitVec-88)
    (a : BitVec 64) (outside : Body.Outside a.toNat (original.regs.rsp.toNat-96) 48)
    (off count : Nat) (inside : off+count ≤ 40) :
    ¬ Emit.InSpan a (current.regs.rsp.toBitVec + BitVec.ofNat 64 off) count := by
  rintro ⟨i, hi, equal⟩
  rw [stack] at equal
  change 96 ≤ original.regs.rsp.toBitVec.toNat at low
  change Body.Outside a.toNat (original.regs.rsp.toBitVec.toNat-96) 48 at outside
  unfold Body.Outside at outside
  bv_omega

theorem initialized_work (original current : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned original left right address capacity used ra)
    (memory : current.dmem = pushedMem original)
    (stack : current.regs.rsp.toBitVec = original.regs.rsp.toBitVec-88)
    (arena : current.regs.r9 = original.regs.r9)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = some r)
    (length : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length =
      Reservation.total current)
    (guardFlags fillFlags : StatusFlags) (helperRA : BitVec 64) (t : MachineState)
    (post : MemsetCall.Post (Reservation.initializedState current address used guardFlags fillFlags)
      helperRA (8*Reservation.total current) t) :
    WorkFrame original t.1.dmem
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat) := by
  have frame := Reservation.initialized_frame current address used guardFlags fillFlags helperRA t post
  have geometry := SszNative.NatMul.allocation_geometry left right address.toNat capacity.toNat used.toNat r allocated
  have pointer : address + BitVec.ofNat 64 (Arena.start address.toNat used.toNat) = BitVec.ofNat 64 r.pointer := by
    simp only [geometry.2.1, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have pointerNat := allocated_pointer_nat original left right address capacity used ra owned r allocated
  have bounds := allocation_bounds original left right address capacity used ra owned r allocated
  intro a _ activation scratch
  rw [← memory]
  apply frame
  rintro (written | buffer | callslot)
  · rcases written with outslot | cursor | leftslot | rightslot | firstslot
    · exact outside_local_span original current owned.stack_low stack a activation 24 8 (by decide) outslot
    · obtain ⟨i, hi, equal⟩ := cursor
      rw [arena] at equal
      have outside := (scratch r allocated).1
      have bound := owned.header_bound
      change original.regs.r9.toBitVec.toNat+24 ≤ 2^64 at bound
      change Body.Outside a.toNat (original.regs.r9.toBitVec.toNat+16) 8 at outside
      unfold Body.Outside at outside
      bv_omega
    · exact outside_local_span original current owned.stack_low stack a activation 16 8 (by decide) leftslot
    · exact outside_local_span original current owned.stack_low stack a activation 32 8 (by decide) rightslot
    · apply outside_local_span original current owned.stack_low stack a activation 0 8 (by decide)
      simpa only [BitVec.add_zero] using firstslot
  · obtain ⟨i, hi, equal⟩ := buffer
    rw [pointer] at equal
    have outside := (scratch r allocated).2
    have bound := bounds.2.2.2.2.2
    rw [length] at outside bound
    apply Body.outside_byte (BitVec.ofNat 64 r.pointer) a (8*Reservation.total current) i
      (by simpa only [pointerNat] using bound) (by simpa only [pointerNat] using outside) hi equal
  · obtain ⟨i, hi, equal⟩ := callslot
    rw [stack] at equal
    have low := owned.stack_low
    change 96 ≤ original.regs.rsp.toBitVec.toNat at low
    change Body.Outside a.toNat (original.regs.rsp.toBitVec.toNat-96) 48 at activation
    unfold Body.Outside at activation
    bv_omega

/-- All initialization resources are consequences of the actual five stores,
CALL, memset execution and helper RET, plus original physical ownership. -/
theorem initialized_memory (original current : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned original left right address capacity used ra)
    (memory : current.dmem = pushedMem original)
    (stack : current.regs.rsp.toBitVec = original.regs.rsp.toBitVec-88)
    (arena : current.regs.r9 = original.regs.r9)
    (counts : Reservation.total current = left.wordCount+right.wordCount)
    (r : Arena.Reservation)
    (model : SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r (SszNative.NatMul.writtenWords left right))
    (base : Int64) (guardFlags fillFlags : StatusFlags) (t : MachineState)
    (post : MemsetCall.Post (Reservation.initializedState current address used guardFlags fillFlags)
      (base+493).toBitVec (8*Reservation.total current) t) :
    Initialized original current left right address capacity used r t := by
  have allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = some r := by
    rw [model]
    rfl
  have length : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length =
      Reservation.total current := by
    rw [model]
    change (SszNative.NatMul.writtenWords left right).length = Reservation.total current
    rw [SszNative.NatMul.writtenWords_length, counts]
  obtain ⟨_, positive, reserved⟩ := SszNative.NatMul.allocation_exact left right address.toNat capacity.toNat used.toNat r allocated
  rw [length] at positive reserved
  have checks := ((Arena.reserve_eq_some_iff_checks _ _ _ _ positive r).mp reserved).1
  have countBound : Reservation.total current < 2^64 := by have := checks.1; omega
  have bounds := allocation_bounds original left right address capacity used ra owned r allocated
  have pointerNat := allocated_pointer_nat original left right address capacity used ra owned r allocated
  have usedNat : (BitVec.ofNat 64 r.used).toNat = r.used := Nat.mod_eq_of_lt (by
    have fit := bounds.2.2.2.2.1
    have capacityBound := capacity.isLt
    omega)
  have separation := initialization_separation original current left right address capacity used ra owned stack r allocated
    (8*Reservation.total current) (by rw [length])
  have destination := Reservation.initialized_pointer current address capacity used positive r reserved guardFlags fillFlags
  have work := initialized_work original current left right address capacity used ra owned memory stack arena r allocated length
    guardFlags fillFlags (base+493).toBitVec t post
  have frame := work.to_frame owned.stack_low
  have initialOutput : Large.Mapped
      (Reservation.allocatedState current address used guardFlags).dmem original.regs.rdi.toBitVec 72 := by
    simpa only [Reservation.allocatedState, Reservation.reservedState, Reservation.countState, memory] using
      pushed_mapped original _ _ owned.output_mapped
  have initialLocals : Large.Mapped
      (Reservation.allocatedState current address used guardFlags).dmem current.regs.rsp.toBitVec 40 := by
    have hm := owned.stack_subrange 8 40 (by decide)
    have pointer : (original.regs.rsp.toBitVec-96)+BitVec.ofNat 64 8 = current.regs.rsp.toBitVec := by
      rw [stack]
      bv_omega
    simpa only [Reservation.allocatedState, Reservation.reservedState, Reservation.countState, memory, pointer] using hm
  have localCursor : Large.Disjoint
      (Reservation.allocatedState current address used guardFlags).regs.rsp.toBitVec
      ((Reservation.allocatedState current address used guardFlags).regs.r9.toBitVec+16#64) 40 8 := by
    simpa only [Reservation.allocatedState, Reservation.reservedState, Reservation.countState, arena] using separation.stack_cursor
  have spills := Reservation.prepared_spills (Reservation.allocatedState current address used guardFlags) localCursor
  have loads (off : Nat) (inside : off+8 ≤ 40) :
      Mem.loadInt t.1.dmem (current.regs.rsp.toBitVec+BitVec.ofNat 64 off) 8 =
        Mem.loadInt (Reservation.preparedMem (Reservation.allocatedState current address used guardFlags))
          (current.regs.rsp.toBitVec+BitVec.ofNat 64 off) 8 := by
    have loaded := Reservation.helper_stack_load _ _ _ t post off inside (by
      rw [destination]
      exact separation.stack_buffer)
    simpa only [Reservation.initializedState, Reservation.preparedState, Reservation.allocatedState,
      Reservation.reservedState, Reservation.countState] using loaded
  have cursorBefore := Reservation.prepared_cursor (Reservation.allocatedState current address used guardFlags) localCursor
  have ending := Reservation.initialized_end current address capacity used positive countBound r reserved guardFlags
  have endNat : (Reservation.allocatedState current address used guardFlags).regs.r11.toNat = r.used := by
    change (Reservation.allocatedState current address used guardFlags).regs.r11.toBitVec.toNat = r.used
    rw [ending]
    exact usedNat
  rw [endNat] at cursorBefore
  have cursorLoad : Mem.loadInt t.1.dmem (original.regs.r9.toBitVec+16#64) 8 = some (r.used : Int) := by
    rw [Reservation.helper_cursor_load _ _ _ t post (original.regs.r9.toBitVec+16#64)
      (by rw [destination]; exact separation.cursor_buffer)
      (by exact separation.cursor_call)]
    simpa only [Reservation.initializedState, Reservation.preparedState, Reservation.allocatedState,
      Reservation.reservedState, Reservation.countState, arena] using cursorBefore
  have bytes := post.output
  rw [destination] at bytes
  obtain ⟨_, returnedStack, _, _, _, _, _, _, _, _, returnedDestination, _⟩ :=
    Reservation.initialized_registers current base address used guardFlags fillFlags t post
  have pointer : address+BitVec.ofNat 64 (Arena.start address.toNat used.toNat) = BitVec.ofNat 64 r.pointer := by
    have geometry := SszNative.NatMul.allocation_geometry left right address.toNat capacity.toNat used.toNat r allocated
    simp only [geometry.2.1, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨returnedStack, returnedDestination.trans pointer, work,
    operand_preserved original left right left address capacity used ra owned _ frame owned.left_at owned.left_owned,
    operand_preserved original left right right address capacity used ra owned _ frame owned.right_at owned.right_owned,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply helper_mapped _ _ _ t post original.regs.rdi.toBitVec 72
    · exact Reservation.prepared_mapped _ _ _ initialOutput
    · rw [destination]
      exact separation.output_buffer
    · exact separation.output_call
  · rw [allocation_cursor left right address capacity used r allocated]
    change widthLoad t.1.dmem (original.regs.r9.toBitVec.toNat+16) 8 = some r.used
    simp only [widthLoad, width_address, cursorLoad, Option.map_some, Int.toNat_natCast]
  · simpa only [pointerNat] using memset_zero_words t.1.dmem (BitVec.ofNat 64 r.pointer) (Reservation.total current) bytes
  · intro i hi
    refine ⟨0, ?_⟩
    simpa [hi] using bytes i (by simpa only [List.length_replicate] using hi)
  · apply helper_mapped _ _ _ t post current.regs.rsp.toBitVec 40
    · exact Reservation.prepared_mapped _ _ _ initialLocals
    · rw [destination]
      exact separation.stack_buffer
    · exact separation.stack_call
  · have first := loads 0 (by decide)
    simp only [BitVec.add_zero] at first
    exact first.trans spills.1
  · exact (loads 16 (by decide)).trans spills.2.1
  · exact (loads 24 (by decide)).trans spills.2.2.1
  · exact (loads 32 (by decide)).trans spills.2.2.2

end SszX86.NatMul
