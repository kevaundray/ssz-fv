import SszX86.BitVectorFinishSuccess
import SszX86.BitVectorFinishNarrowMemory
import SszX86.BitVectorConstruct

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem finish_to_u128_owned (s u : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used ra : BitVec 64)
    (owned : Owned {s with dmem := u.dmem} saved length data address capacity used)
    (stack : u.regs.rsp = s.regs.rsp)
    (pointer : u.regs.r15.toBitVec = length.pointer)
    (payload : u.regs.r12.toBitVec = length.payload) :
    NatToU128.Owned (callState (toU128SetupState u) ra) length ra := by
  let c := callState (toU128SetupState u) ra
  have low : 72 ≤ s.regs.rsp.toNat := owned.stack_low
  have high : s.regs.rsp.toNat + 368 ≤ 2^64 := owned.stack_bound
  have pushed : RegionsFrame u.dmem c.dmem [(s.regs.rsp.toNat - 8, 8)] := by
    have location : (s.regs.rsp.toBitVec - 8#64).toNat = s.regs.rsp.toNat - 8 := by
      change (s.regs.rsp.toBitVec - 8#64).toNat = s.regs.rsp.toBitVec.toNat - 8
      have bound : 72 ≤ s.regs.rsp.toBitVec.toNat := low
      bv_omega
    have frame := store_regions_frame u.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toInt
      (by rw [location]; omega)
    simpa only [c, callState, NatDivision.callState, toU128SetupState, stack,
      show (8 : BitVec 64) = 8#64 by decide, location] using frame
  have operand : length.At (widthLoad c.dmem) := by
    apply pushed.operand length owned.descriptor.2.2
    intro p words equal span member
    subst length
    have apart := owned.operand_owned.work
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst span
    simp only [Body.Apart, workStart, workSize] at apart ⊢
    omega
  apply to_u128_owned {s with dmem := u.dmem} c saved length data address capacity used ra owned
  · simp only [c, NatDivision.callState, toU128SetupState,
      UInt64.toBitVec_ofBitVec, stack]
  · simp only [c, NatDivision.callState, toU128SetupState,
      UInt64.toBitVec_ofBitVec, stack, show (8 : BitVec 64) = 8#64 by decide]
  · exact pointer
  · exact payload
  · change Large.Mapped (Mem.storeInt u.dmem (u.regs.rsp.toBitVec - 8#64) 8 ra.toInt)
      (s.regs.rsp.toBitVec - 72#64) workSize
    exact Large.mapped_store _ _ _ _ _ _ owned.work_mapped
  · exact operand
  · exact NatDivision.call_slot_load _ _ ra

/-- Real linked conversion, inlined option/rounding guard, borrowed success and RET.
Scope arithmetic, rather than future native branch assumptions, rules out both guards. -/
theorem finish_borrow_cps (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s u : MachineData) (saved : Saved) (length expected : NatOperand)
    (remainder address capacity used : BitVec 64) (data : Ssz.Bytes)
    (owned : Owned {s with dmem := u.dmem} saved length data address capacity used)
    (original : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (stack : u.regs.rsp = s.regs.rsp) (sizeReg : u.regs.r14 = s.regs.r14)
    (pointer : u.regs.r15.toBitVec = length.pointer)
    (payload : u.regs.r12.toBitVec = length.payload)
    (outputCache : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 8#64) 8 =
      some (s.regs.rdi.toNat : Int))
    (sourceCache : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 104#64) 8 =
      some (s.regs.rdx.toNat : Int))
    (arithmetic : SszNative.BitVector.Expected length expected remainder)
    (checked : NatNarrow.runExact expected (BitVec.ofNat 64 data.size) = true) :
    Eventually (step e)
      (Terminal s saved u.dmem data (.ok (BitVec.ofNat 128 length.value))) (u, base + 5233) := by
  let count := BitVec.ofNat 128 length.value
  obtain ⟨bound, narrow, scope⟩ := SszNative.BitVector.scope_narrows length expected remainder
    (BitVec.ofNat 64 data.size) arithmetic checked
  have dataBound : data.size < 2^64 := by
    rw [owned.data_length]
    exact s.regs.r14.toBitVec.isLt
  have scopeCount : data.size = (count.toNat + 7) / 8 := by
    simpa only [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt dataBound] using scope
  have countBound : count.toNat < 2^67 := by
    change length.value % 2^128 < 2^67
    rw [Nat.mod_eq_of_lt (by omega)]
    exact bound
  have low : 72 ≤ s.regs.rsp.toNat := owned.stack_low
  have high : s.regs.rsp.toNat + 368 ≤ 2^64 := owned.stack_bound
  have callSlot : CallSlot (toU128SetupState u) := by
    have read := Large.mapped_load u.dmem (s.regs.rsp.toBitVec - 72#64) workSize 64 8
      owned.work_mapped (by decide)
    simpa only [CallSlot, toU128SetupState, stack,
      show s.regs.rsp.toBitVec - 72#64 + BitVec.ofNat 64 64 = s.regs.rsp.toBitVec - 8#64
        by bv_omega] using read
  apply to_u128_setup_cps e base hc.body u
  apply to_u128_cps e base hc (toU128SetupState u) length callSlot
    (finish_to_u128_owned s u saved length data address capacity used _ owned stack pointer payload)
  intro t post
  have sp : t.1.regs.rsp = s.regs.rsp := by
    apply UInt64.toBitVec_inj.mp
    have equal := post.returned.sp
    simp only [callState, NatDivision.callState, toU128SetupState,
      UInt64.toBitVec_ofBitVec, stack] at equal
    bv_omega
  have returnedSize : t.1.regs.r14 = s.regs.r14 := post.returned.r14.trans sizeReg
  have pc : t.2 = base + 5249 := by simpa only [Int64.ofBitVec_toBitVec] using post.returned.pc
  have frame := finish_narrow_frame s u length (base + 5249).toBitVec stack low high t post
  have coarse := finish_narrow_cover s u.dmem t.1.dmem low frame
  have savedAfter := finish_saved s saved u.dmem t.1.dmem low high owned.output_saved
    owned.saved_at coarse
  have outRead : Mem.loadInt t.1.dmem (s.regs.rsp.toBitVec + 8#64) 8 =
      some (s.regs.rdi.toNat : Int) := by
    rw [finish_narrow_cache s u.dmem t.1.dmem 8 (Or.inl rfl) high frame]
    exact outputCache
  have sourceRead : Mem.loadInt t.1.dmem (s.regs.rsp.toBitVec + 104#64) 8 =
      some (s.regs.rdx.toNat : Int) := by
    rw [finish_narrow_cache s u.dmem t.1.dmem 104 (Or.inr rfl) high frame]
    exact sourceCache
  have source : SszNative.ByteView.BytesAt (widthLoad t.1.dmem) s.regs.rdx.toNat data := by
    apply coarse.bytes s.regs.rdx.toNat data owned.source_owned.bound owned.source
    intro span member
    simp only [finishRegions, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact owned.source_owned.output
    · exact owned.source_owned.work
  have mappedOutput : Large.Mapped t.1.dmem s.regs.rdi.toBitVec 80 := by
    rw [post.memory, narrow]
    unfold NatToU128.resultMem NatToU128.someMem callState NatDivision.callState toU128SetupState
    repeat' apply Large.mapped_store
    exact owned.output_mapped
  have memory : t.1.dmem = NatToU128.someMem
      (callState (toU128SetupState u) (base + 5249).toBitVec).dmem
      (s.regs.rsp.toBitVec + 16#64) count := by
    simpa only [narrow, NatToU128.resultMem, toU128SetupState, callState,
      NatDivision.callState, UInt64.toBitVec_ofBitVec, stack] using post.memory
  have tag : Mem.loadInt t.1.dmem (t.1.regs.rsp.toBitVec + 16#64) 1 = some 1 := by
    rw [sp, memory]
    exact finish_some_tag _ _ count
  have outNat : (callState (toU128SetupState u) (base + 5249).toBitVec).regs.rdi.toNat =
      s.regs.rsp.toNat + 16 := by
    change (u.regs.rsp.toBitVec + 16#64).toNat = s.regs.rsp.toBitVec.toNat + 16
    rw [stack]
    have highBV : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 := high
    bv_omega
  have observed := post.observed
  rw [narrow, outNat] at observed
  have lowRead := widthLoad_eq t.1.dmem (s.regs.rsp.toNat + 16 + 16) 8
    (constructLow count).toNat observed.2.2.1
  have highRead := widthLoad_eq t.1.dmem (s.regs.rsp.toNat + 16 + 24) 8
    (constructHigh count).toNat observed.2.2.2
  change Eventually (step e) _ (t.1, t.2)
  rw [pc]
  apply construct_cps e base hc.body t.1 count s.regs.rdi.toBitVec countBound
  · simpa only [UInt64.toNat_toBitVec, returnedSize, ← owned.data_length] using scopeCount
  · exact tag
  · simpa only [sp, Nat.add_assoc, Nat.reduceAdd, ← UInt64.toNat_toBitVec, width_address] using lowRead
  · simpa only [sp, Nat.add_assoc, Nat.reduceAdd, ← UInt64.toNat_toBitVec, width_address] using highRead
  · simpa only [sp, UInt64.toNat_toBitVec] using outRead
  intro flags
  let v := constructReady t.1 count s.regs.rdi.toBitVec flags
  have success := finish_success_cps e base hc.body s v saved data count original sp rfl
    (by simpa only [v, constructReady, returnedSize] using owned.data_length.symm) rfl rfl scopeCount
    mappedOutput owned.output_bound low high owned.output_work owned.output_saved savedAfter
    source owned.source_owned.bound owned.source_owned.output sourceRead
  apply eventually_trans (step e) (Terminal s saved t.1.dmem data (.ok count)) _ _ success
  intro z terminal
  exact Eventually.done _ ⟨terminal.observed, terminal.returned,
    finish_frame_trans coarse terminal.frame⟩

end SszX86.BitVector
