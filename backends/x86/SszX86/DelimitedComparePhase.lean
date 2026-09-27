import SszX86.DelimitedCompareMemory

namespace SszX86.Delimited
open UintCodec

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- The Some-capacity edge performs the actual argument spills, linked CALL,
read-only Nat.compare, restoring loads, and signed low-byte Ordering branch. -/
theorem compare_phase_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hcompare : NatCompare.CodeAt e (base + Int64.ofInt compareOffset))
    (s t : MachineData) (cap : Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s (some cap) data address capacity used ra)
    (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0)
    (ready : SszNative.Delimited.Prepared) (state : Ready s t (some cap) data address capacity used ready)
    (optionAddress : t.regs.rsi = s.regs.rsi)
    (pointer : t.regs.r8.toBitVec = BitVec.ofNat 64 ready.pointer)
    (P : MachineState → Prop)
    (hp : ∀ (u : MachineData) (capPointer capPayload : BitVec 64),
      Ready s u (some cap) data address capacity used ready →
      u.regs.rsi.toBitVec = BitVec.ofNat 64 ready.pointer →
      Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 8#64) 8 = some (capPointer.toNat : Int) →
      Mem.loadInt u.dmem u.regs.rsp.toBitVec 8 = some (capPayload.toNat : Int) →
      widthLoad s.dmem (s.regs.rsi.toNat + 8) 8 = some capPointer.toNat →
      widthLoad s.dmem (s.regs.rsi.toNat + 16) 8 = some capPayload.toNat →
      Eventually (step e) P
        (u, if compare ready.count.value cap = .gt then base + 454 else base + 523)) :
    Eventually (step e) P (t, base + 374) := by
  have active : UsesActivation data := ⟨nonempty, delimiter⟩
  obtain ⟨capPointer, capPayload, originalPointer, originalPayload⟩ := option_header_words s cap h.option_at
  have prefixFrame : Frame s t.dmem data
      (SszNative.Delimited.allocation data ⟨address.toNat, capacity.toNat, used.toNat⟩) := by
    simpa only [state.allocation] using state.frame
  have pointerObserved : widthLoad t.dmem (s.regs.rsi.toNat + 8) 8 = some capPointer.toNat :=
    (preserves_load s (some cap) data address capacity used ra h t.dmem prefixFrame
      s.regs.rsi.toNat 24 8 8 h.option_owned (by decide)).trans originalPointer
  have payloadObserved : widthLoad t.dmem (s.regs.rsi.toNat + 16) 8 = some capPayload.toNat :=
    (preserves_load s (some cap) data address capacity used ra h t.dmem prefixFrame
      s.regs.rsi.toNat 24 16 8 h.option_owned (by decide)).trans originalPayload
  have pointerRead : Mem.loadInt t.dmem (t.regs.rsi.toBitVec + 8#64) 8 = some (capPointer.toNat : Int) := by
    simpa only [optionAddress, ← UInt64.toNat_toBitVec, width_address] using
      widthLoad_eq t.dmem (s.regs.rsi.toNat + 8) 8 capPointer.toNat pointerObserved
  have payloadRead : Mem.loadInt t.dmem (t.regs.rsi.toBitVec + 16#64) 8 = some (capPayload.toNat : Int) := by
    simpa only [optionAddress, ← UInt64.toNat_toBitVec, width_address] using
      widthLoad_eq t.dmem (s.regs.rsi.toNat + 16) 8 capPayload.toNat payloadObserved
  have locals : Large.Mapped t.dmem t.regs.rsp.toBitVec 40 := by
    intro i hi
    have location : t.regs.rsp.toBitVec + BitVec.ofNat 64 i =
        (s.regs.rsp.toBitVec - 104) + BitVec.ofNat 64 (16+i) := by
      rw [state.active.sp]
      bv_omega
    rw [location]
    exact state.active.stack (16+i) (by omega)
  let arguments := compareState t capPointer capPayload
  let called := callState arguments base
  have written : ∀ a : BitVec 64,
      (∀ i < 56, a ≠ (t.regs.rsp.toBitVec - 16#64) + BitVec.ofNat 64 i) →
        called.dmem.get? a = t.dmem.get? a := compare_call_frame t capPointer capPayload base
  have resources := state.work_resources h active called.dmem written
  have callFrame : Frame s called.dmem data
      (SszNative.Delimited.allocation data ⟨address.toNat, capacity.toNat, used.toNat⟩) := by
    simpa only [state.allocation] using resources.1
  have storedPair : SszNative.NatMemory.Pair (widthLoad called.dmem)
      t.regs.r8.toBitVec t.regs.r15.toBitVec ready.count.value := by
    rw [pointer, state.payload]
    exact SszNative.Delimited.PreparedAt.pair (widthLoad called.dmem)
      ⟨address.toNat, capacity.toNat, used.toNat⟩ _ ready state.prepared resources.2.1
      h.arena_bound h.arena_nonzero
  have capOption := option_preserved s (some cap) data address capacity used ra h called.dmem callFrame
  have callPointer : widthLoad called.dmem (s.regs.rsi.toNat + 8) 8 = some capPointer.toNat :=
    (preserves_load s (some cap) data address capacity used ra h called.dmem callFrame
      s.regs.rsi.toNat 24 8 8 h.option_owned (by decide)).trans originalPointer
  have callPayload : widthLoad called.dmem (s.regs.rsi.toNat + 16) 8 = some capPayload.toNat :=
    (preserves_load s (some cap) data address capacity used ra h called.dmem callFrame
      s.regs.rsi.toNat 24 16 8 h.option_owned (by decide)).trans originalPayload
  have capPair : SszNative.NatMemory.Pair (widthLoad called.dmem) capPointer capPayload cap := by
    apply SszNative.NatMemory.pair_of_at _ capPointer capPayload cap _ capOption.2 callPointer
    simpa only [Nat.add_assoc, Nat.reduceAdd] using callPayload
  have mappedArguments : Large.Mapped arguments.dmem (s.regs.rsp.toBitVec - 104) 104 :=
    compare_mapped t capPointer capPayload _ 104 state.active.stack
  have returnWritable : ∃ old, Mem.loadInt arguments.dmem (arguments.regs.rsp.toBitVec - 8) 8 = some old := by
    have location : arguments.regs.rsp.toBitVec - 8 = s.regs.rsp.toBitVec - 96#64 := by
      change t.regs.rsp.toBitVec - 8 = _
      rw [state.active.sp]
      bv_omega
    rw [location]
    exact activation_load arguments.dmem s.regs.rsp.toBitVec 96 mappedArguments (by decide) (by decide)
  have callStack : Large.Mapped called.dmem (s.regs.rsp.toBitVec - 104) 104 :=
    call_mapped arguments base _ 104 mappedArguments
  have callOutput : Large.Mapped called.dmem t.regs.rdi.toBitVec 76 :=
    call_mapped arguments base _ 76 (compare_mapped t capPointer capPayload _ 76 state.active.output)
  have savedCall : SavedAt called.dmem t.regs.rsp.toBitVec s :=
    savedAt_work t.dmem called.dmem t.regs.rsp.toBitVec s written state.active.saved
  have spills := compare_call_spills t capPointer capPayload base
  apply compare_arguments_cps e base hc t capPointer capPayload pointerRead payloadRead locals
  change Eventually (step e) P (arguments, base + 424)
  apply compare_runs e base hc hcompare arguments ready.count.value cap P returnWritable storedPair capPair
  rintro ⟨v, pc⟩ returned
  obtain ⟨pcReturned, ordering, memory, vectors, stackReturned, registers⟩ := returned
  have atReturn : pc = base + 429 := by simpa only [Int64.ofBitVec_toBitVec] using pcReturned
  subst pc
  have stackV : v.regs.rsp.toBitVec = t.regs.rsp.toBitVec := by
    simpa only [arguments, callState, compareState, UInt64.toBitVec_ofBitVec,
      BitVec.sub_add_cancel] using stackReturned
  have rbx : v.regs.rbx = t.regs.rbx := UInt64.toBitVec_inj.1
    (registers .rbx (by decide) (by decide) (by decide) (by decide) (by decide))
  have rbp : v.regs.rbp = t.regs.rbp := UInt64.toBitVec_inj.1
    (registers .rbp (by decide) (by decide) (by decide) (by decide) (by decide))
  have r12 : v.regs.r12 = t.regs.rcx := UInt64.toBitVec_inj.1
    (registers .r12 (by decide) (by decide) (by decide) (by decide) (by decide))
  have r13 : v.regs.r13 = t.regs.r13 := UInt64.toBitVec_inj.1
    (registers .r13 (by decide) (by decide) (by decide) (by decide) (by decide))
  have r14 : v.regs.r14 = t.regs.r8 := UInt64.toBitVec_inj.1
    (registers .r14 (by decide) (by decide) (by decide) (by decide) (by decide))
  have r15 : v.regs.r15 = t.regs.r15 := UInt64.toBitVec_inj.1
    (registers .r15 (by decide) (by decide) (by decide) (by decide) (by decide))
  have sourceSpill : Mem.loadInt v.dmem (v.regs.rsp.toBitVec + 16#64) 8 = some (t.regs.rdx.toBitVec.toNat : Int) := by
    rw [memory, stackV]
    exact spills.2.2.1
  have outputSpill : Mem.loadInt v.dmem (v.regs.rsp.toBitVec + 24#64) 8 = some (t.regs.rdi.toBitVec.toNat : Int) := by
    rw [memory, stackV]
    exact spills.2.2.2.1
  have lowSpill : Mem.loadInt v.dmem (v.regs.rsp.toBitVec + 32#64) 8 = some (t.regs.r14.toBitVec.toNat : Int) := by
    rw [memory, stackV]
    exact spills.2.2.2.2
  let restored := afterCompareState v t.regs.rdx.toBitVec t.regs.rdi.toBitVec t.regs.r14.toBitVec
  have live : Active s restored data := by
    refine ⟨stackV.trans state.active.sp, ?_, ?_, r12.trans state.active.length,
      r13.trans state.active.preceding, rbx.trans state.active.highest, ?_,
      vectors.trans state.active.simd, ?_, ?_⟩
    · exact (UInt64.ofBitVec_toBitVec _).trans state.active.out
    · exact (UInt64.ofBitVec_toBitVec _).trans state.active.source
    · change SavedAt v.dmem v.regs.rsp.toBitVec s
      rw [memory, stackV]
      exact savedCall
    · change Large.Mapped v.dmem t.regs.rdi.toBitVec 76
      rw [memory]
      exact callOutput
    · change Large.Mapped v.dmem (s.regs.rsp.toBitVec - 104) 104
      rw [memory]
      exact callStack
  have readyAfter : Ready s restored (some cap) data address capacity used ready := by
    refine ⟨live, state.prepared, state.allocation, state.low, ?_, ?_, ?_, ?_, ?_⟩
    · change v.regs.rbp.toBitVec = ready.count.high
      rw [rbp]
      exact state.high
    · change v.regs.r15.toBitVec = BitVec.ofNat 64 ready.payload
      rw [r15]
      exact state.payload
    · change SszNative.Delimited.PreparedAt (widthLoad v.dmem) ready
      rw [memory]
      exact resources.2.1
    · change widthLoad v.dmem (s.regs.r8.toNat + 16) 8 = some ready.used
      rw [memory]
      exact resources.2.2
    · change Frame s v.dmem data ready.allocation
      rw [memory]
      exact resources.1
  have actualPointer : restored.regs.rsi.toBitVec = BitVec.ofNat 64 ready.pointer := by
    change v.regs.r14.toBitVec = _
    rw [r14]
    exact pointer
  have expectedPointer : Mem.loadInt restored.dmem (restored.regs.rsp.toBitVec + 8#64) 8 =
      some (capPointer.toNat : Int) := by
    change Mem.loadInt v.dmem (v.regs.rsp.toBitVec + 8#64) 8 = _
    rw [memory, stackV]
    exact spills.2.1
  have expectedPayload : Mem.loadInt restored.dmem restored.regs.rsp.toBitVec 8 =
      some (capPayload.toNat : Int) := by
    change Mem.loadInt v.dmem v.regs.rsp.toBitVec 8 = _
    rw [memory, stackV]
    exact spills.1
  apply compare_restore_cps e base hc v t.regs.rdx.toBitVec t.regs.rdi.toBitVec t.regs.r14.toBitVec
    sourceSpill outputSpill lowSpill
  change Eventually (step e) P (restored, base + 450)
  apply compare_branch_cps e base hc restored (compare ready.count.value cap) ordering
  intro flags
  exact hp {restored with status := flags} capPointer capPayload (readyAfter.with_status flags)
    actualPointer expectedPointer expectedPayload originalPointer originalPayload

end SszX86.Delimited
