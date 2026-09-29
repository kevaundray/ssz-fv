import SszX86.HashCombineInitialize
import SszX86.HashCombineLeft
import SszX86.HashCombineRightUpdate
import SszX86.HashCombineFinish

namespace SszX86.Hash
open SszNative.HashStream

/-- The actual raw two-slice entry executes both streaming updates, the proved
finalizer, and the original RET. Sources may alias each other, either length may
be zero, and the aggregate logical counter uses its native wrapping addition. -/
theorem combine_correct (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root) (s : MachineData) (left right : ByteArray)
    (ra : BitVec 64) (pre : CombinePre root s left right ra) :
    Eventually (step e) (CombinePost s left right ra) (s, root) := by
  have pushesMapping : Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48 := by
    have h := mapped_subrange _ _ 368 320 48 pre.stack.2 (by decide)
    have address : s.regs.rsp.toBitVec - 368 + BitVec.ofNat 64 320 =
        s.regs.rsp.toBitVec - 48 := by bv_omega
    simpa only [address] using h
  apply Combine.pushes_runs e root hc.combine s pushesMapping
  apply Combine.reserve_runs e root hc.combine
  intro flags
  let prepared := Combine.arguments (Combine.reserved (Combine.savedState s) flags)
  have spPrepared : prepared.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 168 := by
    simp only [prepared, Combine.arguments, Combine.reserved, Combine.savedState,
      Dispatch.savedState, UInt64.toBitVec_ofBitVec]
    bv_omega
  have localsMapping : Mapped prepared.dmem prepared.regs.rsp.toBitVec 120 := by
    have all := Dispatch.saved_mapped s _ _ pre.stack.2
    have part := mapped_subrange _ _ 368 200 120 all (by decide)
    have address : s.regs.rsp.toBitVec - 368 + BitVec.ofNat 64 200 =
        s.regs.rsp.toBitVec - 168 := by bv_omega
    simpa only [spPrepared, address] using part
  apply Combine.arguments_runs e root hc.combine
  apply Combine.initialize_runs e root hc prepared localsMapping
  let initialized := Combine.initialized prepared
  have spInitialized : initialized.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 168 := spPrepared
  have rbxInitialized : initialized.regs.rbx = s.regs.rdi := rfl
  have r12Initialized : initialized.regs.r12.toBitVec = initialized.regs.rsp.toBitVec + 72 := rfl
  have r14Initialized : initialized.regs.r14 = s.regs.r8 := rfl
  have r15Initialized : initialized.regs.r15 = s.regs.rcx := rfl
  have rbpInitialized : initialized.regs.rbp = s.regs.rsi := rfl
  have r13Initialized : initialized.regs.r13 = s.regs.rdx := rfl
  have rdxInitialized : initialized.regs.rdx = s.regs.rdx := rfl
  have lengthWord : s.regs.rdx = UInt64.ofNat left.size := by
    apply UInt64.toBitVec_inj.1
    rw [← pre.leftLength]
    simpa only [UInt64.toBitVec_ofNat, BitVec.setWidth_eq] using
      (BitVec.ofNat_toNat s.regs.rdx.toBitVec).symm
  let initialModel : Model := {new with byteLen := UInt64.ofNat left.size}
  have stateInitialized : StateAt initialized.dmem (initialized.regs.rsp.toBitVec + 8) initialModel := by
    have h := Combine.initialized_state prepared
    simpa only [prepared, Combine.arguments, Combine.reserved, Combine.savedState,
      Dispatch.savedState, initialModel, lengthWord] using h
  have liveInitialized : Combine.Live root s left right ra initialized.dmem := by
    apply Combine.Live.after root s left right ra pre _ _ (Combine.saved_live root s left right ra pre)
    · simpa only [spPrepared] using Combine.initialized_frame prepared
    · exact Combine.initialized_mapping prepared
  have memoryLeft : Combine.DrainMemory root initialized.dmem initialized.regs.rsp.toBitVec
      s.regs.rsi.toBitVec left := by
    rw [spInitialized]
    exact Combine.live_drainMemory root s left right ra pre _ liveInitialized _ left
      liveInitialized.leftBytes pre.leftPhysical pre.leftStack
  apply Combine.left_entry_test_runs e root hc.combine initialized
  intro entryFlags
  let current : MachineData := {initialized with status := entryFlags}
  have leftRun := Combine.left_drain_runs e root hc compress current initialModel
    s.regs.rsi.toBitVec left 0 (by omega) memoryLeft stateInitialized r12Initialized
    (by simp only [current, rbpInitialized, BitVec.add_zero])
    (by simpa only [current, r13Initialized, Nat.sub_zero] using pre.leftLength)
  have branch : (if initialized.regs.rdx.toNat < 64 then root + 217 else root + 192) =
      (if 64 ≤ left.size - 0 then root + 192 else root + 217) := by
    rw [rdxInitialized, pre.leftLength]
    simp only [Nat.sub_zero]
    split <;> split <;> try rfl <;> omega
  rw [branch]
  apply eventually_trans (step e) _ _ _ leftRun
  rintro ⟨afterLeft, leftPC⟩ leftPost
  have leftPC' : leftPC = root + 239 := leftPost.pc
  subst leftPC
  have leftSP : afterLeft.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 168 :=
    leftPost.rsp.trans spInitialized
  have leftOut : afterLeft.regs.rbx = s.regs.rdi := leftPost.rbx.trans rbxInitialized
  have leftChain : afterLeft.regs.r12.toBitVec = afterLeft.regs.rsp.toBitVec + 72 := by
    rw [leftPost.r12, leftPost.rsp]
    exact r12Initialized
  have leftState : StateAt afterLeft.dmem (afterLeft.regs.rsp.toBitVec + 8)
      (update new left).state := by
    rw [leftPost.rsp, Combine.update_new]
    exact leftPost.state
  have liveLeft : Combine.Live root s left right ra afterLeft.dmem := by
    apply Combine.Live.after root s left right ra pre _ _ liveInitialized
    · simpa only [current, spInitialized] using leftPost.frame
    · exact leftPost.mapping
  have memoryRight : Combine.DrainMemory root afterLeft.dmem afterLeft.regs.rsp.toBitVec
      s.regs.rcx.toBitVec right := by
    rw [leftSP]
    exact Combine.live_drainMemory root s left right ra pre _ liveLeft _ right
      liveLeft.rightBytes pre.rightPhysical pre.rightStack
  have rightSource : afterLeft.regs.r15.toBitVec = s.regs.rcx.toBitVec :=
    congrArg UInt64.toBitVec (leftPost.r15.trans r15Initialized)
  have rightLength : afterLeft.regs.r14.toNat = right.size := by
    rw [leftPost.r14, r14Initialized]
    exact pre.rightLength
  have buffered : afterLeft.regs.r13.toNat = (update new left).state.buffered.val := by
    have occupied : (update new left).state.buffered.val = left.size % 64 := by
      rw [Combine.update_new]
      simp only [drain, Nat.sub_zero]
    rw [occupied]
    simpa only [Nat.sub_zero] using leftPost.buffered
  have rightRun := Combine.right_update_runs e root hc compress afterLeft (update new left).state
    s.regs.rcx.toBitVec right memoryRight leftState leftChain rightSource rightLength buffered
  apply eventually_trans (step e) _ _ _ rightRun
  rintro ⟨afterRight, rightPC⟩ rightPost
  have rightPC' : rightPC = root + 399 := rightPost.pc
  subst rightPC
  have rightSP : afterRight.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 168 :=
    rightPost.rsp.trans leftSP
  have rightOut : afterRight.regs.rbx = s.regs.rdi := rightPost.rbx.trans leftOut
  have liveRight : Combine.Live root s left right ra afterRight.dmem := by
    apply Combine.Live.after root s left right ra pre _ _ liveLeft
    · simpa only [leftSP] using rightPost.frame
    · exact rightPost.mapping
  apply Combine.finish_runs e root hc compress s left right ra pre afterRight liveRight
  · rw [rightPost.rsp]
    exact rightPost.state
  · exact rightSP
  · exact rightOut

end SszX86.Hash
