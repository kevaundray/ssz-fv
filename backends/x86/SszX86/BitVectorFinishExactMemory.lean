import SszX86.BitVectorFinishMemory
import SszX86.BitVectorReached
import SszX86.BitVectorRound

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

def finishExactRegions (s : MachineData) : List (Nat × Nat) :=
  [(s.regs.rsp.toNat - 8, 8), (s.regs.rsp.toNat + 16, 68)]

theorem finish_exact_frame (s u : MachineData) (expected : NatOperand) (actual ra : BitVec 64)
    (stack : u.regs.rsp = s.regs.rsp)
    (low : 72 ≤ s.regs.rsp.toNat) (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (t : MachineState)
    (post : NatExact.Post (callState (exactSetupState u) ra) expected actual ra t) :
    RegionsFrame u.dmem t.1.dmem (finishExactRegions s) := by
  have lowBV : 72 ≤ s.regs.rsp.toBitVec.toNat := low
  have highBV : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 := high
  have callAddress : (s.regs.rsp.toBitVec - 8#64).toNat = s.regs.rsp.toNat - 8 := by
    change (s.regs.rsp.toBitVec - 8#64).toNat = s.regs.rsp.toBitVec.toNat - 8
    bv_omega
  have resultAddress : (s.regs.rsp.toBitVec + 16#64).toNat = s.regs.rsp.toNat + 16 := by
    change (s.regs.rsp.toBitVec + 16#64).toNat = s.regs.rsp.toBitVec.toNat + 16
    bv_omega
  have pushed := store_regions_frame u.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toInt
    (by rw [callAddress]; omega)
  have checked := exact_regions (callState (exactSetupState u) ra) t.1.dmem _ post.frame
  simp only [callState, NatDivision.callState, exactSetupState, stack,
    UInt64.toNat_ofBitVec] at checked
  have combined := pushed.trans checked
  simpa only [callState, NatDivision.callState, exactSetupState, stack,
    UInt64.toNat_ofBitVec, callAddress, resultAddress, finishExactRegions,
    List.cons_append, List.nil_append] using combined

theorem finish_exact_work (s : MachineData) (before after : DataMem)
    (low : 72 ≤ s.regs.rsp.toNat)
    (frame : RegionsFrame before after (finishExactRegions s)) :
    RegionsFrame before after [(workStart s, workSize)] := by
  apply frame.cover
  intro span member
  simp only [finishExactRegions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals
    refine ⟨(workStart s, workSize), by simp, ?_, ?_⟩ <;>
      unfold workStart workSize <;> omega

theorem finish_exact_cache (s : MachineData) (before after : DataMem) (off : Nat)
    (location : off = 8 ∨ off = 104)
    (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (frame : RegionsFrame before after (finishExactRegions s)) :
    Mem.loadInt after (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 =
      Mem.loadInt before (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 := by
  have cacheLoad := frame.load (s.regs.rsp.toNat + off) 8 (by rcases location with rfl | rfl <;> omega)
    (by
      intro span member
      simp only [finishExactRegions, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> unfold Body.Apart <;>
        rcases location with rfl | rfl <;> omega)
  simpa only [← UInt64.toNat_toBitVec, width_address] using cacheLoad

theorem finish_exact_mapping (u : MachineData) (expected : NatOperand) (actual ra : BitVec 64)
    (t : MachineState)
    (post : NatExact.Post (callState (exactSetupState u) ra) expected actual ra t) :
    Mapping.Extends u.dmem t.1.dmem := by
  intro p n hm
  rw [post.memory]
  unfold NatExact.resultMem
  split
  · unfold NatExact.successMem callState NatDivision.callState exactSetupState
    repeat' apply Large.mapped_store
    exact hm
  · unfold NatExact.failureMem NatExact.errorHeaderMem callState NatDivision.callState exactSetupState
    repeat' apply Large.mapped_store
    exact hm

/-- The exact helper's post restores the stable registers and the two real caches. -/
theorem finish_exact_anchors (s u : MachineData) (length expected : NatOperand)
    (actual ra : BitVec 64) (anchors : Anchors s u length)
    (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (t : MachineState)
    (post : NatExact.Post (callState (exactSetupState u) ra) expected actual ra t)
    (frame : RegionsFrame u.dmem t.1.dmem (finishExactRegions s)) :
    Anchors s t.1 length := by
  have stack : t.1.regs.rsp = s.regs.rsp := by
    apply UInt64.toBitVec_inj.mp
    have equal := post.returned.sp
    simp only [callState, NatDivision.callState, exactSetupState,
      UInt64.toBitVec_ofBitVec, anchors.stack] at equal
    bv_omega
  refine ⟨stack, post.returned.rbx.trans anchors.arena, post.returned.r14.trans anchors.count,
    ?_, ?_, ?_, ?_⟩
  · rw [post.returned.r15]
    exact anchors.pointer
  · rw [post.returned.r12]
    exact anchors.payload
  · rw [finish_exact_cache s u.dmem t.1.dmem 8 (Or.inl rfl) high frame]
    exact anchors.outputCache
  · rw [finish_exact_cache s u.dmem t.1.dmem 104 (Or.inr rfl) high frame]
    exact anchors.sourceCache

end SszX86.BitVector
