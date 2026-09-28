import SszX86.BitVectorFinishMemory
import SszX86.BitVectorCall
import SszX86.BitVectorRound

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

def finishNarrowRegions (s : MachineData) : List (Nat × Nat) :=
  [(s.regs.rsp.toNat - 8, 8), (s.regs.rsp.toNat + 16, 32)]

theorem finish_narrow_frame (s u : MachineData) (length : NatOperand) (ra : BitVec 64)
    (stack : u.regs.rsp = s.regs.rsp)
    (low : 72 ≤ s.regs.rsp.toNat) (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (t : MachineState)
    (post : NatToU128.Post (callState (toU128SetupState u) ra) length ra t) :
    RegionsFrame u.dmem t.1.dmem (finishNarrowRegions s) := by
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
  have narrowed := to_u128_regions (callState (toU128SetupState u) ra) t.1.dmem _ post.frame
  simp only [callState, NatDivision.callState, toU128SetupState, stack,
    UInt64.toNat_ofBitVec] at narrowed
  have combined := pushed.trans narrowed
  simpa only [callState, NatDivision.callState, toU128SetupState, stack,
    UInt64.toBitVec_ofBitVec, UInt64.toNat_ofBitVec, callAddress, resultAddress,
    finishNarrowRegions, List.cons_append, List.nil_append] using combined

theorem finish_narrow_cover (s : MachineData) (before after : DataMem)
    (low : 72 ≤ s.regs.rsp.toNat)
    (frame : RegionsFrame before after (finishNarrowRegions s)) :
    RegionsFrame before after (finishRegions s) := by
  apply frame.cover
  intro span member
  simp only [finishNarrowRegions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals
    refine ⟨(workStart s, workSize), by simp [finishRegions], ?_, ?_⟩ <;>
      unfold workStart workSize <;> omega

theorem finish_narrow_cache (s : MachineData) (before after : DataMem) (off : Nat)
    (location : off = 8 ∨ off = 104)
    (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (frame : RegionsFrame before after (finishNarrowRegions s)) :
    Mem.loadInt after (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 =
      Mem.loadInt before (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 := by
  have cacheLoad := frame.load (s.regs.rsp.toNat + off) 8 (by rcases location with rfl | rfl <;> omega)
    (by
      intro span member
      simp only [finishNarrowRegions, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> unfold Body.Apart <;>
        rcases location with rfl | rfl <;> omega)
  simpa only [← UInt64.toNat_toBitVec, width_address] using cacheLoad

private theorem finish_tag_store (m : DataMem) (out : BitVec 64) :
    Mem.loadInt (Mem.storeInt m out 8 1) out 1 = some 1 := by
  have byte := memmove_store_lookup_inside m out (Int.toBytes 8 1) 0 (by decide) (by decide)
  have loaded := memmove_loadInt_of_lookup (Mem.storeInt m out 8 1) out [1] (by
    intro i hi
    have zero : i = 0 := by simpa using hi
    subst i
    simpa only [Mem.storeInt, show (Int.toBytes 8 1)[0]? = some 1 by decide,
      List.getElem?_cons_zero] using byte)
  simpa only [List.length_cons, List.length_nil, show Int.ofBytes [1] = 1 by decide] using loaded

/-- TEST reads only the low byte of the actual two-word Option tag. -/
theorem finish_some_tag (m : DataMem) (out : BitVec 64) (count : BitVec 128) :
    Mem.loadInt (NatToU128.someMem m out count) out 1 = some 1 := by
  unfold NatToU128.someMem
  rw [load_store_disjoint _ _ _ _ _ _ (by intro i hi j hj; bv_omega)]
  simpa only [BitVec.add_zero] using finish_tag_store _ out

end SszX86.BitVector
