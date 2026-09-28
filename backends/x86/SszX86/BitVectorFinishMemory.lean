import SszX86.BitVectorTerminal
import SszX86.BitVectorPadding
import SszX86.BitVectorSuccess
import SszX86.BitVectorNarrowOwned

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- The successful-scope suffix writes only the outer result and private work. -/
def finishRegions (s : MachineData) : List (Nat × Nat) :=
  [(s.regs.rdi.toNat, 80), (workStart s, workSize)]

theorem finish_saved (s : MachineData) (saved : Saved) (before after : DataMem)
    (low : 72 ≤ s.regs.rsp.toNat) (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (apart : Body.Apart s.regs.rdi.toNat 80 (s.regs.rsp.toNat + 312) 56)
    (stored : SavedAt before s.regs.rsp.toBitVec saved)
    (frame : RegionsFrame before after (finishRegions s)) :
    SavedAt after s.regs.rsp.toBitVec saved := by
  have savedLoad (off : Nat) (lo : 312 ≤ off) (hi : off + 8 ≤ 368) :
      Mem.loadInt after (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 =
        Mem.loadInt before (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 := by
    have read := frame.load (s.regs.rsp.toNat + off) 8 (by omega) (by
      intro span member
      simp only [finishRegions, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · unfold Body.Apart at *
        omega
      · unfold Body.Apart workStart workSize
        omega)
    simpa only [← UInt64.toNat_toBitVec, width_address] using read
  simpa only [SavedAt, savedLoad 312 (by decide) (by decide), savedLoad 320 (by decide) (by decide),
    savedLoad 328 (by decide) (by decide), savedLoad 336 (by decide) (by decide),
    savedLoad 344 (by decide) (by decide), savedLoad 352 (by decide) (by decide),
    savedLoad 360 (by decide) (by decide)] using stored

theorem finish_returned (s u : MachineData) (saved : Saved)
    (original : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (stack : u.regs.rsp = s.regs.rsp)
    (stored : SavedAt u.dmem s.regs.rsp.toBitVec saved) :
    Body.Returned s saved (returned u saved, Int64.ofBitVec saved.rip) := by
  refine ⟨rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, stored⟩
  · have ret := original.2.2.2.2.2.2
    simp only [ret, Option.map_some, SszX86.ofBytes_wordBytes]
  · change u.regs.rsp.toBitVec + 368#64 = s.regs.rsp.toBitVec + 368#64
    rw [stack]

theorem finish_padding_frame (s : MachineData) (m : DataMem)
    (bound : s.regs.rdi.toNat + 80 ≤ 2^64) :
    RegionsFrame m (paddingMem m s.regs.rdi.toBitVec) (finishRegions s) := by
  intro a outside
  apply padding_frame
  intro i hi
  apply Body.outside_byte s.regs.rdi.toBitVec a 80 i bound
    (outside (s.regs.rdi.toNat, 80) (by simp [finishRegions]))
  omega

theorem finish_success_frame (s : MachineData) (m : DataMem)
    (pointer size low high : BitVec 64) (bound : s.regs.rdi.toNat + 80 ≤ 2^64) :
    RegionsFrame m (successMem m s.regs.rdi.toBitVec pointer size low high) (finishRegions s) := by
  intro a outside
  exact success_frame m s.regs.rdi.toBitVec pointer size low high a
    (fun i hi => Body.outside_byte s.regs.rdi.toBitVec a 80 i bound
      (outside (s.regs.rdi.toNat, 80) (by simp [finishRegions])) hi)

theorem finish_frame_trans {s : MachineData} {a b c : DataMem}
    (first : RegionsFrame a b (finishRegions s))
    (second : RegionsFrame b c (finishRegions s)) :
    RegionsFrame a c (finishRegions s) := by
  intro p outside
  exact (second p outside).trans (first p outside)

/-- The padding error's actual stores and common RET, with the original ABI. -/
theorem finish_padding_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s u : MachineData) (saved : Saved) (data : Ssz.Bytes)
    (original : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (stack : u.regs.rsp = s.regs.rsp)
    (out : u.regs.rax.toBitVec = s.regs.rdi.toBitVec)
    (outputMapped : Large.Mapped u.dmem s.regs.rdi.toBitVec 80)
    (bound : s.regs.rdi.toNat + 80 ≤ 2^64)
    (low : 72 ≤ s.regs.rsp.toNat) (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (apart : Body.Apart s.regs.rdi.toNat 80 (s.regs.rsp.toNat + 312) 56)
    (stored : SavedAt u.dmem s.regs.rsp.toBitVec saved) :
    Eventually (step e) (Terminal s saved u.dmem data (.error .paddingBits))
      (u, base + 4885) := by
  have frame := finish_padding_frame s u.dmem bound
  have savedAfter := finish_saved s saved u.dmem _ low high apart stored frame
  apply padding_stores_cps e base hc u (by simpa only [out] using outputMapped)
  apply epilogue_cps e base hc _ saved
  · simpa only [out, stack] using savedAfter
  refine ⟨?_, ?_, ?_⟩
  · change SszNative.UintCodec.errorAt (widthLoad (paddingMem u.dmem u.regs.rax.toBitVec))
      s.regs.rdi.toNat 15 0 0
    rw [out]
    exact padding_observed u.dmem s.regs.rdi.toBitVec bound
  · apply finish_returned s {u with dmem := paddingMem u.dmem u.regs.rax.toBitVec}
      saved original stack
    simpa only [out] using savedAfter
  · simpa only [returned, out, finishRegions] using frame

end SszX86.BitVector
